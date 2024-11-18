{-# LANGUAGE TemplateHaskell #-}

module Graphics.Wayland.Scanner (
  generateClientTypes,
  generateClientInternal,
  generateClientExports,

  generateServerTypes,
  generateServerInternal,
  generateServerExports,

  module Graphics.Wayland.Scanner.Types,
  module Graphics.Wayland.Scanner.Protocol,

  CInterface(..)

  ) where

import Data.Functor ((<$>))
import Data.Either (lefts, rights)
import Data.Maybe (fromJust)
import Data.List (findIndex)
import Control.Monad (liftM)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Writer (tell, WriterT, runWriterT)
import Foreign
import Foreign.C.Types
import Foreign.C.String (withCString)
import Language.Haskell.TH
import Language.Haskell.TH.Syntax (VarStrictType)

import Graphics.Wayland
import Graphics.Wayland.Scanner.Marshaller
import Graphics.Wayland.Scanner.Names
import Graphics.Wayland.Scanner.Protocol
import Graphics.Wayland.Scanner.Types
import Graphics.Wayland.Internal.Util hiding (Client)
import qualified Graphics.Wayland.Internal.Util as Util (Client)


-- Dear future maintainer,
-- I'm sorry.

#include <wayland-server.h>


-- | We will be working in this monad to generate binding code and simultaneously
--   remember which symbols should be exported by the library.
type ProcessWithExports a = WriterT [String] Q a

-- | Remember that we should re-export this symbol so that it is usable
export :: String -> ProcessWithExports ()
export name = tell [name]

-- | Create a `BangType` with lazy evaluation and no unpacking (the default
--   behavior for data fields).
lazyWithoutPacking :: Q Type -> Q BangType
lazyWithoutPacking = bangType (bang noSourceUnpackedness noSourceStrictness)

-- | Generates a Haskell `newtype` declaration with a single constructor.
--   This newtype has no additional constraints, is non-polymorphic, and derives
--   `Show` and `Eq`.
--
--   For example, calling `newtypeGenerator ''MyType (conT ''Int)` would yield:
--       newtype MyType = MyType Int deriving (Show, Eq)
newtypeGenerator :: Name -> Q Type -> Q Dec
newtypeGenerator qname resultingType = newtypeD
  (pure [])      -- No type constraints
  qname          -- Newtype name
  []             -- No type variables; non-polymorphic
  Nothing        -- No specific kind
  (normalC qname [lazyWithoutPacking resultingType]) -- Single lazy constructor
  [derivClause Nothing [conT ''Show, conT ''Eq]]     -- Derives Show and Eq

-- | A helper function to define a foreign import for a C function.
--   This wraps the low-level `forImpD` to simplify creating foreign imports
--
--   Example:
--   foreignC "wl_registry_bind" "registryBind"
--     [t| Registry -> Word32 -> Ptr CChar -> Word32 -> IO SomeType |]
foreignC :: String -> Name -> Q Type -> Q Dec
foreignC cFunctionToImport haskellNameForImport typeSignature =
  forImpD            -- Define a foreign import
    cCall            -- Use the C calling convention.
    unsafe           -- Specify that the function does not call back into Haskell.
    cFunctionToImport -- The name of the C function to import.
    haskellNameForImport -- The Haskell name for the imported function.
    typeSignature    -- The Haskell type signature for the function.

-- | Wayland data types - exported in the Internal.{Client,Server}Types modules
generateDataTypes :: ProtocolSpec -> Q [Dec]
generateDataTypes ps =
  concat <$> traverse generateInterface (protocolInterfaces ps)
  where
    generateInterface :: Interface -> Q [Dec]
    generateInterface iface = do
      let iname = interfaceName iface
          pname = protocolName ps
          qname = mkName (interfaceTypeName pname iname)

      constructorType <- [t| Ptr $(conT qname)|]

      typeDec <- newtypeGenerator qname (pure constructorType)

      versionInstance <- [d|
        instance ProtocolVersion $(conT qname) where
          protocolVersion _ =
            $(litE $ IntegerL $ fromIntegral $ interfaceVersion iface) |]

      return $ typeDec : versionInstance

-- | We should only be able to construct "global" objects, which are those that
--   cannot be obtained via other objects.
--   The following code picks out these global interfaces.
getGlobalInterfaces :: ProtocolSpec -> [Interface]
getGlobalInterfaces ps = filter isGlobalInterface (protocolInterfaces ps) where
  messageCreatesIface child msg = any isCreatingArgument (messageArguments msg)
    where isCreatingArgument (_, NewIdArg _ x, _) = x == interfaceName child
          isCreatingArgument _ = False

  interfaceCreatesIface child parent =
    any (messageCreatesIface child) (interfaceRequests parent)

  protocolCreatesIface child =
    any (interfaceCreatesIface child) (protocolInterfaces ps)

  isGlobalInterface iface =
    interfaceName iface /= "wl_display" && not (protocolCreatesIface iface)

-- | Generates the type signature for the foreign function used to
--   bind Wayland registry objects.
--   The generated signature corresponds to the Wayland function:
--
--     void * wl_registry_bind(struct wl_registry *wl_registry,
--                             uint32_t name,
--                             const struct wl_interface *interface,
--                             uint32_t version);
--
--   In Haskell, this maps to a function that takes:
--     1. A pointer to a Wayland Registry (`Registry`)
--     2. An ID (`uint32_t`) for the object
--     3. The interface type (`CInterface`)
--     4. The version of the protocol (`CUInt`)
--     5. A pointer to the interface name (`Ptr CChar`)
--     6. The version number (`CUInt`)
--     7. A placeholder for additional data (`Ptr ()`, often null)
--   and returns:
--     An IO action that produces a pointer to the bound object.
--
-- Example:
--
-- Suppose we are binding a `wl_compositor` object. The generated
-- type signature will look like:
--
--   Registry -> Word32 -> CInterface -> CUInt ->
--   Ptr CChar -> CUInt -> Ptr () -> IO Compositor
--
-- This signature is used to declare the foreign import for the
-- binding function:
--
--   foreign import ccall unsafe "wl_registry_bind"
--     wl_registry_wl_compositor_c_bind ::
--       Registry -> Word32 -> CInterface -> CUInt ->
--       Ptr CChar -> CUInt -> Ptr () -> IO Compositor
generateTypeSig :: Name -> Q Type
generateTypeSig interfaceType =
  [t| $(conT $ mkName "Registry") -> -- Registry: the WL registry
      {#type uint32_t#} -> -- ObjectID: the object being bound
      CInterface -> -- Interface: the type of the object to bind
      CUInt -> -- Protocol version: compatibility version
      Ptr CChar -> -- Interface name: string pointer to the name
      CUInt -> -- Interface Version (?): version
      Ptr () -> -- Additional data: usually null
      IO $(conT interfaceType) -- Result: a ptr to the  bound object
  |]

-- | Generates the Haskell wrapper for the foreign function that
--   binds a Wayland registry object.  The wrapper takes
--   human-readable arguments, such as strings for the interface
--   name, and marshals them into the format required by the
--   foreign C function.
--
-- Example:
--
-- If the interface is `wl_compositor` and `exposeName` is
-- `registryBindWlCompositor`, the generated wrapper will be:
--
-- exposeName: The name of the Haskell function to generate
-- (e.g., "registryBindWlCompositor").
-- internalCName: The name of the foreign function imported from C
-- (e.g., "wl_registry_wl_compositor_c_bind")
-- interfaceCName: The C symbol representing the Wayland interface
-- (e.g., "wl_compositor_interface").
--
-- Note: the type isn't generated, but its still shown for clarity.
--
-- registryBindWlCompositor ::
-- Registry -> Word32 -> String -> Word32 -> IO Compositor
-- registryBindWlCompositor reg name strname version =
--   withCString strname $ \cstr ->
--     wl_registry_wl_compositor_c_bind
--       reg
--       0
--       wl_compositor_interface
--       (fromIntegral name)
--       cstr
--       (fromIntegral version)
generateWrapper :: String -> Name -> Name -> Q [Dec]
generateWrapper exposeName internalCName interfaceCName = [d|
  $(varP $ mkName exposeName) =
    \ reg name strname version ->
      withCString strname $ \ cstr ->
        $(varE internalCName)
          reg                      -- The Wayland registry object
          0                        -- Opcode (0 for bind operations)
          $(varE $ interfaceCName) -- Interface name (~ wl_compositor_interface)
          (fromIntegral (name :: Word)) -- Global object ID
          cstr -- Marshaled CString representation of the interface name
          (fromIntegral (version :: Word)) -- Interface version
          nullPtr -- Additional arguments (not used here)
  |]

-- | The wayland registry allows one to construct global objects.
--   Its API is in wayland.xml, but that API is type-unsafe, so we construct the
--   the bindings explicitly here.
--
-- From the wayland header files (for reference):
--
-- id = wl_proxy_marshal_constructor(
--     (struct wl_proxy *) wl_registry,
--     WL_REGISTRY_BIND,
--     interface,
--     name,
--     interface->name,
--     version,
--     NULL);
--
-- struct wl_proxy * wl_proxy_marshal_constructor(
--     struct wl_proxy *proxy,
--     uint32_t opcode,
--     const struct wl_interface *interface,
--     ...)
--
generateRegistryBind :: ProtocolSpec -> ProcessWithExports [Dec]
generateRegistryBind ps = do
  concat <$> traverse (registryBindInterface . interfaceName)
                      (getGlobalInterfaces ps)
    where
      pname = protocolName ps

      registryBindInterface :: String -> ProcessWithExports [Dec]
      registryBindInterface iname = do
        let exposedName = registryBindName pname iname
            internalCName = mkName $ "wl_registry_" ++ iname ++ "_c_bind"

        -- Example output:
        -- foreign import ccall unsafe "wl_proxy_marshal_constructor"
        --   wl_registry_wl_compositor_c_bind
        --   :: Registry -> Word32 -> CInterface -> Word32 -> Ptr CChar -> Word32
        --   -> Ptr () -> IO WaylandWlCompositor
        foreignImport <- lift $ foreignC
          "wl_proxy_marshal_constructor"
          internalCName
          (generateTypeSig $ mkName $ interfaceTypeName pname iname)

        exposureDec <- lift $
          (generateWrapper exposedName
                           internalCName
                           (interfaceCInterfaceName pname iname))

        export exposedName

        return $ foreignImport : exposureDec

-- | Wayland has an "enum" type argument for messages. Here, we generate the
--   corresponding Haskell types. Note that wayland-style enums might not
--   actually be enums, in the sense that they are sometimes actually bit fields.
generateEnums :: ProtocolSpec -> Q [Dec]
generateEnums ps =
  fmap concat $ mapM eachGenerateEnums (protocolInterfaces ps) where

    eachGenerateEnums :: Interface -> Q [Dec]
    eachGenerateEnums iface =

      fmap concat $ mapM generateEnum (interfaceEnums iface) where

        generateEnum :: WLEnum -> Q [Dec]
        generateEnum wlenum = do
          let qname =
                enumTypeName (protocolName ps) (interfaceName iface) (enumName wlenum)

              -- Define a newtype for the Wayland enum
              enumNewtype :: Q Dec
              enumNewtype = newtypeGenerator qname (conT ''Int)

              -- Create a unique name for each enum entry
              mkEnumName :: String -> Name
              mkEnumName = enumEntryHaskName (protocolName ps)
                                             (interfaceName iface)
                                             (enumName wlenum)

              -- Map each entry inside the enum to its name and integer value
              enumNamesAndVals :: [(Name, Integer)]
              enumNamesAndVals =
                [ (mkEnumName e, toInteger v) | (e, v) <- enumEntries wlenum ]

              -- Define a Haskell value for each enum entry
              mkHaskellDec :: (Name, Integer) -> Q Dec
              mkHaskellDec (name, val) =
                valD (varP name) (normalB (conE qname `appE` litE (integerL val))) []

          -- Generate the enum newtype declaration and the value declarations
          -- for each entry
          entries <- mapM mkHaskellDec enumNamesAndVals
          newtypeDec <- enumNewtype
          pure (newtypeDec : entries)

-- | We will need a pointer to the wl_interface structs, for passing to wl_proxy_marshal_constructor and wl_resource_create.
--   Now, a pretty solution would construct its own wl_interface struct here.
--   But that's way too much work for me. We just bind to the one generated by the C scanner.
generateCInterfaceDecs :: ProtocolSpec -> Q [Dec]
generateCInterfaceDecs ps = mapM bindCInterface (protocolInterfaces ps)
  where
    bindCInterface :: Interface -> Q Dec
    bindCInterface iface =
      foreignC
        ("&"++ (interfaceName iface) ++ "_interface")
        (interfaceCInterfaceName (protocolName ps) (interfaceName iface) )
        [t| (CInterface)|] -- pointer is fixed

-- | This function generates bindings to the "core" message passing API:
--   it binds to the actual message senders.
generateMethods :: ProtocolSpec -> ServerClient -> ProcessWithExports [Dec]
generateMethods ps sc = liftM concat $ traverse generateInterface $ filter (\iface -> if sc == Server then interfaceName iface /= "wl_display" else True) $ protocolInterfaces ps where
  generateInterface :: Interface -> ProcessWithExports [Dec]
  generateInterface iface = do
    -- Okay, we have to figure out some stuff. There is a tree of possibilities:
    -- - Server
    --   => this is actually an easy case. every message is just some call to wl_resource_post_event
    -- - Client
    -- - - if a message has more than one new_id argument, skip (or undefined for safety?)
    -- - - if a message has a single untyped new_id argument (ie now interface attribute in the XML), then there is some complicated C implementation we won't be copying, skip
    -- - - if a message has a single typed new_id argument, then this is the return value of wl_proxy_marshal_constructor
    --     => pass a bunch of constants in the initial arguments. pass NULL in its argument position
    -- - - if a message has no new_id arguments, we are calling wl_proxy_marshal
    --   => for each argument EXCEPT new_id's(where we would pass NULL as discussed), pass that argument
    -- Note that wl_resource_post_event, wl_proxy_marshal and wl_proxy_marshal_constructor all have the message index in the SECOND position: the object corresponding to the message is the first! So the important thing to remember is that our pretty Haskell function representations have some arguments inserted in between.
    --
    -- Further, in the Client case, we have to make a destructor. Some messages can have type="destructor" in the XML protocol files.
    -- - there is no message typed destructor with name "destroy"
    -- - - if the interface is wl_display, don't do anything
    -- - - if the interface is NOT wl_display
    --     => generate a new function "destroy", a synonnym for wl_proxy_destroy
    -- - otherwise, for each message typed destructor (possibly including "destroy")
    --   => call wl_proxy_marshal as normal, and *also* wl_proxy_destroy on this proxy (sole argument)
    -- - the case of having a "destroy", but no destructor, is illegal: iow, if you have a "destroy", then you must also have a destructor request.
    --   the C scanner allows you to have a non-destructor "destroy", but I doubt that's the intention, so I'll make that undefined.
    -- "dirty" name of internal raw binding to C function

    -- bind object destroyers
    let destroyName = mkName $ interfaceName iface ++ "_destructor"
        needsDefaultDestructor = ((sc == Client) && (not $ any messageIsDestructor $ interfaceRequests iface) && (interfaceName iface /= "wl_display"))
        defaultDestructorName = requestHaskName (protocolName ps) (interfaceName iface) "destroy"
    foreignDestructor <- lift $ foreignC "wl_proxy_destroy" destroyName [t|$(conT $ mkName $ interfaceTypeName (protocolName ps) (interfaceName iface)) -> IO ()|]
    -- FIXME: in the destructors, we should additionally clean up memory allocated for the callback infrastructure
    -- This should happen in the default destructor here and in any other destructor-type message below.
    defaultDestructor <- lift $ [d|$(varP $ mkName defaultDestructorName) = \ proxy -> $(varE destroyName) proxy|]
    if needsDefaultDestructor
       then export defaultDestructorName
       else return ()

    let
     -- Bind to an individual message
      generateMessage :: Int -> Message -> ProcessWithExports [Dec]
      generateMessage idx msg = -- index in the list used for wl_proxy_marshal arguments
        let pname = protocolName ps
            iname = interfaceName iface
            mname = messageName msg

            hname = case sc of
                      Server -> eventHaskName pname iname mname
                      Client -> requestHaskName pname iname mname
            internalCName = case sc of
                              Server -> mkName $ "wl_rpe_" ++ interfaceName iface ++ "_" ++ messageName msg
                              Client -> mkName $ "wl_pm_" ++ interfaceName iface ++ "_" ++ messageName msg

        in case sc of
             Server -> do
               -- From the wayland header files:
               -- void wl_resource_post_event(struct wl_resource *resource, uint32_t opcode, ...);
               cdec <- lift $ foreignC "wl_resource_post_event" internalCName [t|$(conT $ mkName $ interfaceTypeName (protocolName ps) (interfaceName iface)) -> {#type uint32_t#} -> $(genMessageCType Nothing (messageArguments msg)) |]
               resourceName <- lift $ newName "resourceInternalName___"
               let messageIndexApplied = applyAtPosition (varE internalCName) (litE $ IntegerL $ fromIntegral idx) 1
                   resourceApplied = [e|$messageIndexApplied $(varE resourceName)|]
                   (pats,fun) = argTypeMarshaller (messageArguments msg) resourceApplied
               declist <- lift $ [d|$(varP $ mkName hname) = $(LamE (VarP resourceName : pats) <$> fun)|]
               export hname
               return (cdec : declist)
             Client -> do
               -- See tree of possibilities above
               let numNewIds = sum $ map (fromEnum . isNewId) $ messageArguments msg
                   argsWithoutNewId = filter (\arg -> not $ isNewId arg) (messageArguments msg)
                   returnArgument = head $ filter (\arg -> isNewId arg) (messageArguments msg)
                   returnName = let (_, NewIdArg _ theName, _) = returnArgument
                                in theName
                   returnType = [t|IO $(argTypeToCType returnArgument)|]
               cdec <- lift $ case numNewIds of
                     -- void wl_proxy_marshal(struct wl_proxy *proxy, uint32_t opcode, ...)
                     0 -> foreignC "wl_proxy_marshal" internalCName [t|$(conT $ mkName $ interfaceTypeName (protocolName ps) (interfaceName iface)) -> {#type uint32_t#} -> $(genMessageCType Nothing (messageArguments msg)) |]
                     -- struct wl_proxy * wl_proxy_marshal_constructor(struct wl_proxy *proxy, uint32_t opcode, const struct wl_interface *interface, ...)
                     1 -> foreignC "wl_proxy_marshal_constructor" internalCName [t|$(conT $ mkName $ interfaceTypeName (protocolName ps) (interfaceName iface)) -> {#type uint32_t#} -> CInterface -> $(genMessageCType (Just returnType) (messageArguments msg)) |]


               proxyName <- lift $ newName "proxyInternalName___"
               let messageIndexApplied = applyAtPosition (varE internalCName) (litE $ IntegerL $ fromIntegral idx) 1
                   constructorApplied = case numNewIds of
                                          0 -> messageIndexApplied
                                          1 -> applyAtPosition messageIndexApplied (varE $ interfaceCInterfaceName pname (returnName)) 1
                   proxyApplied = [e|$constructorApplied $(varE proxyName)|]
                   makeArgumentNullPtr =
                       let argIdx = fromJust $ findIndex isNewId (messageArguments msg)
                           arg' = (messageArguments msg) !! argIdx
                           msgName = let (_,NewIdArg itsname _,_) = arg'
                                     in itsname
                       in [e|$(conE msgName) nullPtr|]
                   newIdNullInserted = case numNewIds of
                                         0 -> proxyApplied
                                         1 -> applyAtPosition proxyApplied makeArgumentNullPtr (fromJust $ findIndex isNewId (messageArguments msg))
                   finalCall = newIdNullInserted
                   (pats, fun) = argTypeMarshaller (argsWithoutNewId) finalCall
               declist <- lift $ [d|$(varP $ mkName hname) = $(LamE (VarP proxyName : pats) <$> [e|do
                                     -- Let's start by either calling wl_proxy_marshal or wl_proxy_marshal_constructor
                                     retval <- $fun

                                     -- possibly do some destruction here?
                                     $(case messageIsDestructor msg of
                                         False -> [e|return retval|] -- do nothing (will hopefully get optimized away)
                                         True -> [e|$(varE destroyName) $(varE proxyName) |]
                                         )

                                     return retval
                                     |])|]

               export hname
               return (cdec : declist)

    -- collect all message bindings for a given interface
    theMessages <- liftM concat $ sequence $ zipWith generateMessage [0..] $
        case sc of
                    Server -> interfaceEvents iface
                    Client -> interfaceRequests iface

    return $ foreignDestructor : theMessages ++ if needsDefaultDestructor then defaultDestructor else []

applyAtPosition :: ExpQ -> ExpQ -> Int -> ExpQ
applyAtPosition fun arg pos = do
  vars <- traverse (\ _ -> newName "somesecretnameyoushouldntmesswith___") [0..(pos-1)]
  lamE (map varP vars) $
    appsE $ fun : (map varE vars) ++ [arg]

preComposeAt :: ExpQ -> ExpQ -> Int -> Int -> ExpQ
preComposeAt fun arg pos numArgs
  | pos > numArgs  = error "programming error"
preComposeAt fun arg pos numArgs = do
  vars <- traverse (\ _ -> newName "yetanothernewvariablepleasedonttouchme___") [0..numArgs]
  lamE (map varP vars) $
    [e|do
      preCompVal <- $arg $(varE $ vars !! pos)
      $(appsE $ fun : (map varE $ take pos vars) ++ varE 'preCompVal : (map varE $ drop (pos+1) vars))
    |]

-- | Wayland stores callback functions in a C struct. Here we generate the
--   Haskell equivalent of those structs.
generateListenerTypes :: ProtocolSpec -> ServerClient -> Q [Dec]
generateListenerTypes sp sc = traverse generateListenerType $
     filter (\iface -> 0 < (length $ case sc of
       Server -> interfaceRequests iface
       Client -> interfaceEvents iface)) $ protocolInterfaces sp
  where
    generateListenerType :: Interface -> Q Dec
    generateListenerType iface = do
      let
        messages :: [Message]
        messages = case sc of
                   Server -> interfaceRequests iface
                   Client -> interfaceEvents iface
        pname = protocolName sp
        iname = interfaceName iface
        typeName :: Name
        typeName = messageListenerTypeName sc pname iname
        mkListenerType :: Message -> TypeQ
        mkListenerType msg = case sc of
                  Server -> [t|Util.Client -> $(conT $ mkName $ interfaceTypeName pname iname) -> $(genMessageHaskType Nothing $ messageArguments msg)|]  -- see large comment above
                  Client -> [t|$(conT $ mkName $ interfaceTypeName pname iname) -> $(genMessageHaskType Nothing $ messageArguments msg)|]
        mkMessageName :: Message -> String
        mkMessageName msg = messageListenerMessageName sc pname iname (messageName msg)
        mkListenerConstr :: Message -> VarStrictTypeQ
        mkListenerConstr msg = do
          let name = mkName $ mkMessageName msg
          ltype <- mkListenerType msg
          return (name, Bang NoSourceUnpackedness NoSourceStrictness, ltype)
      recArgs <- traverse mkListenerConstr messages
      return $ DataD [] typeName [] Nothing [RecC typeName recArgs] []

-- | For each interface, generate the callback API.
generateListenerMethods :: ProtocolSpec -> ServerClient -> ProcessWithExports [Dec]
generateListenerMethods sp sc = do
  let pname = protocolName sp

  interfaces <- liftM concat $ traverse (\iface -> generateListener sp iface sc) $
    filter (\iface -> 0 < (length $ case sc of
                                      Server -> interfaceRequests iface
                                      Client -> interfaceEvents iface)) $ protocolInterfaces sp

  -- For a new_id type argument, server-side, we are passed raw new_id's.
  -- Since the only sensible thing to do is to create the requested object,
  -- these bindings to that for the user, saving code duplication.
  resourceCreators <-
    case sc of
      Client -> return [] -- resources are created Server-side, and Client's proxies are created by the wayland library always
      Server -> lift $ liftM concat $ sequence $
        map (\ iface -> do
          let iname = interfaceName iface
              internalCName = mkName $ pname ++ "_" ++ iname ++ "_c_resource_create"
          foreignDec <- foreignC "wl_resource_create" internalCName [t|Util.Client -> CInterface -> CInt -> {#type uint32_t#} -> IO $(conT $ mkName $ interfaceTypeName pname iname) |]
          neatDec <- [d|$(varP $ interfaceResourceCreator pname iname) = \ client id ->
                          $(varE internalCName) client $(varE $ interfaceCInterfaceName pname iname) $(litE $ IntegerL $ fromIntegral $ interfaceVersion iface) id|]
          return $ foreignDec : neatDec
          ) (protocolInterfaces sp)
  return $ interfaces ++ resourceCreators


-- | Generate a specific interface's callback API
generateListener :: ProtocolSpec -> Interface -> ServerClient -> ProcessWithExports [Dec]
generateListener sp iface sc = do
  -- Tree of possibilities:
  -- - Server
  --   => call it an Implementation or Interface. first argument is the client, second is the resource
  -- - Client
  --   => call it a Listener. first argument is the proxy
  --
  -- for each argument (we're not gonna deal with untyped objects or new_ids):
  -- - typed new_id
  --   - Client
  --     => that type as arg
  --   - Server
  --     => uint32_t  (the actual id. so that's new. dunno how to handle this. it's to be passed to wl_resource_create. maybe i should just create the resource for the server and pass that.)
  -- - anything else
  --   => the type you'd expect
  let -- declare a Listener or Interface type for this interface
    typeName :: Name
    typeName = messageListenerTypeName sc (protocolName sp) (interfaceName iface)
    pname = protocolName sp
    iname :: String
    iname = interfaceName iface
    messages :: [Message]
    messages = case sc of
                 Server -> interfaceRequests iface
                 Client -> interfaceEvents iface
    mkMessageName :: Message -> String
    mkMessageName msg = messageListenerMessageName sc pname iname (messageName msg)

    -- In the weird uint32_t new_id case, first pass the id through @wl_resource_create@ to just get a resource
    -- See resourceCreators in 'generateListenerMethods' above.
    preCompResourceCreate clientName msg fun =
      case sc of
        Client -> fun
        Server -> foldr (\(arg, idx) curFunc ->
          case arg of
            (_, NewIdArg _ itsName, _) ->
              preComposeAt
                curFunc
                [e|$(varE $ interfaceResourceCreator pname itsName) $(varE clientName) |]
                idx
                (length $ messageArguments msg)
            _                          -> curFunc
          ) fun (zip (messageArguments msg) [1..])

    -- instance dec: this struct better be Storable
    instanceDec :: DecsQ
    instanceDec = do
      [d|instance Storable $(conT typeName) where
          sizeOf _ = $(litE $ IntegerL $ funcSize * (fromIntegral $ length messages))
          alignment _ = $(return $ LitE $ IntegerL funcAlign)
          peek _ = undefined  -- we shouldn't need to be able to read listeners (since we can't change them anyway)
          poke ptr record = $(doE $ ( zipWith (\ idx msg ->
              noBindS [e|do
                let haskFun = $(varE $ mkName $ mkMessageName msg) record
                    unmarshaller fun = \x -> $(let (pats, funexp) = argTypeUnmarshaller (messageArguments msg) ([e|fun x|])
                                               in LamE pats <$> funexp)

                -- The C code wants to call back into Haskell, which we allow by passing
                -- our Haskell functions through @foreign import "wrapper"@.
                -- This allocates memory, which should be freed when the object is no longer used.
                funptr <- $(case sc of -- the Server-side listeners take an extra Client argument
                              Server -> [e|$(varE $ wrapperName msg) $ \ client -> ($(preCompResourceCreate 'client msg [e|unmarshaller $ haskFun client|])) |]
                              -- The Client-side listener takes a void* user_data argument, which we throw out.
                              -- This API assumes that if users want to store data, they can do so using currying.
                              Client -> [e|$(varE $ wrapperName msg) $ \ _ -> unmarshaller haskFun|])

                pokeByteOff ptr $(litE $ IntegerL (idx * funcSize)) funptr
              |] )
            [0..] messages
            ) ++ [noBindS [e|return () |]] )
          |]


    -- FunPtr wrapper. Wraps a Haskell function into a function that can be called by C (ie. wayland).
    mkListenerCType msg = case sc of
              Server -> [t|Util.Client -> $(conT $ mkName $ interfaceTypeName pname iname) -> $(genMessageWeirdCType Nothing $ messageArguments msg)|]  -- see large comment above
              Client -> [t|Ptr () -> $(conT $ mkName $ interfaceTypeName pname iname) -> $(genMessageCType Nothing $ messageArguments msg)|]
    wrapperName msg = messageListenerWrapperName sc iname (messageName msg)
    wrapperDec msg = foreignC "wrapper" (wrapperName msg) [t|$(mkListenerCType msg) -> IO (FunPtr ($(mkListenerCType msg))) |]

    -- Bind add_listener. This instructs wayland to use our callbacks.
    haskName = requestHaskName pname iname "set_listener" -- dunno why I can't use this variable in the splice below.
  export haskName
  let
    foreignName = requestInternalCName iname "c_add_listener"
    foreignDec :: Q Dec
    foreignDec = case sc of
                   -- From the wayland header files:
                   -- void wl_resource_set_implementation(struct wl_resource *resource,
                   --    const void *implementation,
                   --    void *data,
                   --    wl_resource_destroy_func_t destroy);
                   -- typedef void (*wl_resource_destroy_func_t)(struct wl_resource *resource);
                   Server ->
                     forImpD
                       cCall
                       unsafe
                       "wl_resource_set_implementation"
                       foreignName
                       [t|
                         $(conT $ mkName $ interfaceTypeName pname iname)
                         -> (Ptr $(conT $ typeName))
                         -> (Ptr ())
                         -> FunPtr ($(conT $ mkName $ interfaceTypeName pname iname) -> IO ())
                         -> IO ()
                         |]
                   -- int wl_proxy_add_listener(struct wl_proxy *proxy,
                   --    void (**implementation)(void), void *data);
                   Client ->
                     forImpD
                       cCall
                       unsafe
                       "wl_proxy_add_listener"
                       foreignName
                       [t|
                         $(conT $ mkName $ interfaceTypeName pname iname)
                         -> (Ptr $(conT $ typeName))
                         -> (Ptr ())
                         -> IO CInt
                         |]
    apiDec :: Q [Dec]
    apiDec = [d|
      $(varP $ mkName haskName) =
        \ iface listener ->
          do
            -- malloc RAM for Listener type. FIXME: free on object destruction.
            memory <- malloc
            -- store Listener type
            poke memory listener
            -- call foreign add_listener on stored Listener type
            $(case sc of
                Server -> [e|$(varE foreignName) iface memory nullPtr nullFunPtr|]
                Client -> [e|errToResult <$> $(varE foreignName) iface memory nullPtr|])

      |]


  some <- lift $ traverse wrapperDec messages

  other <- lift $ instanceDec
  more <- lift $ foreignDec
  last <- lift $ apiDec

  return $ some ++ other ++ [more] ++ last

-- | Generate all data-types that should be exposed as Client-side API
generateClientTypes :: ProtocolSpec -> Q [Dec]
generateClientTypes ps = do
  dataTypes <- generateDataTypes ps
  listenerTypes <- generateListenerTypes ps Client
  enums <- generateEnums ps

  return $ dataTypes ++ listenerTypes ++ enums

-- | Generate internal binding code (e.g. foreign imports)
generateClientInternal :: ProtocolSpec -> Q [Dec]
generateClientInternal ps = do
  (methods, _) <- runWriterT $ generateMethods ps Client
  (listeners, _) <- runWriterT $ generateListenerMethods ps Client
  (registry, _ ) <- runWriterT $ generateRegistryBind ps
  cInterfaces <- generateCInterfaceDecs ps

  return $ methods ++ listeners ++ registry ++ cInterfaces

-- | Generate code that exports the right symbols to the user
generateClientExports :: ProtocolSpec -> Q [Dec]
generateClientExports ps = do
  (_, methodNames) <- runWriterT $ generateMethods ps Client
  (_, listenerNames) <- runWriterT $ generateListenerMethods ps Client
  (_, registryNames) <- runWriterT $ generateRegistryBind ps
  let names = methodNames ++ listenerNames ++ registryNames

  concat <$> mapM nameToDec names
    where
      nameToDec :: String -> Q [Dec]
      nameToDec name = [d|$(varP $ mkName name) = $(varE $ mkName $ "Import." ++ name) |]

-- | Generate all data-types that should be exposed as Server-side API
generateServerTypes :: ProtocolSpec -> Q [Dec]
generateServerTypes ps = do
  dataTypes <- generateDataTypes ps
  listenerTypes <- generateListenerTypes ps Server
  enums <- generateEnums ps

  return $ dataTypes ++ listenerTypes ++ enums

-- | Generate internal binding code (e.g. foreign imports)
generateServerInternal :: ProtocolSpec -> Q [Dec]
generateServerInternal ps = do
  (methods, _) <- runWriterT $ generateMethods ps Server
  (listeners, _) <- runWriterT $ generateListenerMethods ps Server
  cInterfaces <- generateCInterfaceDecs ps

  return $ methods ++ listeners ++ cInterfaces

-- | Generate code that exports the right symbols to the user
generateServerExports :: ProtocolSpec -> Q [Dec]
generateServerExports ps = do
  --(_, enumNames) <- runWriterT $ generateEnums ps
  (_, methodNames) <- runWriterT $ generateMethods ps Server
  (_, listenerNames) <- runWriterT $ generateListenerMethods ps Server
  let names = methodNames ++ listenerNames

  concat <$> mapM nameToDec names
    where
      nameToDec :: String -> Q [Dec]
      nameToDec name = [d|$(varP $ mkName name) = $(varE $ mkName $ "Import." ++ name) |]

--
-- Helper functions below
--

genMessageCType :: Maybe TypeQ -> [Argument] -> TypeQ
genMessageCType = genMessageType argTypeToCType

genMessageWeirdCType :: Maybe TypeQ -> [Argument] -> TypeQ
genMessageWeirdCType = genMessageType argTypeToWeirdInterfaceCType

genMessageHaskType :: Maybe TypeQ -> [Argument] -> TypeQ
genMessageHaskType = genMessageType argTypeToHaskType

genMessageType :: (Argument -> TypeQ) -> Maybe TypeQ -> [Argument] -> TypeQ
genMessageType fun Nothing args =
  foldr (\addtype curtype -> [t|$(fun addtype) -> $curtype|]) [t|IO ()|] args
genMessageType fun (Just someType) args =
  foldr (\addtype curtype -> [t|$(fun addtype) -> $curtype|]) someType args

-- | 3-tuple version of snd
snd3 :: (a,b,c) -> b
snd3 (_,b,_) = b

-- | Check if a given message argument is of type new_id
isNewId :: Argument -> Bool
isNewId arg = case arg of
                   (_, NewIdArg _ _, _) -> True
                   _                  -> False
