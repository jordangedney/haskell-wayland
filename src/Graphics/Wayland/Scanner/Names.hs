module Graphics.Wayland.Scanner.Names (
  ServerClient(..),

  registryBindName,
  -- apparently we are not allowed to use foreign C names generated by the C scanner
  requestInternalCName, eventInternalCName,
  -- requestForeignCName, eventForeignCName,
  requestHaskName, eventHaskName,

  interfaceTypeName, interfaceCInterfaceName,
  enumTypeName, enumEntryHaskName,
  messageListenerTypeName,
  messageListenerMessageName,
  messageListenerWrapperName,
  interfaceResourceCreator,

  capitalize
  ) where

import Data.Char
import Data.List
import Language.Haskell.TH

import Graphics.Wayland.Scanner.Types


registryBindName :: ProtocolName -> InterfaceName -> String
registryBindName pname iname = "registryBind" ++ (capitalize $ haskifyInterfaceName pname iname)

requestInternalCName :: InterfaceName -> MessageName -> Name
requestInternalCName iface msg = mkName $ iface ++ "_" ++ msg ++ "_request_binding"
eventInternalCName :: InterfaceName -> MessageName -> Name
eventInternalCName iface msg = mkName $ iface ++ "_" ++ msg ++ "_event_binding"

requestHaskName :: ProtocolName -> InterfaceName -> MessageName -> String
requestHaskName pname iname mname = toCamel (haskifyInterfaceName pname iname ++ "_" ++ mname)
eventHaskName :: ProtocolName -> InterfaceName -> MessageName -> String
eventHaskName = requestHaskName
enumEntryHaskName :: ProtocolName -> InterfaceName -> EnumName -> String -> Name
enumEntryHaskName pname iname ename entryName =
  mkName $ haskifyInterfaceName pname iname ++ capitalize (toCamel ename) ++ capitalize (toCamel entryName)

interfaceTypeName :: ProtocolName -> InterfaceName -> String
interfaceTypeName pname iname = capitalize $ haskifyInterfaceName pname iname

interfaceCInterfaceName :: ProtocolName -> InterfaceName -> Name
interfaceCInterfaceName _ iname = mkName $ iname ++ "_c_interface"

enumTypeName :: ProtocolName -> InterfaceName -> EnumName -> Name
enumTypeName pname iname ename = mkName $ capitalize $ haskifyInterfaceName pname iname ++ capitalize (toCamel ename)

messageListenerTypeName :: ServerClient -> ProtocolName -> InterfaceName -> Name
messageListenerTypeName Server pname iname = mkName $ capitalize (haskifyInterfaceName pname iname) ++ "Implementation"
messageListenerTypeName Client pname iname = mkName $ capitalize (haskifyInterfaceName pname iname) ++ "Listener"

messageListenerMessageName :: ServerClient -> ProtocolName -> InterfaceName -> MessageName -> String
messageListenerMessageName Server = requestHaskName
messageListenerMessageName Client = eventHaskName

messageListenerWrapperName :: ServerClient -> InterfaceName -> MessageName -> Name
messageListenerWrapperName Client iname mname = mkName $ iname ++ "_" ++ mname ++ "_listener_wrapper"
messageListenerWrapperName Server iname mname = mkName $ iname ++ "_" ++ mname ++ "_implementation_wrapper"

interfaceResourceCreator :: ProtocolName -> InterfaceName -> Name
interfaceResourceCreator pname iname = mkName $ pname ++ "_" ++ iname ++ "_resource_create"

-- | Some interfaces use a naming convention where wl_ or their protocol's name is prepended.
--   We remove both because it doesn't look very Haskelly.
haskifyInterfaceName :: ProtocolName -> InterfaceName -> String
haskifyInterfaceName pname iname =
  toCamel $ removeInitial (pname ++ "_") $ removeInitial "wl_" iname


-- stupid utility functions follow

-- | if the second argument starts with the first argument, strip that start
removeInitial :: Eq a => [a] -> [a] -> [a]
removeInitial remove input = if remove `isPrefixOf` input
                                     then drop (length remove) input
                                     else input

-- | convert some_string to someString
toCamel :: String -> String
toCamel (a:'_':c:d) | isAlpha a, isAlpha c = a : toUpper c : toCamel d
toCamel (a:b) = a : toCamel b
toCamel x = x


capitalize :: String -> String
capitalize x = toUpper (head x) : tail x

-- decapitalize :: String -> String
-- decapitalize x = toLower (head x) : tail x