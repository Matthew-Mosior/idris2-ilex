module XML.Parser

import Data.Bits
import Data.Buffer
import Data.ByteString
import Data.Linear.Ref1
import Data.SortedMap
import Data.String
import Derive.Prelude
import FS.Posix
import IO.Async.Loop.Epoll
import IO.Async.Loop.Posix
import Syntax.T1
import Text.ILex.Derive
import Text.ILex.FS

import public Text.ILex

%default total
%language ElabReflection

--------------------------------------------------------------------------------
--          Globally Forbidden Characters
--------------------------------------------------------------------------------

forbidden : RExp True
forbidden = -- basic control blocks
            range32 0x00 0x08 &&
            range32 0x0b 0x0c &&
            range32 0x0e 0x1f &&
            -- DEL + C1 controls
            range32 0x7f 0x84 &&
            range32 0x86 0x9f &&
            -- UTF-16 surrogate block
            range32 0xd800 0xdfff &&
            -- unicode characters (fixed block)
            range32 0xfdd0 0xfdef &&
            -- non-characters at end of each unicode plane
            range32 0xfffe 0xffff &&
            range32 0x1fffe 0x1ffff &&
            range32 0x2fffe 0x2ffff &&
            range32 0x3fffe 0x3ffff &&
            range32 0x4fffe 0x4ffff &&
            range32 0x5fffe 0x5ffff &&
            range32 0x6fffe 0x6ffff &&
            range32 0x7fffe 0x7ffff &&
            range32 0x8fffe 0x8ffff &&
            range32 0x9fffe 0x9ffff &&
            range32 0xafffe 0xaffff &&
            range32 0xbfffe 0xbffff &&
            range32 0xcfffe 0xcffff &&
            range32 0xdfffe 0xdffff &&
            range32 0xefffe 0xeffff &&
            range32 0xffffe 0xfffff &&
            range32 0x10fffe 0x10ffff

--------------------------------------------------------------------------------
--          XMLMiscValue
--------------------------------------------------------------------------------

public export
data XMLMiscValue : Type where
  XMLMiscComment                     : ByteString -> XMLMiscValue
  XMLMiscProcessingInstructionTarget : ByteString -> XMLMiscValue
  XMLMiscProcessingInstructionData   : ByteString -> XMLMiscValue
  XMLMiscNL                          : ByteString -> XMLDeclValue
  XMLMiscWhitespace                  : ByteString -> XMLDeclValue

--------------------------------------------------------------------------------
--          XMLMiscValue - RExp
--------------------------------------------------------------------------------

xmlmisccomment : RExp True
xmlmisccomment = (star $ dot && not '-' && not forbidden) || ('-' >> (star $ dot && not '-' && not forbidden))

xmlmiscprocessinginstructiontarget : RExp True
xmlmiscprocessinginstructiontarget = (alpha <|> '_' <|> ':') >> (alpha <|> '-' <|> ':' <|> '.')

xmlmiscprocessinginstructiondata : RExp True
xmlmiscprocessinginstructiondata = plus $ oneOf ['<', '>', '&', '"', '\n'] && not forbidden

--------------------------------------------------------------------------------
--          XMLDeclValue
--------------------------------------------------------------------------------

public export
data XMLDeclValue : Type where
  XMLDeclVersion    : String -> XMDeclLValue
  XMLDeclEncoding   : String -> XMLDeclValue
  XMLDeclStandalone : Bool -> XMLDeclValue
  XMLDeclNL         : ByteString -> XMLDeclValue
  XMLDeclWhitespace : ByteString -> XMLDeclValue

--------------------------------------------------------------------------------
--          XMLDeclValue - RExp
--------------------------------------------------------------------------------

xmldeclwhitespace : RExp True
xmldeclwhitespace = ' ' <|> '\t'

xmldecllinebreak : RExp True
xmldecllinebreak = '\n' <|> "\n\r" <|> "\r\n" <|> '\r' <|> '\RS'

xmldeclversion : RExp True
xmldeclverion = str "1.0"

xmldeclencoding : RExp True
xmldeclencoding = str "UTF-8"

xmldeclstandalone : RExp True
xmldeclstandalone = str "yes" <|> str "no"

--------------------------------------------------------------------------------
--          XMLDocTypeValue
--------------------------------------------------------------------------------

public export
data XMLDocTypeValue : Type where
  XMLDocTypeName           : ByteString -> XMLDocTypeValue
  XMLDocTypeSystem         : ByteString -> XMLDocTypeValue
  XMLDocTypePublicPublicID : ByteString -> XMLDocTypeValue
  XMLDocTypePublicSystemID : ByteString -> XMLDocTypeValue
  XMLDocTypeNL             : ByteString -> XMLDocTypeValue
  XMLDocTypeWhitespace     : ByteString -> XMLDocTypeValue

--------------------------------------------------------------------------------
--          XMLDocTypeValue - RExp
--------------------------------------------------------------------------------

xmldoctypename : RExp True
xmldoctypename = (alpha <|> '_' <|> ':') >> (plus $ alphaNum <|> '-' <|> '_' <|> '.' <|> ':' <|> not forbidden)

xmldoctypesystem : RExp True
xmldoctypesystem = plus $ dot && not '"' && not forbidden

xmldoctypepublicpublicid : RExp True
xmldoctypepublicpublicid = plus $ dot && not '"' && not forbidden

xmldoctypepublicsystemid : RExp True
xmldoctypepublicsystemid = plus $ dot && not '"' && not forbidden

--------------------------------------------------------------------------------
--          XMLElementValue
--------------------------------------------------------------------------------

public export
data XMLElementValue : Type where
  XMLElementEmptyTag               : String -> XMLElementValue
  XMLElementStartTagName           : String -> XMLElementValue
  XMLElementStartTagAttributeName  : String -> XMLElementValue
  XMLElementStartTagAttributeValue : String -> XMLElementValue
  XMLElementStartTagNamespaceName  : String -> XMLElementValue
  XMLElementStartTagNamespaceValue : String -> XMLElementValue
  XMLElementCharData               : String -> XMLElementValue
  XMLElementMisc                   : XMLMiscValue -> XMLElementValue
  XMLElementCDATA                  : String -> XMLElementValue
  XMLElementNL                     : ByteString -> XMLElementValue
  XMLElementNode                   : List XMLElementValue -> XMLElementValue

--------------------------------------------------------------------------------
--          XMLElementValue - RExp
--------------------------------------------------------------------------------

xmlelementemptytag : RExp True
xmlelementemptytag = (alpha <|> '_' <|> ':' <|> not forbidden) >> (plus $ alphaNum <|> '-' <|> '_' <|> '.' <|> ':' <|> not forbidden)

xmlelementstarttagname : RExp True
xmlelementstarttagname = (alpha <|> '_' <|> ':' <|> not forbidden) >> (plus $ alphaNum <|> '-' <|> '_' <|> '.' <|> ':' <|> not forbidden)

xmlelementstarttagattributename : RExp True
xmlelementstarttagattributename = (alpha <|> '_' <|> ':' <|> not forbidden) >> (plus $ alphaNum <|> '-' <|> '_' <|> '.' <|> ':' <|> not forbidden)

xmlelementstarttagattributevalue : RExp True
xmlelementstarttagattributevalue = plus $ dot && not '<' && not '&' && not forbidden

xmlelementchardata : RExp True
xmlelementchardata = plus $ dot && not '<' && not '&' && not (str "]]>") && not forbidden

xmlelementcdata : RExp True
xmlelementcdata = plus $ dot && not (str "]]>") && not forbidden

--------------------------------------------------------------------------------
--          XMLDocument
--------------------------------------------------------------------------------

public export
record XMLDocument where
  constructor MkXMLDocument
  decl            : Maybe (List XMLDeclValue)
  postdeclmisc    : Maybe (List Misc)
  doctype         : Maybe (List XMLDocTypeValue)
  postdoctypemisc : Maybe (List Misc)
  root            : List XMLElementValue
  postrootmisc    : Maybe (List Misc)

%runElab derive "XMLDocument" [Show,Eq]

Interpolation XMLDocument where interpolate = show

--------------------------------------------------------------------------------
--          XMLSTCK
--------------------------------------------------------------------------------

public export
record XMLSTCK (q : Type) where
  constructor XML
  line               : Ref q Nat
  col                : Ref q Nat
  psns               : Ref q (SnocList Position)
  strs               : Ref q (SnocList String)
  err                : Ref q (Maybe $ BoundedErr Void)
  xmlelementstack    : Ref q (SnocList (String, SnocList XMLElementValue))
  xmldecl            : Ref q (SnocList XMLDeclValue)
  xmlpostdeclmisc    : Ref q (SnocList XMLMiscValue)
  xmldoctype         : Ref q (SnocList XMLDocTypeValue)
  xmlpostdoctypemisc : Ref q (SnocList XMLMiscValue)
  xmlrootelement     : Ref q (SnocList XMLElementValue)
  xmlpostrootmisc    : Ref q (SnocList XMLMiscValue)
  bytes              : Ref q ByteString

export %inline
HasPosition XMLSTCK where
  line      = XMLSTCK.line
  col       = XMLSTCK.col
  positions = XMLSTCK.psns

export %inline
HasError XMLSTCK Void where
  error = err

export %inline
HasStringLits XMLSTCK where
  strings = strs

export %inline
HasBytes XMLSTCK where
  bytes = XMLSTCK.bytes

export
xmlinit : F1 q (XMLSTCK q)
xmlinit = T1.do
  l  <- ref1 Z
  c  <- ref1 Z
  bs <- ref1 [<]
  ss <- ref1 [<]
  er <- ref1 Nothing
  es <- ref1 [<]
  xmldl <- ref1 [<]
  xmlpdl <- ref1 [<]
  xmldt <- ref1 [<]
  xmlpdt <- ref1 [<]
  xmlre <- ref1 [<]
  xmlpr <- ref1 [<]
  by <- ref1 ""
  pure (XML l c bs ss er es xmldl xmlpdl xmldt xmlpdt xmlre xmlpr by)

--------------------------------------------------------------------------------
--          Parser State
--------------------------------------------------------------------------------

%runElab deriveParserState "XMLSz" "XMLST"
  [ -- initial state
    "XMLIni"
    -- empty state
  , "XMLEmpty"
    -- declaration parser states
  , "XMLDeclVersionS"
  , "XMLDeclVersionStrStart"
  , "XMLDeclVersionStr"
  , "XMLDeclVersionE"
  , "XMLDeclVersionNLE"
  , "XMLDeclVersionWhitespaceE"
  , "XMLDeclEncodingS"
  , "XMLDeclEncodingStrStart"
  , "XMLDeclEncodingStr"
  , "XMLDeclEncodingE"
  , "XMLDeclEncodingNLE"
  , "XMLDeclEncodingWhitespaceE"
  , "XMLDeclEncodingPostUnfinished"
  , "XMLDeclStandaloneS"
  , "XMLDeclStandaloneStrStart"
  , "XMLDeclStandaloneStr"
  , "XMLDeclStandaloneE"
  , "XMLDeclStandaloneNLE"
  , "XMLDeclStandaloneWhitespaceE"
  -- post declaration misc parser states
  , "XMLPostDeclStart"
  , "XMLPostDeclMiscCommentNLE"
  , "XMLPostDeclMiscCommentWhitespaceE"
  , "XMLPostDeclMiscCommentStrStart"
  , "XMLPostDeclMiscCommentStr"
  , "XMLPostDeclMiscCommentE"
  , "XMLPostDeclMiscAfterProcessingInstructionTargetNLE"
  , "XMLPostDeclMiscAfterProcessingInstructionTargetWhitespaceE"
  , "XMLPostDeclMiscAfterProcessingInstructionDataNLE"
  , "XMLPostDeclMiscAfterProcessingInstructionDataWhitespaceE"
  , "XMLPostDeclMiscProcessingInstructionTargetStrStart"
  , "XMLPostDeclMiscProcessingInstructionTargetStr"
  , "XMLPostDeclMiscProcessingInstructionTargetE"
  , "XMLPostDeclMiscProcessingInstructionDataStrStart"
  , "XMLPostDeclMiscProcessingInstructionDataStr"
  , "XMLPostDeclMiscProcessingInstructionDataE"
  , "XMLPostDeclMiscProcessingInstructionE"
  -- doctype parser states
  , "XMLDocTypeNameS"
  , "XMLDocTypeNameStrStart"
  , "XMLDocTypeNameStr"
  , "XMLDocTypeNameE"
  , "XMLDocTypeSystemURIS"
  , "XMLDocTypeSystemURIStrStart"
  , "XMLDocTypeSystemURIStr"
  , "XMLDocTypeSystemURIE"
  , "XMLDocTypePublicPublicIDStrStart"
  , "XMLDocTypePublicPublicIDStr"
  , "XMLDocTypePublicPublicIDE"
  , "XMLDocTypePublicSystemIDS"
  , "XMLDocTypePublicSystemIDStrStart"
  , "XMLDocTypePublicSystemIDStr"
  , "XMLDocTypePublicSystemIDE"
  , "XMLDocTypeBeforeNameNLE"
  , "XMLDocTypeBeforeNameWhitespaceE"
  , "XMLDocTypeAfterNameNLE"
  , "XMLDocTypeAfterNameWhitespaceE"
  , "XMLDocTypeAfterSystemURINLE"
  , "XMLDocTypeAfterSystemURIWhitespaceE"
  , "XMLDocTypeAfterPublicPublicIDNLE"
  , "XMLDocTypeAfterPublicPublicIDWhitespaceE"
  , "XMLDocTypeAfterPublicSystemIDNLE"
  , "XMLDocTypeAfterPublicSystemIDWhitespaceE"
  -- post doctype misc parser states
  , "XMLPostDocTypeMiscCommentNLE"
  , "XMLPostDocTypeMiscCommentWhitespaceE"
  , "XMLPostDocTypeMiscCommentStrStart"
  , "XMLPostDocTypeMiscCommentStr"
  , "XMLPostDocTypelMiscCommentE"
  , "XMLPostDocTypeMiscAfterProcessingInstructionTargetNLE"
  , "XMLPostDocTypeMiscAfterProcessingInstructionTargetWhitespaceE"
  , "XMLPostDocTypeMiscAfterProcessingInstructionDataNLE"
  , "XMLPostDocTypeMiscAfterProcessingInstructionDataWhitespaceE"
  , "XMLPostDocTypeMiscProcessingInstructionTargetStrStart"
  , "XMLPostDocTypeMiscProcessingInstructionTargetStr"
  , "XMLPostDocTypeMiscProcessingInstructionTargetE"
  , "XMLPostDoctypeMiscProcessingInstructionDataStrStart"
  , "XMLPostDocTypeMiscProcessingInstructionDataStr"
  , "XMLPostDocTypeMiscProcessingInstructionDataE"
  , "XMLPostDocTypeMiscProcessingInstructionE"
  -- root element parser states
  , "XMLElementEmptyTagS"
  , "XMLElementEmptyTagStrStart"
  , "XMLElementEmptyTagStr"
  , "XMLElementEmptyTagE"
  , "XMLElementStartTagNameStrStart"
  , "XMLElementStartTagNameStr"
  , "XMLElementStartTagNameE"
  , "XMLElementStartTagAttributeNameS"
  , "XMLElementStartTagAttributeNameStrStart"
  , "XMLElementStartTagAttributeNameStr"
  , "XMLElementStartTagAttributeNameE"
  , "XMLElementStartTagAttributeValueS"
  , "XMLElementStartTagAttributeValueStrStart"
  , "XMLElementStartTagAttributeValueStr"
  , "XMLElementStartTagAttributeValueE"
  , "XMLElementStartTagNamespaceNameS"
  , "XMLElementStartTagNamespaceNameStrStart"
  , "XMLElementStartTagNamespaceNameStr"
  , "XMLElementStartTagNamespaceNameE"
  , "XMLElementStartTagNamespaceValueS"
  , "XMLElementStartTagNamespaceValueStrStart"
  , "XMLElementStartTagNamespaceValueStr"
  , "XMLElementStartTagNamespaceValueE"
  , "XMLElementCharDataS"
  , "XMLElementCharDataStrStart"
  , "XMLElementCharDataStr"
  , "XMLElementCharDataE"
  , "XMLElementMiscCommentS"
  , "XMLElementMiscCommentStrStart"
  , "XMLElementMiscCommentStr"
  , "XMLElementMiscCommentE"
  , "XMLElementMiscProcessingInstructionS"
  , "XMLElementMiscProcessingInstructionTargetStrStart"
  , "XMLElementMiscProcessingInstructionTargetStr"
  , "XMLElementMiscProcessingInstructionTargetE"
  , "XMLElementMiscProcessingInstructionDataStrStart"
  , "XMLElementMiscProcessingInstructionDataStr"
  , "XMLElementMiscProcessingInstructionDataE"
  , "XMLElementCDATAS"
  , "XMLElementCDATAStrStart"
  , "XMLElementCDATAStr"
  , "XMLElementCDATAE"
  , "XMLElementEndTagS"
  , "XMLElementEndTagStrStart"
  , "XMLElementEndTagStr"
  , "XMLElementEndTagE"
  -- post root element misc parser states
  , "XMLPostElementMiscCommentNLE"
  , "XMLPostElementMiscCommentWhitespaceE"
  , "XMLPostElementMiscCommentStrStart"
  , "XMLPostElementMiscCommentStr"
  , "XMLPostElementMiscCommentE"
  , "XMLPostElementMiscAfterProcessingInstructionTargetNLE"
  , "XMLPostElementMiscAfterProcessingInstructionTargetWhitespaceE"
  , "XMLPostElementMiscAfterProcessingInstructionDataNLE"
  , "XMLPostElementMiscAfterProcessingInstructionDataWhitespaceE"
  , "XMLPostElementMiscProcessingInstructionTargetStrStart"
  , "XMLPostElementMiscProcessingInstructionTargetStr"
  , "XMLPostElementMiscProcessingInstructionTargetE"
  , "XMLPostElementMiscProcessingInstructionDataStrStart"
  , "XMLPostElementMiscProcessingInstructionDataStr"
  , "XMLPostElementMiscProcessingInstructionDataE"
  , "XMLPostElementMiscProcessingInstructionE"
    -- terminal state
  , "XMLDone"
  ]

--------------------------------------------------------------------------------
--          Errors
--------------------------------------------------------------------------------

xmlErr : Arr32 XMLSz (XMLSTCK q -> F1 q (BoundedErr Void))
xmlErr =
  arr32 XMLSz (unexpected [])
    [ E XMLBroken $ unexpected ["character other than '>'"]
    , E XMLEmpty $ unexpected ["sequence data"]
    ]

--------------------------------------------------------------------------------
--          State Transitions and DFAs - declaration
--------------------------------------------------------------------------------

onXMLDeclPostVersionNL : (x : XMLSTCK q) => ByteString -> F1 q XMLST
onXMLDeclPostVersionNL v = incline 1 >> push1 x.xmldecl (XMLDeclNL v) >> pure XMLDeclVersionNLE

onXMLDeclPostVersionWhitespace : (x : XMLSTCK q) => ByteString -> F1 q XMLST
onXMLDeclPostVersionWhitespace v = push1 x.xmldecl (XMLDeclWhitespace v) >> pure XMLDeclVersionWhitespaceE

onXMLDeclPostEncodingNL : (x : XMLSTCK q) => ByteString -> F1 q XMLST
onXMLDeclPostEncodingNL v = incline 1 >> push1 x.xmldecl (XMLDeclNL v) >> pure XMLDeclEncodingNLE

onXMLDeclPostEncodingWhitespace : (x : XMLSTCK q) => ByteString -> F1 q XMLST
onXMLDeclPostEncodingWhitespace v = push1 x.xmldecl (XMLDeclWhitespace v) >> pure XMLDeclEncodingWhitespaceE

onXMLDeclPostStandaloneNL : (x : XMLSTCK q) => ByteString -> F1 q XMLST
onXMLDeclPostStandaloneNL v = incline 1 >> push1 x.xmldecl (XMLDeclNL v) >> pure XMLDeclStandaloneNLE

onXMLDeclPostStandaloneWhitespace : (x : XMLSTCK q) => ByteString -> F1 q XMLST
onXMLDeclPostStandaloneWhitespace v = push1 x.xmldecl (XMLDeclWhitespace v) >> pure XMLDeclStandaloneWhitespaceE

onXMLDeclVersionStrEnd : (x : XMLSTCK) => XMLDeclValue -> F1 q XMLST
onXMLDeclVersionStrEnd v = push1 x.xmldecl v >> pure XMLDeclVersionE

onXMLDeclEncodingStrEnd : (x : XMLSTCK) => XMLDeclValue -> F1 q XMLST
onXMLDeclEncodingStrEnd v = push1 x.xmldecl v >> pure XMLDeclEncodingE

onXMLDeclStandaloneStrEnd : (x : XMLSTCK) => XMLDeclValue -> F1 q XMLST
onXMLDeclStandaloneStrEnd v = push1 x.xmldecl v >> pure XMLDeclStandaloneE

xmlDeclVersionS : DFA q XMLSz XMLSTCK
xmlDeclVersionS =
  dfa
    [ copen '"' (pure XMLDeclVersionStrStart)
    ]

xmlDeclVersionStr : DFA q XMLSz XMLSTCK
xmlDeclVersionStr =
  dfa
    [ cclose '"' $ getStr >>= onXMLDeclVersionStrEnd . XMLDeclVersion
    , read (plus $ dot && not '"') (pushStr XMLDeclVersionStr)
    ]

xmlDeclEncodingS : DFA q XMLSz XMLSTCK
xmlDeclEncodingS =
  dfa
    [ copen '"' (pure XMLDeclEncodingStrStart)
    ]

xmlDeclEncodingStr : DFA q XMLSz XMLSTCK
xmlDeclEncodingStr =
  dfa
    [ cclose '"' $ getStr >>= onXMLDeclEncodingStrEnd . XMLDeclEncoding
    , read (plus $ dot && not '"') (pushStr XMLDeclEncodingStr)
    ]

xmlDeclStandaloneS : DFA q XMLSz XMLSTCK
xmlDeclStandaloneS =
  dfa
    [ copen '"' (pure XMLDeclStandaloneStrStart)
    ]

xmlDeclStandaloneStr : DFA q XMLSz XMLSTCK
xmlDeclStandaloneStr =
  dfa
    [ cclose '"' $ getStr >>= onXMLDeclStandaloneStrEnd . XMLDeclStandalone
    , read (plus $ dot && not '"') (pushStr XMLDeclStandaloneStr)
    ]

--------------------------------------------------------------------------------
--          State Transitions and DFAs - post declaration misc
--------------------------------------------------------------------------------

onXMLDeclMiscCommentStrEnd : (x : XMLSTCK) => XMLMiscValue -> F1 q XMLST
onXMLDeclMiscCommentStrEnd v = push1 x.xmlpostdeclmisc v >> pure XMLDeclMiscCommentE

onXMLPostDeclMiscProcessingInstructionTargetStrEnd : (x : XMLSTCK) => XMLMiscValue -> F1 q XMLST
onXMLPostDeclMiscProcessingInstructionTargetStrEnd v = push1 x.xmlpostdeclmisc v >> pure XMLPostDeclMiscProcessingInstructionTargetE

onXMLPostDeclMiscProcessingInstructionDataStrEnd : (x : XMLSTCK) => XMLMiscValue -> F1 q XMLST
onXMLPostDeclMiscProcessingInstructionDataStrEnd v = push1 x.xmlpostdeclmisc v >> pure XMLPostDeclMiscProcessingInstructionDataE

onXMLPostDeclMiscCommentNL : (x : XMLSTCK q) => ByteString -> F1 q XMLST
onXMLPostDeclMiscCommentNL v = incline 1 >> push1 x.xmlpostdeclmisc (XMLMiscNL v) >> pure XMLPostDeclMiscCommentNLE

onXMLPostDeclMiscCommentWhitespace : (x : XMLSTCK q) => ByteString -> F1 q XMLST
onXMLPostDeclMiscCommentWhitespace v = push1 x.xmlpostdeclmisc (XMLMiscWhitespace v) >> pure XMLPostDeclMiscCommentWhitespaceE

onXMLPostDeclMiscAfterProcessingInstructionTargetNL : (x : XMLSTCK q) => ByteString -> F1 q XMLST
onXMLPostDeclMiscAfterProcessingInstructionTargetNL v = incline 1 >> push1 x.xmlpostdeclmisc (XMLMiscNL v) >> pure XMLPostDeclMiscAfterProcessingInstructionTargetNLE

onXMLPostDeclMiscAfterProcessingInstructionTargetWhitespace : (x : XMLSTCK q) => ByteString -> F1 q XMLST
onXMLPostDeclMiscAfterProcessingInstructionTargetWhitespace v = push1 x.xmlpostdeclmisc (XMLMiscWhitespace v) >> pure XMLPostDeclMiscAfterProcessingInstructionTargetWhitespaceE

onXMLPostDeclMiscAfterProcessingInstructionDataNL : (x : XMLSTCK q) => ByteString -> F1 q XMLST
onXMLPostDeclMiscAfterProcessingInstructionDataNL v = incline 1 >> push1 x.xmlpostdeclmisc (XMLMiscNL v) >> pure XMLPostDeclMiscAfterProcessingInstructionDataNLE

onXMLPostDeclMiscAfterProcessingInstructionDataWhitespace : (x : XMLSTCK q) => ByteString -> F1 q XMLST
onXMLPostDeclMiscAfterProcessingInstructionDataWhitespace v = push1 x.xmlpostdeclmisc (XMLMiscWhitespace v) >> pure XMLPostDeclMiscAfterProcessingInstructionDataWhitespaceE

xmlPostDeclMiscCommentStr : DFA q XMLSz XMLSTCK
xmlPostDeclMiscCommentStr =
  dfa
    [ conv linebreak (\bs => onXMLPostDeclMiscCommentNL bs)
    , conv whitespace (\bs => onXMLPostDeclMiscCommentWhitespace bs)
    , conv (plus $ dot && not "--") (pushStr XMLDeclStandaloneStr)
    ]

--------------------------------------------------------------------------------
--          State Transitions and DFAs - documentation type declaration
--------------------------------------------------------------------------------

onXMLDocTypeBeforeNameNL : (x : XMLSTCK q) => ByteString -> F1 q XMLST
onXMLDoctypeBeforeNameNL v = incline 1 >> push1 x.xmldoctype (XMLDocTypeNL v) >> pure XMLDocTypeBeforeNameNLE

onXMLDocTypeBeforeNameWhitespace : (x : XMLSTCK q) => ByteString -> F1 q XMLST
onXMLDoctypeBeforeNameWhitespace v = push1 x.xmldoctype (XMLDocTypeWhitespace v) >> pure XMLDocTypeBeforeNameWhitespaceE

onXMLDocTypeNameStrEnd : (x : XMLSTCK) => XMLDocTypeValue -> F1 q XMLST
onXMLDocTypeNameStrEnd v = push1 x.xmldoctype v >> pure XMLDocTypeNameE

onXMLDocTypeAfterNameNL : (x : XMLSTCK q) => ByteString -> F1 q XMLST
onXMLDoctypeAfterNameNL v = incline 1 >> push1 x.xmldoctype (XMLDocTypeNL v) >> pure XMLDocTypeAfterNameNLE

onXMLDocTypeAfterNameWhitespace : (x : XMLSTCK q) => ByteString -> F1 q XMLST
onXMLDoctypeAfterNameWhitespace v = push1 x.xmldoctype (XMLDocTypeWhitespace v) >> pure XMLDocTypeAfterNameWhitespaceE

onXMLDocTypeSystemURIStrEnd : (x : XMLSTCK) => XMLDocTypeValue -> F1 q XMLST
onXMLDocTypeSystemURIStrEnd v = push1 x.xmldoctype v >> pure XMLDocTypeSystemURIE

onXMLDocTypeAfterSystemURINL : (x : XMLSTCK q) => ByteString -> F1 q XMLST
onXMLDoctypeAfterSystemURINL v = incline 1 >> push1 x.xmldoctype (XMLDocTypeNL v) >> pure XMLDocTypeAfterSystemURINLE

onXMLDocTypeAfterSystemURIWhitespace : (x : XMLSTCK q) => ByteString -> F1 q XMLST
onXMLDoctypeAfterSystemURIWhitespace v = push1 x.xmldoctype (XMLDocTypeWhitespace v) >> pure XMLDocTypeAfterSystemURIWhitespaceE

onXMLDocTypePublicPublicPublicIDStrEnd : (x : XMLSTCK) => XMLDocTypeValue -> F1 q XMLST
onXMLDoctypePublicPublicPublicIDStrEnd v = push1 x.xmldoctype v >> pure XMLDocTypePublicPublicIDE

onXMLDocTypeAfterPublicPublicIDNL : (x : XMLSTCK q) => ByteString -> F1 q XMLST
onXMLDoctypeAfterPublicPublicIDNL v = incline 1 >> push1 x.xmldoctype (XMLDocTypeNL v) >> pure XMLDocTypeAfterPublicPublicIDNLE

onXMLDocTypeAfterPublicPublicIDWhitespace : (x : XMLSTCK q) => ByteString -> F1 q XMLST
onXMLDoctypeAfterPublicPublicIDWhitespace v = push1 x.xmldoctype (XMLDocTypeWhitespace v) >> pure XMLDocTypeAfterPublicPublicIDWhitespaceE

onXMLDocTypePublicPublicSystemIDStrEnd : (x : XMLSTCK) => XMLDocTypeValue -> F1 q XMLST
onXMLDoctypePublicPublicSystemIDStrEnd v = push1 x.xmldoctype v >> pure XMLDocTypePublicSystemIDE

onXMLDocTypeAfterPublicSystemIDNL : (x : XMLSTCK q) => ByteString -> F1 q XMLST
onXMLDoctypeAfterPublicSystemIDNL v = incline 1 >> push1 x.xmldoctype (XMLDocTypeNL v) >> pure XMLDocTypeAfterPublicSystemIDNLE

onXMLDocTypeAfterPublicSystemIDWhitespace : (x : XMLSTCK q) => ByteString -> F1 q XMLST
onXMLDoctypeAfterPublicSystemIDWhitespace v = push1 x.xmldoctype (XMLDocTypeWhitespace v) >> pure XMLDocTypeAfterPublicSystemIDWhitespaceE

xmlDocTypeNameStr : DFA q XMLSz XMLSTCK
xmlDocTypeNameStr =
  dfa
    [ conv linebreak (\bs => onXMLDocTypeNL bs)
    , conv whitespace (\bs => onXMLDocTypeWhitespace bs)
    , conv (plus $ dot && not linebreak && not whitespace) (onXMLDocTypeNameStrEnd . XMLDocTypeName)
    ]

xmlDocTypeSystemURIStr : DFA q XMLSz XMLSTCK
xmlDocTypeSystemURIStr =
  dfa
    [ conv linebreak (\bs => onXMLDocTypeBeforeNameNL bs)
    , conv whitespace (\bs => onXMLDocTypeBeforeNameWhitespace bs)
    , conv (plus $ dot && not linebreak && not whitespace) (onXMLDocTypeSystemURIStrEnd . XMLDocTypeSystem)
    ]

xmlDocTypePublicPublicIDStr : DFA q XMLSz XMLSTCK
xmlDocTypePublicPublicIDStr =
  dfa
    [ conv linebreak (\bs => onXMLDocTypeBeforePublicPublicIDNL bs)
    , conv whitespace (\bs => onXMLDocTypeBeforePublicPublicIDWhitespace bs)
    , conv (plus $ dot && not linebreak && not whitespace) (onXMLDocTypePublicPublicIDStrEnd . XMLDocTypePublicPublicID)
    ]

xmlDocTypePublicSystemIDStr : DFA q XMLSz XMLSTCK
xmlDocTypePublicSystemIDStr =
  dfa
    [ conv linebreak (\bs => onXMLDocTypeBeforePublicSystemIDNL bs)
    , conv whitespace (\bs => onXMLDocTypeBeforePublicSystemIDWhitespace bs)
    , conv (plus $ dot && not linebreak && not whitespace) (onXMLDocTypePublicSystemIDStrEnd . XMLDocTypePublicSystemID)
    ]

--------------------------------------------------------------------------------
--          State Transition - EOI
--------------------------------------------------------------------------------

onEOI : (x : FSTCK q) => F1 q (Either (BoundedErr Void) FST)
onEOI = T1.do
  incline 1
  xmlvs@(_::_) <- getList x.xmlvalues
    | [] => arrFail XMLSTCK xmlErr XMLEmpty x
  ln <- read1 x.line
  push1 x.xmldoc (MkXMLValues ln xmlvs)
  pure (Right XMLDone)

--------------------------------------------------------------------------------
--          DFA - initial
--------------------------------------------------------------------------------

xmlInit : DFA q XMLSz XMLSTCK
xmlInit =
  dfa
    [ read (str "<?xml version=") (pure XMLDeclVersionS)
    , conv (str "<!--") (pure XMLPostDeclMiscCommentS)
    , conv (str "<?") (pure XMLPostDeclMiscProcessingInstructionTargetStrStart)
    , conv (str "<!DOCTYPE") (pure XMLDocTypeNameS)
    , conv '<' (pure XMLElementStartTagNameS)
    ]

--------------------------------------------------------------------------------
--          DFA - after declaration version
--------------------------------------------------------------------------------

xmlDeclVersionAfter : DFA q XMLSz XMLSTCK
xmlDeclVersionAfter =
  dfa
    [ conv linebreak (\bs => onXMLDeclPostVersionNL bs)
    , conv whitespace (\bs => onXMLDeclPostVersionWhitespace bs)
    , read (str "encoding=") (pure XMLDeclEncodingS)
    , read (str "standalone=") (pure XMLDeclStandaloneS)
    , read (str "?>") (pure XMLPostDeclStart)
    ]

--------------------------------------------------------------------------------
--          DFA - after declaration encoding
--------------------------------------------------------------------------------

xmlDeclEncodingAfter : DFA q XMLSz XMLSTCK
xmlDeclEncodingAfter =
  dfa
    [ conv linebreak (\bs => onXMLDeclPostEncodingNL bs)
    , conv whitespace (\bs => onXMLDeclPostEncodingWhitespace bs)
    , read (str "standalone=") (pure XMLDeclStandaloneS)
    , read (str "?>") (pure XMLPostDeclStart)
    ]

--------------------------------------------------------------------------------
--          DFA - after declaration standalone
--------------------------------------------------------------------------------

xmlDeclStandaloneAfter : DFA q XMLSz XMLSTCK
xmlDeclStandaloneAfter =
  dfa
    [ conv linebreak (\bs => onXMLDeclPostStandaloneNL bs)
    , conv whitespace (\bs => onXMLDeclPostStandaloneWhitespace bs)
    , read (str "?>") (pure XMLPostDeclStart)
    ]

--------------------------------------------------------------------------------
--          DFA - start of post declaration
--------------------------------------------------------------------------------

xmlPostDeclStart : DFA q XMLSz XMLSTCK
xmlPostDeclStart =
  dfa
    [ conv linebreak (\bs => onXMLDeclPostStandaloneNL bs)
    , conv whitespace (\bs => onXMLDeclPostStandaloneWhitespace bs)
    , read (str "<!--") (pure XMLMiscCommentStrStart)
    , read (str "<?") (pure XMLMiscProcessingInstructionTargetStrStart)
    , read (str "<!DOCTYPE") (pure XMLDocTypeNameS)
    , read '<' (pure XMLElementStartTagNameStrStart)
    ]

--------------------------------------------------------------------------------
--          DFA - after post declaration comment
--------------------------------------------------------------------------------

xmlPostDeclMiscCommentAfter : DFA q XMLSz XMLSTCK
xmlPostDeclMiscCommentAfter =
  dfa
    [ conv linebreak (\bs => onXMLPostDeclNL bs)
    , conv whitespace (\bs => onXMLPostDeclWhitespace bs)
    , read (str "<!--") (pure XMLMiscCommentStr)
    , read (str "<?") (pure XMLMiscProcessingInstructionTargetStrStart)
    , read (str "<!DOCTYPE") (pure XMLDocTypeNameStr)
    , read '<' (pure XMLElementStartTagNameStrStart)
    ]

--------------------------------------------------------------------------------
--          DFA - after post declaration processing instruction target
--------------------------------------------------------------------------------

xmlPostDeclMiscProcessingInstructionTargetAfter : DFA q XMLSz XMLSTCK
xmlPostDeclMiscProcessingInstructionTargetAfter =
  dfa
    [ conv linebreak (\bs => onXMLPostDeclNL bs)
    , conv whitespace (\bs => onXMLPostDeclWhitespace bs)
    , conv (plus $ dot && not linebreak && not whitespace && not "?>") (onXMLPostDeclProcessingInstructionDataStrEnd . XMLMiscProcessingInstructionData)
    , conv "?>" (pure XMLPostDeclMiscProcessingInstructionE)
    ]

--------------------------------------------------------------------------------
--          DFA - after post declaration processing instruction data
--------------------------------------------------------------------------------

xmlPostDeclMiscProcessingInstructionDataAfter : DFA q XMLSz XMLSTCK
xmlPostDeclMiscProcessingInstructionDataAfter =
  dfa
    [ conv linebreak (\bs => onXMLDocTypeBeforePublicPublicIDNL bs)
    , conv whitespace (\bs => onXMLDocTypeBeforePublicPublicIDWhitespace bs)
    , conv "?>" (pure XMLPostDeclMiscProcessingInstructionE)
    ]

--------------------------------------------------------------------------------
--          DFA - after doctype name
--------------------------------------------------------------------------------

xmlDocTypeNameAfter : DFA q XMLSz XMLSTCK
xmlDocTypeNameAfter =
  dfa
    [ conv linebreak (\bs => onXMLDocTypeAfterNameNL bs)
    , conv whitespace (\bs => onXMLDocTypeAfterNameWhitespace bs)
    , read '>' (pure XMLDocTypeFinished)
    ]

--------------------------------------------------------------------------------
--          DFA - after doctype system uri
--------------------------------------------------------------------------------

xmlDocTypeSystemURIAfter : DFA q XMLSz XMLSTCK
xmlDocTypeSystemURIAfter =
  dfa
    [ conv linebreak (\bs => onXMLDocTypeAfterSystemURINL bs)
    , conv whitespace (\bs => onXMLDocTypeAfterSystemURIWhitespace bs)
    , read '>' (pure XMLDocTypeFinished)
    ]

--------------------------------------------------------------------------------
--          DFA - after doctype public public id
--------------------------------------------------------------------------------

xmlDocTypePublicPublicIDAfter : DFA q XMLSz XMLSTCK
xmlDocTypePublicPublicIDAfter =
  dfa
    [ conv linebreak (\bs => onXMLDocTypeAfterPublicPublicIDNL bs)
    , conv whitespace (\bs => onXMLDocTypeAfterPublicPublicIDWhitespace bs)
    ]

--------------------------------------------------------------------------------
--          Parsers
--------------------------------------------------------------------------------

xmlSteps : Lex1 q XMLSz XMLSTCK
xmlSteps =
  lex1
    [ -- Initial state
      E XMLIni xmlInit
      -- XML declaration - optional
    , E XMLDeclVersionS xmlDeclVersionS
    , E XMLDeclVersionStrStart xmlDecVersionStr
    , E XMLDeclVersionNLE xmlDeclVersionAfter
    , E XMLDeclVersionWhitespaceE xmlDeclVersionAfter
    , E XMLDeclVersionE xmlDeclVersionAfter
    , E XMLDeclEncodingS xmlDeclEncodingS
    , E XMLDeclEncodingStrStart xmlDeclEncodingStr
    , E XMLDeclEncodingNLE xmlDeclEncodingAfter
    , E XMLDeclEncodingWhitespaceE xmlDeclEncodingAfter
    , E XMLDeclEncodingE xmlDeclEncodingAfter
    , E XMLDeclStandaloneS xmlDeclStandaloneS
    , E XMLDeclStandaloneStrStart xmlDeclStandaloneStr
    , E XMLDeclStandaloneNLE xmlDeclStandaloneAfter
    , E XMLDeclStandaloneWhitespaceE xmlDeclStandaloneAfter
    , E XMLDeclStandaloneE xmlDeclStandaloneAfter
      -- After XML declaration - optional (comments and processing instructions)
    , E XMLPostDeclStart xmlPostDeclStart
    , E XMLMiscCommentStrStart xmlPostDeclMiscCommentStr
    , E XMLPostDeclMiscProcessingInstructionTargetE xmlPostDeclMiscProcessingInstructionTargetAfter
    , E XMLPostDeclMiscProcessingInstructionDataE xmlPostDeclMiscProcessingInstructionDataAfter
    , E XMLPostDeclMiscCommentNLE xmlPostDeclStart
    , E XMLPostDeclMiscCommentWhiteSpaceE xmlPostDeclStart
    , E XMLMiscProcessingInstructionTargetStrStart xmlPostDeclMiscProcessingInstructionTargetStr
    , E XMLPostDeclMiscAfterProcessingInstructionTargetNLE xmlPostDeclMiscProcessingInstructionTargetAfter
    , E XMLPostDeclMiscAfterProcessingInstructionTargetWhitespaceE xmlPostDeclMiscProcessingInstructionTargetAfter
    , E XMLPostDeclMiscAfterProcessingInstructionDataNLE xmlPostDeclMiscProcessingInstructionDataAfter
    , E XMLPostDeclMiscAfterProcessingInstructionDataWhitespaceE xmlPostDeclMiscProcessingInstructionDataAfter
    -- XML DocType - optional
    ]

--------------------------------------------------------------------------------
--          EOI
--------------------------------------------------------------------------------

xmlEOI : XMLST -> XMLSTCK q -> F1 q (Either (BoundedErr Void) XMLDocument)
xmlEOI st x =
  case st == XMLIni || st == XMLEmpty of
    True  => arrFail XMLSTCK xmlErr st x
    False => T1.do
      _ <- onEOI
      xml <- getList x.xmldoc
      pure (Right xml)

--------------------------------------------------------------------------------
--          Parser
--------------------------------------------------------------------------------

export
xml : P1 q (BoundedErr Void) XMLSz XMLSTCK XMLDocument
xml = P XMLIni xmlinit xmlSteps snocChunk xmlErr xmlEOI

export %inline
parseXML : Origin -> String -> Either (ParseError Void) XMLDocument
parseXML = parseString xml

--------------------------------------------------------------------------------
--          Streaming
--------------------------------------------------------------------------------

streamXML :  String
          -> AsyncPull Poll Void [ParseError Void, Errno] ()
streamXML pth =
     readBytes pth
  |> streamParse xml (FileSrc pth)
  |> C.count
  |> printLnTo Stdout

streamXMLDocuments :  AsyncPull Poll String [ParseError Void, Errno] ()
                   -> AsyncPull Poll Void [ParseError Void, Errno] ()
streamXMLDocuments pths =
     flatMap pths (\p => readBytes p |> streamParse xml (FileSrc p))
  |> C.count
  |> printLnTo Stdout
