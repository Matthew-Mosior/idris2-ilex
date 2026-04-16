module XML.Parser

import XML.RExp

import Data.Bits
import Data.Buffer
import Data.ByteString
import Data.Linear.Ref1
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
--          XMLMiscValue
--------------------------------------------------------------------------------

public export
data XMLMiscValue : Type where
  XMLMiscComment                     : ByteString -> XMLMiscValue
  XMLMiscProcessingInstructionTarget : ByteString -> XMLMiscValue
  XMLMiscProcessingInstructionData   : ByteString -> XMLMiscValue
  XMLMiscWhitespace                  : ByteString -> XMLMiscValue

--------------------------------------------------------------------------------
--          XMLMiscValue - RExp
--------------------------------------------------------------------------------

xmlmisccomment : RExp True
xmlmisccomment = (plus $ char && not '-') || ('-' >> (plus $ char && not '-'))

xmlmiscprocessinginstructiontarget : RExp True
xmlmiscprocessinginstructiontarget = name && not (like "xml")

xmlmiscprocessinginstructiondata : RExp True
xmlmiscprocessinginstructiondata =  star $ char && not (str "?>")

--------------------------------------------------------------------------------
--          XMLDeclValue
--------------------------------------------------------------------------------

public export
data XMLDeclValue : Type where
  XMLDeclVersion    : String -> XMDeclLValue
  XMLDeclEncoding   : String -> XMLDeclValue
  XMLDeclStandalone : Bool -> XMLDeclValue
  XMLDeclWhitespace : ByteString -> XMLDeclValue

--------------------------------------------------------------------------------
--          XMLDeclValue - RExp
--------------------------------------------------------------------------------

xmldeclversion : RExp True
xmldeclversion = str "1.0"

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
  XMLDocTypeWhitespace     : ByteString -> XMLDocTypeValue

--------------------------------------------------------------------------------
--          XMLDocTypeValue - RExp
--------------------------------------------------------------------------------

xmldoctypename : RExp True
xmldoctypename = namestartchar >> star namechar

xmldoctypesystemdoublequote : RExp True
xmldoctypesystemdoublequote = star $ dot && not '"' && not forbidden

xmldoctypesystemsinglequote : RExp True
xmldoctypesystemsinglequote = star $ dot && not '\'' && not forbidden

xmldoctypepublicpubliciddoublequote : RExp True
xmldoctypepublicpubliciddoublequote = star $ pubidchar && not '"'

xmldoctypepublicpublicidsinglequote : RExp True
xmldoctypepublicpublicidsinglequote = star $ pubidchar && not '\''

xmldoctypepublicsystemidsinglequote : RExp True
xmldoctypepublicsystemidsinglequote = star $ dot && not '"' && not forbidden

xmldoctypepublicsystemidsinglequote : RExp True
xmldoctypepublicsystemidsinglequote = star $ dot && not '\'' && not forbidden

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
  XMLElementWhitespace             : ByteString -> XMLElementValue
  XMLElementNode                   : List XMLElementValue -> XMLElementValue

--------------------------------------------------------------------------------
--          XMLElementValue - RExp
--------------------------------------------------------------------------------

xmlelementstarttagname : RExp True
xmlelementstarttagname = namestartchar >> star namechar

xmlelementstarttagattributename : RExp True
xmlelementstarttagattributename = namestartchar >> star namechar

xmlelementstarttagattributevalue : RExp True
xmlelementstarttagattributevalue = star $ dot && not '<' && not '&' && not forbidden

xmlelementchardata : RExp True
xmlelementchardata = plus $ dot && not '<' && not '&' && not (str "]]>") && not forbidden

xmlelementcdata : RExp True
xmlelementcdata = plus $ dot && not (str "]]>") && not forbidden

xmlelementendtagname : RExp True
xmlelementendtagname = namestartchar >> star namechar

xmlelementemptytagname : RExp True
xmlelementemptytagname  = namestartchar >> star namechar

xmlelementemptytagattributename : RExp True
xmlelementemptytagattributename = namestartchar >> star namechar

xmlelementemptytagattributevalue : RExp True
xmlelementemptytagattributevalue = star $ dot && not '<' && not '&' && not forbidden

--------------------------------------------------------------------------------
--          XMLDocument
--------------------------------------------------------------------------------

public export
record XMLDocument where
  constructor MkXMLDocument
  decl            : Maybe (List XMLDeclValue)
  postdeclmisc    : Maybe (List XMLMiscValue)
  doctype         : Maybe (List XMLDocTypeValue)
  postdoctypemisc : Maybe (List XMLMiscValue)
  root            : List XMLElementValue
  postrootmisc    : Maybe (List XMLMiscValue)

%runElab derive "XMLDocument" [Show,Eq]

Interpolation XMLDocument where interpolate = show

--------------------------------------------------------------------------------
--          XMLSTCK
--------------------------------------------------------------------------------

public export
record XMLSTCK (q : Type) where
  constructor XML
  line                  : Ref q Nat
  col                   : Ref q Nat
  psns                  : Ref q (SnocList Position)
  strs                  : Ref q (SnocList String)
  err                   : Ref q (Maybe $ BoundedErr Void)
  xmlelementstack       : Ref q (SnocList (String, SnocList XMLElementValue))
  xmldecl               : Ref q (SnocList XMLDeclValue)
  xmlpostdeclmisc       : Ref q (SnocList XMLMiscValue)
  xmldoctype            : Ref q (SnocList XMLDocTypeValue)
  xmlpostdoctypemisc    : Ref q (SnocList XMLMiscValue)
  xmlrootelement        : Ref q (SnocList XMLElementValue)
  xmlpostrootmisc       : Ref q (SnocList XMLMiscValue)
  bytes                 : Ref q ByteString

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
  , "XMLDeclVersionWhitespaceE"
  , "XMLDeclEncodingS"
  , "XMLDeclEncodingStrStart"
  , "XMLDeclEncodingStr"
  , "XMLDeclEncodingE"
  , "XMLDeclEncodingWhitespaceE"
  , "XMLDeclStandaloneS"
  , "XMLDeclStandaloneStrStart"
  , "XMLDeclStandaloneStr"
  , "XMLDeclStandaloneE"
  , "XMLDeclStandaloneWhitespaceE"
  -- post declaration misc parser states
  , "XMLPostDeclStart"
  , "XMLPostDeclWhitespaceE"
  , "XMLPostDeclMiscCommentWhitespaceE"
  , "XMLPostDeclMiscCommentStrStart"
  , "XMLPostDeclMiscCommentStr"
  , "XMLPostDeclMiscCommentE"
  , "XMLPostDeclMiscAfterProcessingInstructionTargetWhitespaceE"
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
  , "XMLDocTypeSystemE"
  , "XMLDocTypeSystemURIDoubleQuoteStrStart"
  , "XMLDocTypeSystemURISingleQuoteStrStart"
  , "XMLDocTypeSystemURIStr"
  , "XMLDocTypeSystemURIE"
  , "XMLDocTypePublicE"
  , "XMLDocTypePublicPublicIDDoubleQuoteStrStart"
  , "XMLDocTypePublicPublicIDSingleQuoteStrStart"
  , "XMLDocTypePublicPublicIDStr"
  , "XMLDocTypePublicPublicIDE"
  , "XMLDocTypePublicSystemIDDoubleQuoteStrStart"
  , "XMLDocTypePublicSystemIDSingleQuoteStrStart"
  , "XMLDocTypePublicSystemIDStr"
  , "XMLDocTypePublicSystemIDE"
  , "XMLDocTypeBeforeNameWhitespaceE"
  , "XMLDocTypeAfterNameWhitespaceE"
  , "XMLDocTypeAfterSystemURIWhitespaceE"
  , "XMLDocTypeAfterPublicPublicIDWhitespaceE"
  , "XMLDocTypeAfterPublicSystemIDWhitespaceE"
  -- post doctype misc parser states
  , "XMLPostDocTypeStart"
  , "XMLPostDoctypeWhitespaceE"
  , "XMLPostDocTypeMiscCommentWhitespaceE"
  , "XMLPostDocTypeMiscCommentStrStart"
  , "XMLPostDocTypeMiscCommentStr"
  , "XMLPostDocTypeMiscCommentE"
  , "XMLPostDocTypeMiscAfterProcessingInstructionTargetWhitespaceE"
  , "XMLPostDocTypeMiscAfterProcessingInstructionDataWhitespaceE"
  , "XMLPostDocTypeMiscProcessingInstructionTargetStrStart"
  , "XMLPostDocTypeMiscProcessingInstructionTargetStr"
  , "XMLPostDocTypeMiscProcessingInstructionTargetE"
  , "XMLPostDocTypeMiscProcessingInstructionDataStrStart"
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
  , "XMLPostElementStart"
  , "XMLPostElementWhitespaceE"
  , "XMLPostElementMiscCommentWhitespaceE"
  , "XMLPostElementMiscCommentStrStart"
  , "XMLPostElementMiscCommentStr"
  , "XMLPostElementMiscCommentE"
  , "XMLPostElementMiscAfterProcessingInstructionTargetWhitespaceE"
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
    [ E XMLEmpty $ unexpected ["no root element"]
    , E XMLMismatchedStartEndTag $ unexpected ["start/end tag don't match"]
    ]

--------------------------------------------------------------------------------
--          State Transitions and DFAs - declaration
--------------------------------------------------------------------------------

onXMLDeclPostVersionWhitespace : (x : XMLSTCK q) => XMLDeclValue -> F1 q XMLST
onXMLDeclPostVersionWhitespace v = push1 x.xmldecl v >> pure XMLDeclVersionWhitespaceE

onXMLDeclPostEncodingWhitespace : (x : XMLSTCK q) => XMLDeclValue -> F1 q XMLST
onXMLDeclPostEncodingWhitespace v = push1 x.xmldecl v >> pure XMLDeclEncodingWhitespaceE

onXMLDeclPostStandaloneWhitespace : (x : XMLSTCK q) => XMLDeclValue -> F1 q XMLST
onXMLDeclPostStandaloneWhitespace v = push1 x.xmldecl v >> pure XMLDeclStandaloneWhitespaceE

onXMLDeclVersionStrEnd : (x : XMLSTCK) => XMLDeclValue -> F1 q XMLST
onXMLDeclVersionStrEnd v = push1 x.xmldecl v >> pure XMLDeclVersionE

onXMLDeclEncodingStrEnd : (x : XMLSTCK) => XMLDeclValue -> F1 q XMLST
onXMLDeclEncodingStrEnd v = push1 x.xmldecl v >> pure XMLDeclEncodingE

onXMLDeclStandaloneStrEnd : (x : XMLSTCK) => String -> F1 q XMLST
onXMLDeclStandaloneStrEnd s =
  case s of
    "yes" => T1.do
      push1 x.xmldecl (XMLDeclStandalone True) >> pure XMLDeclStandaloneE
    _ => T1.do
      push1 x.xmldecl (XMLDeclStandalone False) >> pure XMLDeclStandaloneE

xmlDeclVersionS : DFA q XMLSz XMLSTCK
xmlDeclVersionS =
  dfa
    [ copen '"' (pure XMLDeclVersionStrStart)
    ]

xmlDeclVersionStr : DFA q XMLSz XMLSTCK
xmlDeclVersionStr =
  dfa
    [ cclose '"' $ getStr >>= onXMLDeclVersionStrEnd . XMLDeclVersion
    , read xmldeclversion (pushStr XMLDeclVersionStr)
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
    , read xmldeclencoding (pushStr XMLDeclEncodingStr)
    ]

xmlDeclStandaloneS : DFA q XMLSz XMLSTCK
xmlDeclStandaloneS =
  dfa
    [ copen '"' (pure XMLDeclStandaloneStrStart)
    ]

xmlDeclStandaloneStr : DFA q XMLSz XMLSTCK
xmlDeclStandaloneStr =
  dfa
    [ cclose '"' $ getStr >>= (\str => onXMLDeclStandaloneStrEnd str)
    , read xmldeclstandalone (pushStr XMLDeclStandaloneStr)
    ]

--------------------------------------------------------------------------------
--          State Transitions and DFAs - post declaration misc
--------------------------------------------------------------------------------

onXMLPostDeclMiscCommentWhitespace : (x : XMLSTCK q) => XMLMiscValue -> F1 q XMLST
onXMLPostDeclMiscCommentWhitespace v = push1 x.xmlpostdeclmisc v >> pure XMLPostDeclMiscCommentWhitespaceE

onXMLPostDeclMiscAfterCommentWhitespace : (x : XMLSTCK q) => XMLMiscValue -> F1 q XMLST
onXMLPostDeclMiscAfterCommentWhitespace v = push1 x.xmlpostdeclmisc v >> pure XMLPostDeclMiscCommentWhitespaceE

onXMLPostDeclMiscAfterProcessingInstructionTargetWhitespace : (x : XMLSTCK q) => XMLMiscValue -> F1 q XMLST
onXMLPostDeclMiscAfterProcessingInstructionTargetWhitespace v = push1 x.xmlpostdeclmisc v >> pure XMLPostDeclMiscAfterProcessingInstructionTargetWhitespaceE

onXMLPostDeclMiscAfterProcessingInstructionDataWhitespace : (x : XMLSTCK q) => XMLMiscValue -> F1 q XMLST
onXMLPostDeclMiscAfterProcessingInstructionDataWhitespace v = push1 x.xmlpostdeclmisc v >> pure XMLPostDeclMiscAfterProcessingInstructionDataWhitespaceE

onXMLPostDeclMiscCommentStrEnd : (x : XMLSTCK) => XMLMiscValue -> F1 q XMLST
onXMLPostDeclMiscCommentStrEnd v = push1 x.xmlpostdeclmisc v >> pure XMLPostDeclMiscCommentE

onXMLPostDeclMiscProcessingInstructionTargetStrEnd : (x : XMLSTCK) => XMLMiscValue -> F1 q XMLST
onXMLPostDeclMiscProcessingInstructionTargetStrEnd v = push1 x.xmlpostdeclmisc v >> pure XMLPostDeclMiscProcessingInstructionTargetE

onXMLPostDeclMiscProcessingInstructionDataStrEnd : (x : XMLSTCK) => XMLMiscValue -> F1 q XMLST
onXMLPostDeclMiscProcessingInstructionDataStrEnd v = push1 x.xmlpostdeclmisc v >> pure XMLPostDeclMiscProcessingInstructionDataE

xmlPostDeclMiscCommentStr : DFA q XMLSz XMLSTCK
xmlPostDeclMiscCommentStr =
  dfa
    [ conv xmlmisccomment (onXMLPostDeclMiscCommentStrEnd . XMLMiscComment)
    ]

xmlPostDeclMiscProcessingInstructionTargetStr : DFA q XMLSz XMLSTCK
xmlPostDeclMiscProcessingInstructionTargetStr =
  dfa
    [ conv xmlmiscprocessinginstructiontarget (onXMLPostDeclMiscProcessingInstructionTargetStrEnd . XMLMiscProcessingInstructionTarget)
    ]

xmlPostDeclMiscProcessingInstructionDataStr : DFA q XMLSz XMLSTCK
xmlPostDeclMiscProcessingInstructionDataStr =
  dfa
    [ conv xmlmiscprocessinginstructiondata (onXMLPostDeclMiscProcessingInstructionDataStrEnd . XMLMiscProcessingInstructionData)
    ]

--------------------------------------------------------------------------------
--          State Transitions and DFAs - post declaration whitespace
--------------------------------------------------------------------------------

onXMLPostDeclWhitespace : (x : XMLSTCK q) => XMLMiscValue -> F1 q XMLST
onXMLPostDeclWhitespace v = push1 x.xmlpostdeclmisc v >> pure XMLPostDeclWhitespaceE

--------------------------------------------------------------------------------
--          State Transitions and DFAs - doctype declaration
--------------------------------------------------------------------------------

onXMLDocTypeBeforeNameWhitespace : (x : XMLSTCK q) => XMLDocTypeValue -> F1 q XMLST
onXMLDoctypeBeforeNameWhitespace v = push1 x.xmldoctype v >> pure XMLDocTypeBeforeNameWhitespaceE

onXMLDocTypeAfterNameWhitespace : (x : XMLSTCK q) => XMLDocTypeValue -> F1 q XMLST
onXMLDoctypeAfterNameWhitespace v = push1 x.xmldoctype v >> pure XMLDocTypeAfterNameWhitespaceE

onXMLDocTypeAfterSystem : (x : XMLSTCK q) => F1 q XMLST
onXMLDocTypeAfterSystem = pure XMLDocTypeSystemE

onXMLDocTypeAfterSystemWhitespace : (x : XMLSTCK q) => XMLDocTypeValue -> F1 q XMLST
onXMLDoctypeAfterSystemWhitespace v = push1 x.xmldoctype v >> pure XMLDocTypeAfterSystemWhitespaceE

onXMLDocTypeAfterSystemURIWhitespace : (x : XMLSTCK q) => XMLDocTypeValue -> F1 q XMLST
onXMLDoctypeAfterSystemURIWhitespace v = push1 x.xmldoctype v >> pure XMLDocTypeAfterSystemURIWhitespaceE

onXMLDocTypeAfterPublic : (x : XMLSTCK q) => F1 q XMLST
onXMLDocTypeAfterPublic = pure XMLDocTypePublicE

onXMLDocTypeAfterPublicWhitespace : (x : XMLSTCK q) => XMLDocTypeValue -> F1 q XMLST
onXMLDoctypeAfterPublicWhitespace v = push1 x.xmldoctype v >> pure XMLDocTypeAfterPublicWhitespaceE

onXMLDocTypeAfterPublicPublicIDWhitespace : (x : XMLSTCK q) => XMLDocTypeValue -> F1 q XMLST
onXMLDoctypeAfterPublicPublicIDWhitespace v = push1 x.xmldoctype v >> pure XMLDocTypeAfterPublicPublicIDWhitespaceE

onXMLDocTypeAfterPublicSystemIDWhitespace : (x : XMLSTCK q) => XMLDocTypeValue -> F1 q XMLST
onXMLDoctypeAfterPublicSystemIDWhitespace v = push1 x.xmldoctype v >> pure XMLDocTypeAfterPublicSystemIDWhitespaceE

onXMLDocTypeNameStrEnd : (x : XMLSTCK) => XMLDocTypeValue -> F1 q XMLST
onXMLDocTypeNameStrEnd v = push1 x.xmldoctype v >> pure XMLDocTypeNameE

onXMLDocTypeSystemURIStrEnd : (x : XMLSTCK) => XMLDocTypeValue -> F1 q XMLST
onXMLDocTypeSystemURIStrEnd v = push1 x.xmldoctype v >> pure XMLDocTypeSystemURIE

onXMLDocTypePublicPublicPublicIDStrEnd : (x : XMLSTCK) => XMLDocTypeValue -> F1 q XMLST
onXMLDoctypePublicPublicPublicIDStrEnd v = push1 x.xmldoctype v >> pure XMLDocTypePublicPublicIDE

onXMLDocTypePublicPublicSystemIDStrEnd : (x : XMLSTCK) => XMLDocTypeValue -> F1 q XMLST
onXMLDoctypePublicPublicSystemIDStrEnd v = push1 x.xmldoctype v >> pure XMLDocTypePublicSystemIDE

xmlDocTypeSystemURIDoubleQuoteStr : DFA q XMLSz XMLSTCK
xmlDocTypeSystemURIDoubleQuoteStr =
  dfa
    [ cclose '"' $ getStr >>= onXMLDocTypeSystemURIStrEnd . XMLDocTypeSystem
    , read xmldoctypesystemdoublequote (pushStr XMLDocTypeSystemURIStr)
    ]

xmlDocTypeSystemURISingleQuoteStr : DFA q XMLSz XMLSTCK
xmlDocTypeSystemURISingleQuoteStr =
  dfa
    [ cclose '\'' $ getStr >>= onXMLDocTypeSystemURIStrEnd . XMLDocTypeSystem
    , read xmldoctypesystemsinglequote (pushStr XMLDocTypeSystemURIStr)
    ]

xmlDocTypePublicPublicIDDoubleQuoteStr : DFA q XMLSz XMLSTCK
xmlDocTypePublicPublicIDDoubleQuoteStr =
  dfa
    [ cclose '"' $ getStr >>= onXMLDocTypePublicPublicIDStrEnd . XMLDocTypePublicPublicID
    , read xmldoctypepublicpublididdoublequote (pushStr XMLDocTypePublicPublicIDStr)
    ]

xmlDocTypePublicPublicIDSingleQuoteStr : DFA q XMLSz XMLSTCK
xmlDocTypePublicPublicIDSingleQuoteStr =
  dfa
    [ cclose '\'' $ getStr >>= onXMLDocTypePublicPublicIDStrEnd . XMLDocTypePublicPublicID
    , read xmldoctypepublicpublididsinglequote (pushStr XMLDocTypePublicPublicIDStr)
    ]

xmlDocTypePublicSystemIDDoubleQuoteStr : DFA q XMLSz XMLSTCK
xmlDocTypePublicSystemIDDoubleQuoteStr =
  dfa
    [ cclose '"' $ getStr >>= onXMLDocTypePublicSystemIDStrEnd . XMLDocTypePublicSystemID
    , read xmldoctypepublicsystemiddoublequote (pushStr XMLDocTypePublicSystemIDStr)
    ]

xmlDocTypePublicSystemIDSingleQuoteStr : DFA q XMLSz XMLSTCK
xmlDocTypePublicSystemIDSingleQuoteStr =
  dfa
    [ cclose '\'' $ getStr >>= onXMLDocTypePublicSystemIDStrEnd . XMLDocTypePublicSystemID
    , read xmldoctypepublicsystemidsinglequote (pushStr XMLDocTypePublicSystemIDStr)
    ]

--------------------------------------------------------------------------------
--          State Transitions and DFAs - post doctype whitespace
--------------------------------------------------------------------------------

onXMLPostDocTypeWhitespace : (x : XMLSTCK q) => XMLMiscValue -> F1 q XMLST
onXMLPostDocTypeWhitespace v = push1 x.xmlpostdeclmisc v >> pure XMLPostDocTypeWhitespaceE

--------------------------------------------------------------------------------
--          State Transitions and DFAs - post doctype misc
--------------------------------------------------------------------------------

onXMLPostDocTypeMiscCommentWhitespace : (x : XMLSTCK q) => XMLMiscValue -> F1 q XMLST
onXMLPostDocTypeMiscCommentWhitespace v = push1 x.xmlpostdoctypemisc v >> pure XMLPostDocTypeMiscCommentWhitespaceE

onXMLPostDocTypeMiscAfterCommentWhitespace : (x : XMLSTCK q) => XMLMiscValue -> F1 q XMLST
onXMLPostDocTypeMiscAfterCommentWhitespace v = push1 x.xmlpostdoctypemisc v >> pure XMLPostDocTypeMiscCommentWhitespaceE

onXMLPostDocTypeMiscAfterProcessingInstructionTargetWhitespace : (x : XMLSTCK q) => XMLMiscValue -> F1 q XMLST
onXMLPostDocTypeMiscAfterProcessingInstructionTargetWhitespace v = push1 x.xmlpostdoctypemisc v >> pure XMLPostDocTypeMiscAfterProcessingInstructionTargetWhitespaceE

onXMLPostDocTypeMiscAfterProcessingInstructionDataWhitespace : (x : XMLSTCK q) => XMLMiscValue -> F1 q XMLST
onXMLPostDocTypeMiscAfterProcessingInstructionDataWhitespace v = push1 x.xmlpostdoctypemisc v >> pure XMLPostDocTypeMiscAfterProcessingInstructionDataWhitespaceE

onXMLPostDocTypeMiscCommentStrEnd : (x : XMLSTCK) => XMLMiscValue -> F1 q XMLST
onXMLPostDocTypeMiscCommentStrEnd v = push1 x.xmlpostdoctypemisc v >> pure XMLPostDocTypeMiscCommentE

onXMLPostDocTypeMiscProcessingInstructionTargetStrEnd : (x : XMLSTCK) => XMLMiscValue -> F1 q XMLST
onXMLPostDocTypeMiscProcessingInstructionTargetStrEnd v = push1 x.xmlpostdoctypemisc v >> pure XMLPostDocTypeMiscProcessingInstructionTargetE

onXMLPostDocTypeMiscProcessingInstructionDataStrEnd : (x : XMLSTCK) => XMLMiscValue -> F1 q XMLST
onXMLPostDocTypeMiscProcessingInstructionDataStrEnd v = push1 x.xmlpostdoctypemisc v >> pure XMLPostDocTypeMiscProcessingInstructionDataE

xmlPostDocTypeMiscCommentStr : DFA q XMLSz XMLSTCK
xmlPostDocTypeMiscCommentStr =
  dfa
    [ conv xmlmisccomment (onXMLPostDocTypeMiscCommentStrEnd . XMLMiscComment)
    ]

xmlPostDocTypeMiscProcessingInstructionTargetStr : DFA q XMLSz XMLSTCK
xmlPostDocTypeMiscProcessingInstructionTargetStr =
  dfa
    [ conv xmlmiscprocessinginstructiontarget (onXMLPostDocTypeMiscProcessingInstructionTargetStrEnd . XMLMiscProcessingInstructionTarget)
    ]

xmlPostDocTypeMiscProcessingInstructionDataStr : DFA q XMLSz XMLSTCK
xmlPostDocTypeMiscProcessingInstructionDataStr =
  dfa
    [ conv xmlmiscprocessinginstructiondata (onXMLPostDocTypeMiscProcessingInstructionDataStrEnd . XMLMiscProcessingInstructionData)
    ]

--------------------------------------------------------------------------------
--          State Transitions and DFAs - root element
--------------------------------------------------------------------------------

onXMLElementEndTagStrEnd : (x : XMLSTCK q) => ByteString -> F1 q XMLST
onXMLElementEndTagStrEnd v =
  read1 x.xmlelementstack >>= \case
    (sv :< (a, b) :< (c, d)) =>
      case v == c of
        True  => T1.do
          write1 x.xmlelementstack (sv :< (a, b :< d)) >> pure XMLElementEndTagE
        False =>
          pure XMLMismatchedStartEndTag
    (Lin :< (a, b))          =>
      case v == a of
        True  => T1.do
          write1 x.xmlrootelement (sv :< (a, b :< d)) >> pure XMLElementEndTagE
        False =>
          pure XMLMismatchedStartEndTag
    _                        =>
      pure XMLMismatchedStartEndTag

--------------------------------------------------------------------------------
--          State Transitions and DFAs - post root element misc
--------------------------------------------------------------------------------

onXMLPostElementMiscCommentWhitespace : (x : XMLSTCK q) => XMLMiscValue -> F1 q XMLST
onXMLPostElementMiscCommentWhitespace v = push1 x.xmlpostrootmisc v >> pure XMLPostElementMiscCommentWhitespaceE

onXMLPostElementMiscAfterCommentWhitespace : (x : XMLSTCK q) => XMLMiscValue -> F1 q XMLST
onXMLPostElementMiscAfterCommentWhitespace v = push1 x.xmlpostrootmisc v >> pure XMLPostElementMiscCommentWhitespaceE

onXMLPostElementMiscAfterProcessingInstructionTargetWhitespace : (x : XMLSTCK q) => XMLMiscValue -> F1 q XMLST
onXMLPostElementMiscAfterProcessingInstructionTargetWhitespace v = push1 x.xmlpostrootmisc v >> pure XMLPostElementMiscAfterProcessingInstructionTargetWhitespaceE

onXMLPostElementMiscAfterProcessingInstructionDataWhitespace : (x : XMLSTCK q) => XMLMiscValue -> F1 q XMLST
onXMLPostElementMiscAfterProcessingInstructionDataWhitespace v = push1 x.xmlpostrootmisc v >> pure XMLPostElementMiscAfterProcessingInstructionDataWhitespaceE

onXMLPostElementMiscCommentStrEnd : (x : XMLSTCK) => XMLMiscValue -> F1 q XMLST
onXMLPostElementMiscCommentStrEnd v = push1 x.xmlpostrootmisc v >> pure XMLPostElementMiscCommentE

onXMLPostElementMiscProcessingInstructionTargetStrEnd : (x : XMLSTCK) => XMLMiscValue -> F1 q XMLST
onXMLPostElementMiscProcessingInstructionTargetStrEnd v = push1 x.xmlpostrootmisc v >> pure XMLPostElementMiscProcessingInstructionTargetE

onXMLPostElementMiscProcessingInstructionDataStrEnd : (x : XMLSTCK) => XMLMiscValue -> F1 q XMLST
onXMLPostElementMiscProcessingInstructionDataStrEnd v = push1 x.xmlpostrootmisc v >> pure XMLPostElementMiscProcessingInstructionDataE

xmlPostElementMiscCommentStr : DFA q XMLSz XMLSTCK
xmlPostElementMiscCommentStr =
  dfa
    [ conv xmlmisccomment (onXMLPostElementMiscCommentStrEnd . XMLMiscComment)
    ]

xmlPostElementMiscProcessingInstructionTargetStr : DFA q XMLSz XMLSTCK
xmlPostElementMiscProcessingInstructionTargetStr =
  dfa
    [ conv xmlmiscprocessinginstructiontarget (onXMLPostElementMiscProcessingInstructionTargetStrEnd . XMLMiscProcessingInstructionTarget)
    ]

xmlPostElementMiscProcessingInstructionDataStr : DFA q XMLSz XMLSTCK
xmlPostElementMiscProcessingInstructionDataStr =
  dfa
    [ conv xmlmiscprocessinginstructiondata (onXMLPostElementMiscProcessingInstructionDataStrEnd . XMLMiscProcessingInstructionData)
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
    , conv (str "<!DOCTYPE") (pure XMLAfterDocType)
    , conv '<' (pure XMLElementStartTagNameS)
    ]

--------------------------------------------------------------------------------
--          DFA - after declaration version
--------------------------------------------------------------------------------

xmlDeclVersionAfter : DFA q XMLSz XMLSTCK
xmlDeclVersionAfter =
  dfa
    [ conv whitespace (onXMLDeclPostVersionWhitespace . XMLDeclWhitespace)
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
    [ conv whitespace (onXMLDeclPostEncodingWhitespace . XMLDeclWhitespace)
    , read (str "standalone=") (pure XMLDeclStandaloneS)
    , read (str "?>") (pure XMLPostDeclStart)
    ]

--------------------------------------------------------------------------------
--          DFA - after declaration standalone
--------------------------------------------------------------------------------

xmlDeclStandaloneAfter : DFA q XMLSz XMLSTCK
xmlDeclStandaloneAfter =
  dfa
    [ conv whitespace (onXMLDeclPostStandaloneWhitespace . XMLDeclWhitespace)
    , read (str "?>") (pure XMLPostDeclStart)
    ]

--------------------------------------------------------------------------------
--          DFA - start of post declaration
--------------------------------------------------------------------------------

xmlPostDeclStart : DFA q XMLSz XMLSTCK
xmlPostDeclStart =
  dfa
    [ conv whitespace (onXMLPostDeclWhitespace . XMLMiscWhitespace)
    , read (str "<!--") (pure XMLPostDeclMiscCommentStrStart)
    , read (str "<?") (pure XMLPostDeclMiscProcessingInstructionTargetStrStart)
    , read (str "<!DOCTYPE") (pure XMLAfterDocType)
    , read '<' (pure XMLElementStartTagNameStrStart)
    ]

--------------------------------------------------------------------------------
--          DFA - after post declaration comment
--------------------------------------------------------------------------------

xmlPostDeclMiscCommentAfter : DFA q XMLSz XMLSTCK
xmlPostDeclMiscCommentAfter =
  dfa
    [ conv whitespace (onXMLPostDeclWhitespace . XMLMiscValue)
    , read (str "<!--") (pure XMLMiscCommentStr)
    , read (str "<?") (pure XMLMiscProcessingInstructionTargetStrStart)
    , read (str "<!DOCTYPE") (pure XMLAfterDocType)
    , read '<' (pure XMLElementStartTagNameStrStart)
    ]

--------------------------------------------------------------------------------
--          DFA - after post declaration processing instruction target
--------------------------------------------------------------------------------

xmlPostDeclMiscProcessingInstructionTargetAfter : DFA q XMLSz XMLSTCK
xmlPostDeclMiscProcessingInstructionTargetAfter =
  dfa
    [ conv whitespace (onXMLPostDeclMiscAfterProcessingInstructionTargetWhitespace . XMLMiscWhitespace)
    , conv xmlmiscprocessinginstructiondata (onXMLPostDeclProcessingInstructionDataStrEnd . XMLMiscProcessingInstructionData)
    , conv "?>" (pure XMLPostDeclMiscProcessingInstructionE)
    ]

--------------------------------------------------------------------------------
--          DFA - after post declaration processing instruction data
--------------------------------------------------------------------------------

xmlPostDeclMiscProcessingInstructionDataAfter : DFA q XMLSz XMLSTCK
xmlPostDeclMiscProcessingInstructionDataAfter =
  dfa
    [ conv whitespace (onXMLPostDeclMiscAfterProcessingInstructionWhitespace . XMLMiscWhitespace)
    , conv "?>" (pure XMLPostDeclMiscProcessingInstructionE)
    ]

--------------------------------------------------------------------------------
--          DFA - after doctype
--------------------------------------------------------------------------------

xmlAfterDocType : DFA q XMLSz XMLSTCK
xmlAfterDocType =
  dfa
    [ conv whitespace (onXMLDocTypeBeforeNameWhitespace . XMLDocTypeWhitespace)
    ]

--------------------------------------------------------------------------------
--          DFA - after doctype and at least one whitespace
--------------------------------------------------------------------------------

xmlAfterDocTypeAndWhitespace : DFA q XMLSz XMLSTCK
xmlAfterDocTypeAndWhitespace =
  dfa
    [ conv whitespace (onXMLDocTypeBeforeNameWhitespace . XMLDocTypeWhitespace)
    , conv xmldoctypename (onXMLDocTypeNameStrEnd . XMLDocTypeName)
    ]

--------------------------------------------------------------------------------
--          DFA - after doctype name
--------------------------------------------------------------------------------

xmlDocTypeNameAfter : DFA q XMLSz XMLSTCK
xmlDocTypeNameAfter =
  dfa
    [ conv whitespace (onXMLDocTypeAfterNameWhitespace . XMLDocTypeWhitespace)
    , read '>' (pure XMLDocTypeFinished)
    ]

--------------------------------------------------------------------------------
--          DFA - after doctype name and at least one whitespace
--------------------------------------------------------------------------------

xmlDocTypeNameAndWhitespaceAfter : DFA q XMLSz XMLSTCK
xmlDocTypeNameAndWhitespaceAfter =
  dfa
    [ conv whitespace (onXMLDocTypeAfterNameWhitespace . XMLDocTypeWhitespace)
    , read (str "SYSTEM") (\_ => onXMLDocTypeAfterSystem)
    , read (str "PUBLIC") (\_ => onXMLDocTypeAfterPublic)
    , read '>' (pure XMLDocTypeFinished)
    ]

--------------------------------------------------------------------------------
--          DFA - after doctype system
--------------------------------------------------------------------------------

xmlDocTypeSystemAfter : DFA q XMLSz XMLSTCK
xmlDocTypeSystemAfter =
  dfa
    [ conv whitespace (onXMLDocTypeAfterSystemWhitespace . XMLDocTypeWhitespace)
    ]

--------------------------------------------------------------------------------
--          DFA - after doctype system and at least one whitespace
--------------------------------------------------------------------------------

xmlDocTypeSystemAndWhitespaceAfter : DFA q XMLSz XMLSTCK
xmlDocTypeSystemAndWhitespaceAfter =
  dfa
    [ conv whitespace (onXMLDocTypeAfterSystemWhitespace . XMLDocTypeWhitespace)
    , copen '"' (pure XMLDocTypeSystemURIDoubleQuoteStrStart)
    , copen '\'' (pure XMLDocTypeSystemURISingleQuoteStrStart)
    ]

--------------------------------------------------------------------------------
--          DFA - after doctype system uri
--------------------------------------------------------------------------------

xmlDocTypeSystemURIAfter : DFA q XMLSz XMLSTCK
xmlDocTypeSystemURIAfter =
  dfa
    [ conv whitespace (onXMLDocTypeAfterSystemURIWhitespace . XMLDocTypeWhitespace)
    , read '>' (pure XMLDocTypeFinished)
    ]

--------------------------------------------------------------------------------
--          DFA - after doctype public
--------------------------------------------------------------------------------

xmlDocTypePublicAfter : DFA q XMLSz XMLSTCK
xmlDocTypePublicAfter =
  dfa
    [ conv whitespace (onXMLDocTypeAfterNameWhitespace . XMLDocTypeWhitespace)
    ]

--------------------------------------------------------------------------------
--          DFA - after doctype public and at least one whitespace
--------------------------------------------------------------------------------

xmlDocTypePublicAndWhitespaceAfter : DFA q XMLSz XMLSTCK
xmlDocTypePublicAndWhitespaceAfter =
  dfa
    [ conv whitespace (onXMLDocTypeAfterNameWhitespace . XMLDocTypeWhitespace)
    , copen '"' (pure XMLDocTypePublicPublicIDDoubleQuoteStrStart)
    , copen '\'' (pure XMLDocTypePublicPublicIDSingleQuoteStrStart)
    ]

--------------------------------------------------------------------------------
--          DFA - after doctype public public id
--------------------------------------------------------------------------------

xmlDocTypePublicPublicIDAfter : DFA q XMLSz XMLSTCK
xmlDocTypePublicPublicIDAfter =
  dfa
    [ conv whitespace (onXMLDocTypeAfterPublicPublicIDWhitespace . XMLDocTypeWhitespace)
    ]

--------------------------------------------------------------------------------
--          DFA - after doctype public public id and at least one whitespace
--------------------------------------------------------------------------------

xmlDocTypePublicPublicIDAndWhiteSpaceAfter : DFA q XMLSz XMLSTCK
xmlDocTypePublicPublicIDAndWhitespaceAfter =
  dfa
    [ conv whitespace (onXMLDocTypeAfterPublicPublicIDWhitespace . XMLDocTypeWhitespace)
    , copen '"' (pure XMLDocTypePublicSystemIDDoubleQuoteStrStart)
    , copen '\'' (pure XMLDocTypePublicSystemIDSingleQuoteStrStart)
    ]

--------------------------------------------------------------------------------
--          DFA - after doctype public system id
--------------------------------------------------------------------------------

xmlDocTypePublicSystemIDAfter : DFA q XMLSz XMLSTCK
xmlDocTypePublicSystemIDAfter =
  dfa
    [ conv whitespace (onXMLDocTypeAfterPublicPublicIDWhitespace . XMLDocTypeWhitespace)
    , read '>' (pure XMLDocTypeFinished)
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
    , E XMLPostDeclMiscCommentStrStart xmlPostDeclMiscCommentStr
    , E XMLPostDeclMiscProcessingInstructionTargetE xmlPostDeclMiscProcessingInstructionTargetAfter
    , E XMLPostDeclMiscProcessingInstructionDataE xmlPostDeclMiscProcessingInstructionDataAfter
    , E XMLPostDeclMiscCommentWhitespaceE xmlPostDeclStart
    , E XMLPostDeclMiscProcessingInstructionTargetStrStart xmlPostDeclMiscProcessingInstructionTargetStr
    , E XMLPostDeclMiscAfterProcessingInstructionTargetWhitespaceE xmlPostDeclMiscProcessingInstructionTargetAfter
    , E XMLPostDeclMiscAfterProcessingInstructionDataWhitespaceE xmlPostDeclMiscProcessingInstructionDataAfter
    -- XML DocType - optional
    , E XMLAfterDocType xmlAfterDocType
    , E XMLDocTypeBeforeNameWhitespaceE xmlAfterDocType
    , E XMLDocTypeNameE xmlDocTypeNameAfter
    , E XMLDocTypeAfterNameWhitespaceE xmlDocTypeNameAndWhitespaceAfter
    , E XMLDocTypeSystemE xmlDocTypeSystemAfter
    , E XMLDocTypeAfterSystemWhitespaceE xmlDocTypeSystemAndWhitespaceAfter
    , E XMLDocTypeSystemURIDoubleQuoteStrStart xmlDocTypeSystemURIDoubleQuoteStr
    , E XMLDocTypeSystemURISingleQuoteStrStart xmlDocTypeSystemURISingleQuoteStr
    , E XMLDocTypePublicE xmlDocTypePublicAfter
    , E XMLDocTypeAfterPublicWhitespaceE xmlDocTypePublicAndWhitespaceAfter
    , E XMLDocTypePublicPublicIDDoubleQuoteStrStart xmlDocTypePublicPublicIDDoubleQuoteStr
    , E XMLDocTypePublicPublicIDSingleQuoteStrStart xmlDocTypePublicPublicIDSingleQuoteStr
    , E XMLDocTypeSystemURIE xmlDocTypeSystemURIAfter
    , E XMLDocTypePublicPublicIDE xmlDocTypePublicPublicIDAfter
    , E XMLDocTypePublicPublicIDAndWhitespaceE xmlDocTypePublicPublicIDAndWhitespaceAfter
    , E XMLDocTypePublicSystemIDDoubleQuoteStrStart xmlDocTypePublicSystemIDDoubleQuoteStr
    , E XMLDocTypePublicSystemIDSingleQuoteStrStart xmlDocTypePublicSystemIDSingleQuoteStr
    , E XMLDocTypePublicSystemIDE xmlDocTypePublicSystemIDAfter
      -- After DocType - optional (comments and processing instructions)
    , E XMLPostDocTypeStart xmlPostDocTypeStart
    , E XMLPostDocTypeMiscCommentStrStart xmlPostDocTypeMiscCommentStr
    , E XMLPostDocTypeMiscProcessingInstructionTargetE xmlPostDocTypeMiscProcessingInstructionTargetAfter
    , E XMLPostDocTypeMiscProcessingInstructionDataE xmlPostDocTypeMiscProcessingInstructionDataAfter
    , E XMLPostDocTypeMiscCommentWhitespaceE xmlPostDocTypeStart
    , E XMLPostDocTypeMiscProcessingInstructionTargetStrStart xmlPostDocTypeMiscProcessingInstructionTargetStr
    , E XMLPostDocTypeMiscAfterProcessingInstructionTargetWhitespaceE xmlPostDocTypeMiscProcessingInstructionTargetAfter
    , E XMLPostDocTypeMiscAfterProcessingInstructionDataWhitespaceE xmlPostDocTypeMiscProcessingInstructionDataAfter
      -- XML root element - required
      -- After root element - optional (comments and processing instructions)
    , E XMLPostElementStart xmlPostElementStart
    , E XMLPostElementMiscCommentStrStart xmlPostElementMiscCommentStr
    , E XMLPostElementMiscProcessingInstructionTargetE xmlPostElementMiscProcessingInstructionTargetAfter
    , E XMLPostElementMiscProcessingInstructionDataE xmlPostElementMiscProcessingInstructionDataAfter
    , E XMLPostElementMiscCommentWhitespaceE xmlPostElementStart
    , E XMLPostElementMiscProcessingInstructionTargetStrStart xmlPostElementMiscProcessingInstructionTargetStr
    , E XMLPostElementMiscAfterProcessingInstructionTargetWhitespaceE xmlPostElementMiscProcessingInstructionTargetAfter
    , E XMLPostElementMiscAfterProcessingInstructionDataWhitespaceE xmlPostElementMiscProcessingInstructionDataAfter
    ]

--------------------------------------------------------------------------------
--          EOI
--------------------------------------------------------------------------------

xmlEOI : XMLST -> XMLSTCK q -> F1 q (Either (BoundedErr Void) XMLDocument)
xmlEOI st x =
  case st == XMLIni || st == XMLEmpty || isNil x.root of
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
