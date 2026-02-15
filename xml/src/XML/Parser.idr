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
xmlmisccomment = plus $ dot && not (str "--")

xmlmiscprocessinginstructiontarget : RExp True
xmlmiscprocessinginstructiontarget = plus $ alpha && not '_' && not ':'

xmlmiscprocessinginstructiondata : RExp True
xmlmiscprocessinginstructiondata = plus $ '<' <|> '>' <|> '&' <|> '"' <|> '\n' <|> range32 0x20 0x10ffff

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
xmldeclverion = '1' >> '.' >> plus dot

xmldeclversion : RExp True
xmldeclverion = '1' >> '.' >> dot

xmldeclencoding : RExp True
xmldeclencoding = plus dot

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
  [ "XMLIni"
  , "XMLEmpty"
  , "XMLComplete"
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
  , "XMLFinished"
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
--          State Transitions (newlines/whitespace and strings)
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

--------------------------------------------------------------------------------
--          State Transition (EOI)
--------------------------------------------------------------------------------

onEOI : (x : FSTCK q) => F1 q (Either (BoundedErr Void) FST)
onEOI = T1.do
  incline 1
  xmlvs@(_::_) <- getList x.xmlvalues
    | [] => arrFail XMLSTCK xmlErr XMLEmpty x
  ln <- read1 x.line
  push1 x.xmldoc (MkXMLValues ln xmlvs)
  pure (Right XMLComplete)

--------------------------------------------------------------------------------
--          State Transitions (Strings/ByteStrings)
--------------------------------------------------------------------------------

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

xmlPostDeclMiscCommentStr : DFA q XMLSz XMLSTCK
xmlPostDeclMiscCommentStr =
  dfa
    [ conv linebreak (\bs => onXMLPostDeclMiscCommentNL bs)
    , conv whitespace (\bs => onXMLPostDeclMiscCommentWhitespace bs)
    , conv (plus $ dot && not "--") (pushStr XMLDeclStandaloneStr)
    ]

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
--          State Transitions (Non Strings/ByteStrings)
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

xmlDeclVersionAfter : DFA q XMLSz XMLSTCK
xmlDeclVersionAfter =
  dfa
    [ conv linebreak (\bs => onXMLDeclPostVersionNL bs)
    , conv whitespace (\bs => onXMLDeclPostVersionWhitespace bs)
    , read (str "encoding=") (pure XMLDeclEncodingS)
    , read (str "standalone=") (pure XMLDeclStandaloneS)
    , read (str "?>") (pure XMLPostDeclStart)
    ]

xmlDeclEncodingAfter : DFA q XMLSz XMLSTCK
xmlDeclEncodingAfter =
  dfa
    [ conv linebreak (\bs => onXMLDeclPostEncodingNL bs)
    , conv whitespace (\bs => onXMLDeclPostEncodingWhitespace bs)
    , read (str "standalone=") (pure XMLDeclStandaloneS)
    , read (str "?>") (pure XMLPostDeclStart)
    ]

xmlDeclStandaloneAfter : DFA q XMLSz XMLSTCK
xmlDeclStandaloneAfter =
  dfa
    [ conv linebreak (\bs => onXMLDeclPostStandaloneNL bs)
    , conv whitespace (\bs => onXMLDeclPostStandaloneWhitespace bs)
    , read (str "?>") (pure XMLPostDeclStart)
    ]

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

xmlPostDeclMiscProcessingInstructionTargetAfter : DFA q XMLSz XMLSTCK
xmlPostDeclMiscProcessingInstructionTargetAfter =
  dfa
    [ conv linebreak (\bs => onXMLPostDeclNL bs)
    , conv whitespace (\bs => onXMLPostDeclWhitespace bs)
    , conv (plus $ dot && not linebreak && not whitespace && not "?>") (onXMLPostDeclProcessingInstructionDataStrEnd . XMLMiscProcessingInstructionData)
    , conv "?>" (pure XMLPostDeclMiscProcessingInstructionE)
    ]

xmlPostDeclMiscProcessingInstructionDataAfter : DFA q XMLSz XMLSTCK
xmlPostDeclMiscProcessingInstructionDataAfter =
  dfa
    [ conv linebreak (\bs => onXMLDocTypeBeforePublicPublicIDNL bs)
    , conv whitespace (\bs => onXMLDocTypeBeforePublicPublicIDWhitespace bs)
    , conv "?>" (pure XMLPostDeclMiscProcessingInstructionE)
    ]

xmlDocTypeNameAfter : DFA q XMLSz XMLSTCK
xmlDocTypeNameAfter =
  dfa
    [ conv linebreak (\bs => onXMLDocTypeAfterNameNL bs)
    , conv whitespace (\bs => onXMLDocTypeAfterNameWhitespace bs)
    , read '>' (pure XMLDocTypeFinished)
    ]

xmlDocTypeSystemURIAfter : DFA q XMLSz XMLSTCK
xmlDocTypeSystemURIAfter =
  dfa
    [ conv linebreak (\bs => onXMLDocTypeAfterSystemURINL bs)
    , conv whitespace (\bs => onXMLDocTypeAfterSystemURIWhitespace bs)
    , read '>' (pure XMLDocTypeFinished)
    ]

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
