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
--          XMLPostDeclWhitespaceValue
--------------------------------------------------------------------------------

public export
data XMLPostDeclWhitespaceValue : Type where
  XMLPostDeclWhitespace : ByteString -> XMPostDeclWhitespaceValue

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

xmldoctypesystem : RExp True
xmldoctypesystem = star $ dot && not '"' && not forbidden

xmldoctypepublicpublicid : RExp True
xmldoctypepublicpublicid = star $ pubidchar

xmldoctypepublicsystemid : RExp True
xmldoctypepublicsystemid = star $ dot && not '"' && not forbidden

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
  decl               : Maybe (List XMLDeclValue)
  postdeclwhitespace : Maybe (List XMLPostDeclWhitespaceValue)
  postdeclmisc       : Maybe (List XMLMiscValue)
  doctype            : Maybe (List XMLDocTypeValue)
  postdoctypemisc    : Maybe (List XMLMiscValue)
  root               : List XMLElementValue
  postrootmisc       : Maybe (List XMLMiscValue)

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
  xmlpostdeclwhitespace : Ref q (SnocList XMLPostDeclWhitespaceValue)
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
  , "XMLDeclEncodingPostUnfinished"
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
  , "XMLDocTypeBeforeNameWhitespaceE"
  , "XMLDocTypeAfterNameWhitespaceE"
  , "XMLDocTypeAfterSystemURIWhitespaceE"
  , "XMLDocTypeAfterPublicPublicIDWhitespaceE"
  , "XMLDocTypeAfterPublicSystemIDWhitespaceE"
  -- post doctype misc parser states
  , "XMLPostDocTypeMiscCommentWhitespaceE"
  , "XMLPostDocTypeMiscCommentStrStart"
  , "XMLPostDocTypeMiscCommentStr"
  , "XMLPostDocTypelMiscCommentE"
  , "XMLPostDocTypeMiscAfterProcessingInstructionTargetWhitespaceE"
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
    [ E XMLBroken $ unexpected ["character other than '>'"]
    , E XMLEmpty $ unexpected ["sequence data"]
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
onXMLPostDeclMiscCommentStrEnd v = push1 x.xmlpostdeclmisc v >> pure XMLDeclMiscCommentE

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

onXMLPostDeclWhitespace : (x : XMLSTCK q) => XMLPostDeclWhitespaceValue -> F1 q XMLST
onXMLPostDeclWhitespace v = push1 x.xmlpostdeclwhitespace v >> pure XMLPostDeclWhitespaceE

--------------------------------------------------------------------------------
--          State Transitions and DFAs - documentation type declaration
--------------------------------------------------------------------------------

onXMLDocTypeBeforeNameWhitespace : (x : XMLSTCK q) => XMLDocTypeValue -> F1 q XMLST
onXMLDoctypeBeforeNameWhitespace v = push1 x.xmldoctype v >> pure XMLDocTypeBeforeNameWhitespaceE

onXMLDocTypeAfterNameWhitespace : (x : XMLSTCK q) => XMLDocTypeValue -> F1 q XMLST
onXMLDoctypeAfterNameWhitespace v = push1 x.xmldoctype v >> pure XMLDocTypeAfterNameWhitespaceE

onXMLDocTypeAfterSystemURIWhitespace : (x : XMLSTCK q) => XMLDocTypeValue -> F1 q XMLST
onXMLDoctypeAfterSystemURIWhitespace v = push1 x.xmldoctype v >> pure XMLDocTypeAfterSystemURIWhitespaceE

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

xmlDocTypeNameStr : DFA q XMLSz XMLSTCK
xmlDocTypeNameStr =
  dfa
    [ conv xmldoctypename (onXMLDocTypeNameStrEnd . XMLDocTypeName)
    ]

xmlDocTypeSystemURIStr : DFA q XMLSz XMLSTCK
xmlDocTypeSystemURIStr =
  dfa
    [ conv xmldoctypesystem (onXMLDocTypeSystemURIStrEnd . XMLDocTypeSystem)
    ]

xmlDocTypePublicPublicIDStr : DFA q XMLSz XMLSTCK
xmlDocTypePublicPublicIDStr =
  dfa
    [ conv xmldoctypepublicpublicid (onXMLDocTypePublicPublicIDStrEnd . XMLDocTypePublicPublicID)
    ]

xmlDocTypePublicSystemIDStr : DFA q XMLSz XMLSTCK
xmlDocTypePublicSystemIDStr =
  dfa
    [ conv xmldoctypepublicsystemid (onXMLDocTypePublicSystemIDStrEnd . XMLDocTypePublicSystemID)
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
    [ conv whitespace (onXMLPostDeclWhitespace . XMLPostDeclWhitespace)
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
    [ conv whitespace (onXMLPostDeclWhitespace . XMLPostDeclWhitespace)
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
--          DFA - after doctype name
--------------------------------------------------------------------------------

xmlDocTypeNameAfter : DFA q XMLSz XMLSTCK
xmlDocTypeNameAfter =
  dfa
    [ conv whitespace (onXMLDocTypeAfterNameWhitespace . XMLDocTypeWhitespace)
    , read '>' (pure XMLDocTypeFinished)
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
--          DFA - after doctype public public id
--------------------------------------------------------------------------------

xmlDocTypePublicPublicIDAfter : DFA q XMLSz XMLSTCK
xmlDocTypePublicPublicIDAfter =
  dfa
    [ conv whitespace (onXMLDocTypeAfterPublicPublicIDWhitespace . XMLDocTypeWhitespace)
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
