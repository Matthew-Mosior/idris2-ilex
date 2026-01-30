module FASTA.Parser

import Data.Bits
import Data.Buffer
import Data.ByteString
import Data.Linear.Ref1
import Derive.Prelude
import Syntax.T1
import Text.ILex.Derive

import public Text.ILex

%default total
%language ElabReflection

--------------------------------------------------------------------------------
--          FASTAValue
--------------------------------------------------------------------------------

public export
data FASTAValue : Type where
  NL      : FASTAValue
  FHeader : String -> FASTAValue
  FData   : String -> FASTAValue

%runElab derive "FASTAValue" [Show,Eq]

isFHeader : FASTAValue -> Bool
isFHeader (FHeader _) = True
isFHeader _           = False

isFData : FASTAValue -> Bool
isFData (FData _) = True
isFData _         = False

--------------------------------------------------------------------------------
--          FASTALine
--------------------------------------------------------------------------------

public export
record FASTALine where
  constructor MkFASTALine
  nr     : Nat
  values : List FASTAValue

%runElab derive "FASTALine" [Show,Eq]

Interpolation FASTALine where interpolate = show

--------------------------------------------------------------------------------
--          FASTA
--------------------------------------------------------------------------------

public export
0 FASTA : Type
FASTA = List FASTALine

--------------------------------------------------------------------------------
--          RExp
--------------------------------------------------------------------------------

linebreak : RExp True
linebreak = '\n' <|> '\r' <|> "\r\n"

nucleotide : RExp True
nucleotide = 'A' <|> 'T' <|> 'G' <|> 'C'

--------------------------------------------------------------------------------
--          Parser State
--------------------------------------------------------------------------------

public export
record FSTCK (q : Type) where
  constructor F
  line        : Ref q Nat
  col         : Ref q Nat
  psns        : Ref q (SnocList Position)
  strs        : Ref q (SnocList String)
  err         : Ref q (Maybe $ BoundedErr Void)
  fastavalues : Ref q (SnocList FASTAValue)
  fastalines  : Ref q (SnocList FASTALine)
  bytes       : Ref q ByteString

export %inline
HasPosition FSTCK where
  line      = FSTCK.line
  col       = FSTCK.col
  positions = FSTCK.psns

export %inline
HasError FSTCK Void where
  error = err

export %inline
HasStringLits FSTCK where
  strings = strs

export %inline
HasStack FSTCK (SnocList FASTALine) where
  stack = fastalines

export %inline
HasBytes FSTCK where
  bytes = FSTCK.bytes

export
fastainit : F1 q (FSTCK q)
fastainit = T1.do
  l  <- ref1 Z
  c  <- ref1 Z
  bs <- ref1 [<]
  ss <- ref1 [<]
  er <- ref1 Nothing
  fvs <- ref1 [<]
  fls <- ref1 [<]
  by <- ref1 ""
  pure (F l c bs ss er fvs fls by)

--------------------------------------------------------------------------------
--          Parser State
--------------------------------------------------------------------------------

%runElab deriveParserState "FSz" "FST"
  ["FIni", "FBroken", "FHdr", "FNoHdr", "FHdrAfterD", "FHdrAE", "FHdrMissingNL", "FHdrToNL", "FHdrDone", "FD", "FDNL", "FEmpty", "FComplete"]

--------------------------------------------------------------------------------
--          Errors
--------------------------------------------------------------------------------

fastaErr : Arr32 FSz (FSTCK q -> F1 q (BoundedErr Void))
fastaErr =
  arr32 FSz (unexpected [])
    [ E FBroken $ unexpected ["incorrect format"]
    , E FNoHdr $ unexpected ["no header line"]
    , E FHdrAfterD $ unexpected ["header line found after sequence line"]
    , E FHdrAE $ unexpected ["header line already encountered"]
    , E FHdrMissingNL $ unexpected ["newline at end of header line missing"]
    , E FEmpty $ unexpected ["empty line"]
    , E FHdr $ unexpected ["no sequence line(s)"]
    ]

--------------------------------------------------------------------------------
--          State Transitions
--------------------------------------------------------------------------------

onFASTAValueFHdr : (x : FSTCK q) => FASTAValue -> F1 q FST
onFASTAValueFHdr v = push1 x.fastavalues v >> pure FHdr

onFASTAValueFD : (x : FSTCK q) => FASTAValue -> F1 q FST
onFASTAValueFD v = push1 x.fastavalues v >> pure FD

onNLFHdr : (x : FSTCK q) => F1 q FST
onNLFHdr = T1.do
  fvs@(_::_) <- getList x.fastavalues | [] => pure FEmpty
  case Prelude.any isFHeader fvs && Prelude.any isFData fvs of
    True  => pure FBroken
    False => T1.do
      incline 1
      ln <- read1 x.line
      push1 x.fastalines (MkFASTALine ln fvs)
      pure FHdrDone

onNLFD : (x : FSTCK q) => F1 q FST
onNLFD = T1.do
  fvs@(_::_) <- getList x.fastavalues | [] => pure FEmpty
  case Prelude.any isFHeader fvs && Prelude.any isFData fvs of
    True  => pure FBroken
    False => T1.do
      incline 1
      ln <- read1 x.line
      push1 x.fastalines (MkFASTALine ln fvs)
      pure FDNL

onEOI : (x : FSTCK q) => F1 q (Either (BoundedErr Void) FST)
onEOI = T1.do
  fvs@(_::_) <- getList x.fastavalues
    | [] => arrFail FSTCK fastaErr FEmpty x
  fls@(_::_) <- getList x.fastalines
    | [] => arrFail FSTCK fastaErr FEmpty x
  incline 1
  ln <- read1 x.line
  push1 x.fastalines (MkFASTALine ln fvs)
  pure (Right FComplete)

fastaInit : DFA q FSz FSTCK
fastaInit =
  dfa
    [ conv linebreak (const $ pure FNoHdr)
    , copen '>' (pure FHdrToNL)
    , read (plus nucleotide) (const $ pure FNoHdr)
    ]

fastaHdrStr : DFA q FSz FSTCK
fastaHdrStr =
  dfa
    [ read dot (onFASTAValueFHdr . FHeader)
    , conv linebreak (\_ => onNLFHdr)
    ]

fastaFDInit : DFA q FSz FSTCK
fastaFDInit =
  dfa
    [ conv linebreak (const $ pure FEmpty)
    , read '>' (const $ pure FHdrAE)
    , read nucleotide (onFASTAValueFD . FData)
    ]

fastaFD : DFA q FSz FSTCK
fastaFD =
  dfa
    [ conv linebreak (\_ => onNLFD)
    , read nucleotide (onFASTAValueFD . FData)
    ]

fastaSteps : Lex1 q FSz FSTCK
fastaSteps =
  lex1
    [ E FIni fastaInit
    , E FHdrToNL fastaHdrStr
    , E FHdrDone fastaFDInit
    , E FD fastaFD
    , E FDNL fastaFDInit
    ]

fastaEOI : FST -> FSTCK q -> F1 q (Either (BoundedErr Void) FASTA)
fastaEOI st x =
  case st == FIni of
    True => T1.do
      (P l c) <- getPosition
      case c of
        Z => arrFail FSTCK fastaErr FEmpty x
        _ => arrFail FSTCK fastaErr FBroken x
    False => T1.do
      case st == FHdr || st == FEmpty of
        True  => arrFail FSTCK fastaErr st x
        False => T1.do
          _     <- onEOI
          fasta <- getList x.fastalines
          pure (Right fasta)

--------------------------------------------------------------------------------
--          Parser
--------------------------------------------------------------------------------

export
fasta : P1 q (BoundedErr Void) FSz FSTCK FASTA
fasta = P FIni fastainit fastaSteps snocChunk fastaErr fastaEOI

export %inline
parseFASTA : Origin -> String -> Either (ParseError Void) FASTA
parseFASTA = parseString fasta
