module FASTA.Parser

import Data.Bits
import Data.Buffer
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
  FHeader : String -> FASTAValue
  FData   : String -> FASTAValue

%runElab derive "FASTAValue" [Show,Eq]

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
linebreak = '\n' <|> '\r'

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

%runElab deriveParserState "FSz" "FST"
  ["FIni", "FBroken", "FHdr", "FNoHdr", "FD", "FNoD", "FEmpty", "FDone"]

--------------------------------------------------------------------------------
--          Errors
--------------------------------------------------------------------------------

fastaErr : Arr32 FSz (FSTCK q -> F1 q (BoundedErr Void))
fastaErr =
  arr32 FSz (unexpected [])
    [ E FBroken $ unexpected ["incorrect format"]
    , E FNoD $ unexpected ["empty sequence line"]
    , E FNoHdr $ unexpected ["no header line"]
    , E FEmpty $ unexpected ["no data"]
    , E FHdr $ unexpected ["no sequence line(s)"]
    ]

--------------------------------------------------------------------------------
--          State Transitions
--------------------------------------------------------------------------------

onFASTAValueFHdr : (x : FSTCK q) => FASTAValue -> FST -> F1 q (Either (BoundedErr Void) FST)
onFASTAValueFHdr v st =
  case st == FD of
    True  => arrFail FSTCK fastaErr FNoHdr x
    False => T1.do
      push1 x.fastavalues v
      pure (Right FHdr)

onFASTAValueFD : (x : FSTCK q) => FASTAValue -> F1 q FST
onFASTAValueFD v = push1 x.fastavalues v >> pure FD

onNL : (x : FSTCK q) => FST -> F1 q (Either (BoundedErr Void) FST)
onNL st = T1.do
  incline 1
  fvs@(_::_) <- getList x.fastavalues | [] => arrFail FSTCK fastaErr FEmpty x
  case Prelude.any isFHeader fvs && Prelude.any isFData fvs of
    True  => arrFail FSTCK fastaErr FBroken x
    False => T1.do
      ln <- read1 x.line
      push1 x.fastalines (MkFASTALine ln fvs)
      pure (Right st)
  where
    isFHeader : FASTAValue -> Bool
    isFHeader (FHeader _) = True
    isFHeader _           = False
    isFData : FASTAValue -> Bool
    isFData (FData _) = True
    isFData _         = False

onEOI : (x : FSTCK q) => F1 q (Either (BoundedErr Void) FST)
onEOI = T1.do
  incline 1
  fvs@(_::_) <- getList x.fastavalues
    | [] => arrFail FSTCK fastaErr FEmpty x
  fls@(_::_) <- getList x.fastalines
    | [] => arrFail FSTCK fastaErr FEmpty x
  ln <- read1 x.line
  push1 x.fastalines (MkFASTALine ln fvs)
  pure (Right FDone)

fastaDflt : FST -> DFA q FSz FSTCK
fastaDflt st =
  dfa
    [ conv linebreak (\_ => onNL st)
    , read ('>' >> plus (not linebreak)) (\fv => onFASTAValueFHdr (FHeader fv) st)
    , read (plus nucleotide) (onFASTAValueFD . FData)
    ]

fastaSteps : Lex1 q FSz FSTCK
fastaSteps =
  lex1
    [ E FIni (fastaDflt FIni)
    , E FHdr (fastaDflt FHdr)
    , E FD (fastaDflt FD)
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
