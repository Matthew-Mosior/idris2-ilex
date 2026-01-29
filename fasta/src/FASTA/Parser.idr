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
  NL      : FASTAValue
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
  ["FIni", "FHdr", "FD", "FNL"]

--------------------------------------------------------------------------------
--          State Transitions
--------------------------------------------------------------------------------

onFASTAValueFHdr : (x : FSTCK q) => FASTAValue -> F1 q FST
onFASTAValueFHdr v = push1 x.fastavalues v >> pure FHdr

onFASTAValueFD : (x : FSTCK q) => FASTAValue -> F1 q FST
onFASTAValueFD v = push1 x.fastavalues v >> pure FD

onNL : (x : FSTCK q) => F1 q FST
onNL = T1.do
  incline 1
  fvs@(_::_) <- getList x.fastavalues | [] => pure FIni
  ln <- read1 x.line
  push1 x.fastalines (MkFASTALine ln fvs)
  pure FIni

fastaDflt : DFA q FSz FSTCK
fastaDflt =
  dfa
    [ conv linebreak (\_ => onNL)
    , read ('>' >> plus (dot && not linebreak)) (onFASTAValueFHdr . FHeader)
    , read (plus (nucleotide && not linebreak)) (onFASTAValueFD . FData)
    ]

fastaSteps : Lex1 q FSz FSTCK
fastaSteps =
  lex1
    [ E FIni fastaDflt
    , E FHdr fastaDflt
    , E FD fastaDflt
    ]

fastaErr : Arr32 FSz (FSTCK q -> F1 q (BoundedErr Void))
fastaErr =
  arr32 FSz (unexpected [])
    [ E FNL $ unclosed "\""
    , E FHdr $ unexpected ["no sequence line(s)"]
    , E FD $ unexpected ["^[ATGC]"]
    ]

fastaEOI : FST -> FSTCK q -> F1 q (Either (BoundedErr Void) FASTA)
fastaEOI st x =
  case st == FHdr of
    True  => arrFail FSTCK fastaErr st x
    False => T1.do
      _     <- onNL
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
