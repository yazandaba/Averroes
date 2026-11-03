import Averroes.Diagnostics
import Averroes.Lexer
open Averroes.Lexer
open Averroes.Diagnostics

namespace Averroes.Parser

inductive LispLeafAtomKind where
| Identifier
| Operator
| String
| Number
| Invalid
deriving BEq, Repr


mutual

structure LispLeafAtomSyntax where
  Create ::
  private Atom : Token
  Value : String := Atom.Text
  Location : SourceLocation := Atom.Location
  Fragments : List LispFragmentSyntax := []

structure LispListSyntax where
  Create ::
  private Start : Token
  private End : Token
  Location : SourceLocation := Start.Location
  Span : SourceLocation × SourceLocation := ⟨ Start.Location,End.Location ⟩
  Diagnostic : Option Diagnostic := none
  Fragments : List LispFragmentSyntax := []
  Atoms : List LispAtomSyntax

structure LispFragmentSyntax where
  Create ::
  private Fragment : Token
  Location : SourceLocation := Fragment.Location

structure LispSentinelSyntax where
  Create ::
  SentinelToken : Token
  Fragments : List LispFragmentSyntax := []
  Diagnostic : Option Diagnostic := none

structure LispErrorSyntax where
  Create ::
  Diagnostic : Diagnostic

inductive LispAtomSyntax where
| Leaf  : LispLeafAtomSyntax -> LispAtomSyntax
| List  : LispListSyntax -> LispAtomSyntax
| Sent  : LispSentinelSyntax -> LispAtomSyntax
| Error : LispErrorSyntax -> LispAtomSyntax

inductive LispUnitSyntax where
| Unit : (List LispAtomSyntax) -> LispUnitSyntax

end

def ParseAtoms (tokens: List Token): List LispAtomSyntax × List Token:=
  match tokens with
  | [] => ([],[])
  | currentToken :: rest =>
    match currentToken.Kind with
    | .LeftParnthesis =>
      let (atoms,rem) := ParseAtoms rest
      match atoms with
      | [] => ([.List { Start := currentToken, End := currentToken, Diagnostic := MissingListClosingError currentToken.Location, Atoms := [] }],rem)
      | head::tail =>
        match (head :: tail).getLast (by simp) with
        | .Sent sent =>
          let len := rest.length - rem.length -- number of tokens consumed
          -- we do rest.drop len instead of just simply passing rem (i.e. ParseAtoms rem)
          -- because it simplifies termination by significantly
          let (sibling,siblingRem) := ParseAtoms (rest.drop len)
          (.List {Start := currentToken, End := sent.SentinelToken, Atoms := atoms} :: sibling, siblingRem)

        | .Leaf _| .List _| .Error _ =>
          let len := rest.length - rem.length -- number of tokens consumed
          let (sibling,siblingRem) := ParseAtoms (rest.drop len)
          (.List { Start := currentToken, End := currentToken, Diagnostic := MissingListClosingError currentToken.Location, Atoms := atoms }:: sibling,
           siblingRem)


    | .RightParenthesis =>
      ([.Sent {SentinelToken := currentToken}],rest)

    | .Identifier | .String | .Number | .Operator =>
      let (atoms,atomsRem) := ParseAtoms rest
      (.Leaf { Atom := currentToken } :: atoms, atomsRem)

    | .Fragment =>
      let (atoms,atomsRem) := ParseAtoms rest
      match atoms with
      | [] => ([.Error {Diagnostic := ParsingInvalidStateError currentToken.Location}],atomsRem)
      | target :: restAtoms =>
        match target with
        | .Leaf atom => (.Leaf {atom with Fragments := {Fragment := currentToken} :: atom.Fragments} :: restAtoms, atomsRem)
        | .List list => (.List {list with Fragments := {Fragment := currentToken} :: list.Fragments} :: restAtoms, atomsRem)
        | .Sent sent => (.Sent {sent with Fragments := {Fragment := currentToken} :: sent.Fragments} :: restAtoms, atomsRem)
        | .Error err => (atoms,atomsRem)

    | .Eof => ([.Leaf { Atom := currentToken }],[])

    | .Invalid =>
      let (atoms,atomsRem) := ParseAtoms rest
      (.Error {Diagnostic := UnrecognizedTokenError currentToken currentToken.Location} :: atoms, atomsRem)

termination_by tokens.length
decreasing_by all_goals simp_all <;> omega

-- every non-empty input consumes at least one token
theorem ParseAtomsConsumes (tokens : List Token) :
    (ParseAtoms tokens).2.length ≤ tokens.length - 1 := by
  fun_induction ParseAtoms tokens <;> simp_all <;> omega

def ParseTop : (List Token) -> List LispAtomSyntax
| [] => [.Error {Diagnostic := EmptyProgramError}]
| tok :: rest =>
  match _h : ParseAtoms (tok :: rest) with
  | (program, rem) =>
    -- ParseAtoms only ever yields a sentinel as its last atom: a stray ')' at top level,
    -- flag it and resume parsing after it
    match program.getLast? with
    | none => [.Error {Diagnostic := EmptyProgramError}]
    | some (.Sent sent) =>
      let stray := .Sent {sent with Diagnostic := MissingListOpeningError sent.SentinelToken.Location}
      program.dropLast ++ stray :: ParseTop rem
    | some _ => program

termination_by tokens => tokens.length
decreasing_by
  have := ParseAtomsConsumes (tok :: rest)
  simp_all; omega

def ParseUnit (tokens: List Token) : LispUnitSyntax := LispUnitSyntax.Unit (ParseTop tokens)

def Parse (text: String) : LispUnitSyntax := ParseUnit (Lex text.toList 0 0)
