import Averroes.Lexer
open Averroes.Lexer

namespace Averroes.Diagnostics


inductive DiagnosticCode where
| MissingListClosing
| MissingListOpening
| UnrecognizedToken
| NoProgress
| InvalidState
| EmptyProgram

structure Diagnostic where
  Create ::
  Message : String
  Code : DiagnosticCode
  Location : SourceLocation

private def FormatLocation (location: SourceLocation) := s!"({location.Start.Line},{location.Start.Column})"

def MissingListClosingError (location: SourceLocation) :=
  Diagnostic.Create s!"Missing list closing ')' at {FormatLocation location}" DiagnosticCode.MissingListClosing location

def MissingListOpeningError (location: SourceLocation) :=
  Diagnostic.Create s!"Missing list opening '(' at {FormatLocation location}" DiagnosticCode.MissingListOpening location

def UnrecognizedTokenError (token: Token) (location: SourceLocation) :=
  Diagnostic.Create s!"Unrecognized token '{token.Text}' at {FormatLocation location}" DiagnosticCode.UnrecognizedToken location

def EmptyProgramError := Diagnostic.Create "Program cannot be empty." DiagnosticCode.EmptyProgram {Start := {Line := 0, Column := 0}, End := {Line := 0, Column := 0}}

def ParsingInvalidStateError (location: SourceLocation) :=
  Diagnostic.Create s!"Parsing an inavlid state at {FormatLocation location}" DiagnosticCode.InvalidState location

def ProgressError (location: Option SourceLocation) :=
  match location with
  | none => Diagnostic.Create s!"[FATAL] Parser stopped making progress" DiagnosticCode.NoProgress {Start := {Line := 0, Column := 0}, End := {Line := 0, Column := 0}}
  | some loc => Diagnostic.Create s!"Parser stopped making progress at {FormatLocation loc}" DiagnosticCode.NoProgress loc
