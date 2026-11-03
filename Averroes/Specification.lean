import Averroes.Lexer
open Averroes.Lexer

namespace Averroes.Specification


-- True when the text contains a '"' that is not escaped by a '\'.
def HasClosingQuote : (List Char) -> Bool
| [] => false
| '"' :: _ => true
| '\\' :: _ :: tail => HasClosingQuote tail
| _ :: tail => HasClosingQuote tail

def lexStringSpecification : (List Char) -> Nat -> Nat -> Token
| [], line, column =>
        Token.Create TokenKind.Invalid
          (SourceLocation.Create (SourcePosition.Create line column) (SourcePosition.Create line column))
          "[FATAL] INVALID EMPTY STRING LEXEM"
| _ :: rest, line, column =>
        if HasClosingQuote rest then
          let content := ScanString rest
          let literal := s!"\"{String.ofList content}\""
          Token.Create TokenKind.String
            (SourceLocation.Create (SourcePosition.Create line column) (SourcePosition.Create line (column + literal.length)))
            literal
        else
          Token.Create TokenKind.Invalid
            (SourceLocation.Create (SourcePosition.Create line column) (SourcePosition.Create line (column + (rest.length + 1))))
            "unterminated string"


def intScanSpecification : (List Char) -> List Char
| [] => []
| head :: tail => if head.isDigit then head :: intScanSpecification tail else []

def lexNumberSpecification : (List Char) -> Nat -> Nat -> Token
| [] , line, column => Token.Create TokenKind.Invalid (SourceLocation.Create (SourcePosition.Create line column) (SourcePosition.Create line column)) "[FATAL] INVALID EMPTY NUMBER LEXEM"
| fnum :: rest, line, column =>
  let intPart := intScanSpecification (fnum::rest)
  let optDot := (fnum::rest).drop intPart.length
  if optDot[0]? == some '.' then
    let mantissaPart := optDot.drop 1
    let mantissa := intScanSpecification mantissaPart
    if mantissa == [] then
      Token.Create TokenKind.Invalid (SourceLocation.Create (SourcePosition.Create line column) (SourcePosition.Create line (column + (String.ofList intPart ++ ".").length))) s!"malformed floating point literal '{String.ofList intPart}.'"
    else
      let float := (String.ofList intPart) ++ "." ++ (String.ofList mantissa)
      Token.Create TokenKind.Number (SourceLocation.Create (SourcePosition.Create line column) (SourcePosition.Create line (column + float.length))) float
  else
    Token.Create TokenKind.Number (SourceLocation.Create (SourcePosition.Create line column) (SourcePosition.Create line (column + intPart.length))) (String.ofList intPart)

def identifierScanSpecification : (List Char) -> (List Char)
| [] => []
| head :: tail => if head.isAlphanum then head :: identifierScanSpecification tail else []

def lexIdentifierSpecification : (List Char) -> Nat -> Nat -> Token
| [] , line, column => Token.Create TokenKind.Invalid (SourceLocation.Create (SourcePosition.Create line column) (SourcePosition.Create line column)) "[FATAL] INVALID EMPTY IDENTEFIER LEXEM"
| head :: tail, line, column =>
  let id := head::identifierScanSpecification (tail)
  Token.Create TokenKind.Identifier (SourceLocation.Create (SourcePosition.Create line column) (SourcePosition.Create line (column + id.length))) (String.ofList id)


def FragmentsLocation: (List Char) -> Nat -> Nat -> Nat × Nat
| '\r' :: '\n' :: rest , line, _ => FragmentsLocation rest (line + 1) 0
| '\n' :: rest, line, _ => FragmentsLocation rest (line + 1) 0
| ' '  :: rest, line, column => FragmentsLocation rest line (column + 1)
| '\t' :: rest, line, column => FragmentsLocation rest line (column + 1)
| _, line, column => ⟨line, column⟩

/-- The leading fragment: spaces, tabs, LF, and CRLF. A lone CR stops scanning. -/
def FragmentsText : List Char -> List Char
| '\r' :: '\n' :: rest => '\r' :: '\n' :: FragmentsText rest
| '\n' :: rest => '\n' :: FragmentsText rest
| ' ' :: rest => ' ' :: FragmentsText rest
| '\t' :: rest => '\t' :: FragmentsText rest
| _ => []

def lexFragmentsCoreSpecification (text : List Char) (line column : Nat) : Token :=
  let fragment := FragmentsText text
  let (l,c) := FragmentsLocation text line column
  Token.Create TokenKind.Fragment (SourceLocation.Create (SourcePosition.Create l c) (SourcePosition.Create l c)) (String.ofList fragment)

def lexFragmentsSpecification : (List Char) -> Nat -> Nat ->  SourceLocation × Token
| [], line, column =>
  let tok := lexFragmentsCoreSpecification [] line column
  (tok.Location,tok)
| text, line, column =>
  let tok := lexFragmentsCoreSpecification text line column
  let resultTok := { tok with Location.Start := SourcePosition.Create line column }
  (tok.Location, resultTok)

def lexCommentScanSpecification : (List Char) -> List Char
| [] => []
| ch :: tail => if ch != '\n' then ch :: lexCommentScanSpecification tail else []

def lexCommentSpecification : (List Char) -> Nat -> Nat -> Token
| ';' :: tail, line, column =>
  let comment := ';' :: (lexCommentScanSpecification tail)
  Token.Create TokenKind.Fragment (SourceLocation.Create (SourcePosition.Create line column) (SourcePosition.Create line (column + comment.length))) (String.ofList comment)
|  _ , line, column => Token.Create TokenKind.Invalid (SourceLocation.Create (SourcePosition.Create line column) (SourcePosition.Create line column)) "[FATAL] INVALID COMMENT LEXEM"


def lexSpecification : (List Char) -> Nat -> Nat -> (List Token)
| [], line, column => [Token.Create TokenKind.Eof (SourceLocation.Create (SourcePosition.Create line column) (SourcePosition.Create line (column + 1))) "\x00"]
| '(' :: rest, line, column =>
      { Kind := TokenKind.LeftParnthesis
        Location := SourceLocation.Create (SourcePosition.Create line column) (SourcePosition.Create line (column + 1))
        Text := "("
      } :: lexSpecification rest line (column + 1)

| ')' :: rest, line, column =>
       {
        Kind := TokenKind.RightParenthesis
        Location := SourceLocation.Create (SourcePosition.Create line column) (SourcePosition.Create line (column + 1))
        Text := ")"
      } :: lexSpecification rest line (column + 1)

| head :: tail , line, column =>
  if head.isWhitespace then
    let (location,fragment) := lexFragmentsSpecification (head::tail) line column
    let ⟨skippedLines,lastColumn⟩ := location.End
    fragment :: lexSpecification (tail.drop (fragment.Text.length - 1)) skippedLines lastColumn

  else if head == ';' then
    let comment := lexCommentSpecification (head::tail) line column
    comment :: lexSpecification (tail.drop (comment.Length - 1)) line comment.Location.End.Column

  else if Char.isAlpha head then
    let identifier := lexIdentifierSpecification (head::tail) line column
    identifier :: lexSpecification (tail.drop (identifier.Length - 1)) line identifier.Location.End.Column

  else if Char.isDigit head then
     let digit := lexNumberSpecification (head::tail) line column
     digit :: lexSpecification (tail.drop (digit.Length - 1)) line digit.Location.End.Column

  else if head = '"' then
      let string := lexStringSpecification (head::tail) line column
      string :: lexSpecification (tail.drop (string.Length - 1)) line string.Location.End.Column

  else if IsOperator head then
      LexOperator head line column :: lexSpecification tail line (column + 1)

  else
    Token.Create TokenKind.Invalid (SourceLocation.Create (SourcePosition.Create line column) (SourcePosition.Create line (column + 1))) head.toString :: Lex tail line (column + 1)

termination_by source _  _ =>source.length
decreasing_by
  all_goals simp only [List.length_cons, List.length_drop]
  all_goals omega
