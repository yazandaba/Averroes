namespace Averroes.Lexer

structure SourcePosition where
  Create ::
  Line : Nat
  Column : Nat
deriving Repr

structure SourceLocation where
  Create ::
  Start : SourcePosition
  End : SourcePosition
deriving Repr

inductive TokenKind where
| LeftParnthesis
| RightParenthesis
| Number
| String
| Identifier
| Operator
| Fragment -- whtiespaces and comments
| Invalid
| Eof
deriving BEq, Repr

structure Token where
  Create ::
  Kind : TokenKind
  Location : SourceLocation
  Text : String

-- Only meaningful for single-line tokens: a fragment can end on a later line.
def Token.Length (token : Token) : Nat := token.Location.End.Column - token.Location.Start.Column


def IsOperator : Char -> Bool
| '+'
| '-'
| '*'
| '/'
| '%'
| '!'
| '^'
| '|'
| '&' => true
| _ => false

-- Scans string content up to the closing '"'. A '\' escapes the next char,
-- so '\"' does not close the string (and '\\' is a plain backslash).
def ScanString : (List Char) -> List Char
| [] => []
| '"' :: _ => []
| '\\' :: ch :: tail => '\\' :: ch :: ScanString tail
| ch :: tail => ch :: ScanString tail

def LexString : (List Char) -> Nat -> Nat -> Token
| [] , line, column => Token.Create TokenKind.Invalid (SourceLocation.Create (SourcePosition.Create line column) (SourcePosition.Create line column)) "[FATAL] INVALID EMPTY STRING LEXEM"
| _ :: rest, line, column =>
  let string := ScanString rest
  if string.length == rest.length then
    Token.Create TokenKind.Invalid (SourceLocation.Create (SourcePosition.Create line column) (SourcePosition.Create line (column + (rest.length + 1)))) "unterminated string"
  else
    let literal := s!"\"{String.ofList string}\""
    Token.Create TokenKind.String (SourceLocation.Create (SourcePosition.Create line column) (SourcePosition.Create line (column + literal.length))) literal

def LexNumber : (List Char) -> Nat -> Nat -> Token
| [] , line, column => Token.Create TokenKind.Invalid (SourceLocation.Create (SourcePosition.Create line column) (SourcePosition.Create line column)) "[FATAL] INVALID EMPTY NUMBER LEXEM"
| fnum :: rest, line, column =>
  let (number, reminder) := (fnum::rest).span Char.isDigit
  if reminder[0]? == some '.' then -- floating point
    let mantisa := (reminder.drop 1).takeWhile Char.isDigit
    if mantisa.length == 0 then
      Token.Create TokenKind.Invalid (SourceLocation.Create (SourcePosition.Create line column) (SourcePosition.Create line (column + (String.ofList number ++ ".").length))) s!"malformed floating point literal '{String.ofList number}.'"
    else
      let float := (String.ofList number) ++ "." ++ (String.ofList mantisa)
      Token.Create TokenKind.Number (SourceLocation.Create (SourcePosition.Create line column) (SourcePosition.Create line (column + float.length))) float
  else
    Token.Create TokenKind.Number (SourceLocation.Create (SourcePosition.Create line column) (SourcePosition.Create line (column + number.length))) (String.ofList number)

def LexIdentifier : (List Char) -> Nat -> Nat -> Token
| [] , line, column => Token.Create TokenKind.Invalid (SourceLocation.Create (SourcePosition.Create line column) (SourcePosition.Create line column)) "[FATAL] INVALID EMPTY IDENTEFIER LEXEM"
| ch :: rest, line, column =>
  let id := ch :: rest.takeWhile (Char.isAlphanum .)
  Token.Create TokenKind.Identifier (SourceLocation.Create (SourcePosition.Create line column) (SourcePosition.Create line (column + id.length))) (String.ofList id)

def LexOperator : (Char) -> Nat -> Nat -> Token
| ch, line, column =>
  if IsOperator ch then
    Token.Create TokenKind.Operator (SourceLocation.Create (SourcePosition.Create line column) (SourcePosition.Create line (column + 1))) ch.toString
  else
    Token.Create TokenKind.Invalid (SourceLocation.Create (SourcePosition.Create line column) (SourcePosition.Create line column)) "[FATAL] INVALID NON OPERATOR LEXEM"


def LexComment : (List Char) -> Nat -> Nat -> Token
| ';' :: tail, line, column =>
  let comment := ';'::tail.takeWhile (. != '\n')
  Token.Create TokenKind.Fragment (SourceLocation.Create (SourcePosition.Create line column) (SourcePosition.Create line (column + comment.length))) (String.ofList comment)
| _ , line, column => Token.Create TokenKind.Invalid (SourceLocation.Create (SourcePosition.Create line column) (SourcePosition.Create line column)) "[FATAL] INVALID COMMENT LEXEM"



def LexFragmentsCore : (List Char) -> String -> Nat -> Nat -> Token
-- End of input preserves the fragment accumulated so far.
| [] , fragment ,line, column => Token.Create TokenKind.Fragment (SourceLocation.Create (SourcePosition.Create line column) (SourcePosition.Create line column)) fragment

| '\r' :: '\n' :: tail, fragment, line, _ => LexFragmentsCore tail (fragment ++ "\r\n") (line + 1) 0

| '\n' :: tail, fragment, line, _ => LexFragmentsCore tail (fragment ++ "\n") (line + 1) 0

| ' ' :: tail, fragment, line, column => LexFragmentsCore tail (fragment ++ " ") line (column + 1)

| '\t' :: tail, fragment, line, column => LexFragmentsCore tail (fragment ++ "\t") line (column + 1)

| _ :: _ , fragment, line, column => Token.Create TokenKind.Fragment (SourceLocation.Create (SourcePosition.Create line column) (SourcePosition.Create line column)) fragment

termination_by text _ _ _ => text.length


def LexFragments : (List Char) -> Nat -> Nat -> SourceLocation × Token
| [], line, column =>
  let emptyToken := LexFragmentsCore [] "" line column
  (emptyToken.Location, emptyToken)
| ch :: rest, line, column =>
  let fragmentToken := LexFragmentsCore (ch :: rest) "" line column
  -- the location of the tokenization cursor aka where 'LexFragmentCore' stopped is represented by 'fragmentToken'
  -- location but this really should be the fragment token location !! it should be the first spot/location where
  -- it was detected which is represented by matched line,column , the computed location or span would be consumed by
  -- the caller of this function to update the lexer state
  (fragmentToken.Location, {fragmentToken with Location := { fragmentToken.Location with Start := SourcePosition.Create line column }})



def Lex (source : List Char) (line column : Nat) : List Token := match source with
| [] => [Token.Create TokenKind.Eof (SourceLocation.Create (SourcePosition.Create line column) (SourcePosition.Create line (column + 1))) "\x00"]
| '(' :: rest =>
      { Kind := TokenKind.LeftParnthesis
        Location := SourceLocation.Create (SourcePosition.Create line column) (SourcePosition.Create line (column + 1))
        Text := "("
      } :: Lex rest line (column + 1)

| ')' :: rest =>
       {
        Kind := TokenKind.RightParenthesis
        Location := SourceLocation.Create (SourcePosition.Create line column) (SourcePosition.Create line (column + 1))
        Text := ")"
      } :: Lex rest line (column + 1)

| ch :: rest =>
  if (Char.isWhitespace ch) then
    let (location,fragment) := LexFragments source line column
    let ⟨skippedLines,lastColumn⟩ := location.End
    fragment :: Lex (rest.drop (fragment.Text.length - 1)) skippedLines lastColumn

  else if ch == ';' then
    let comment := LexComment source line column
    comment :: Lex (rest.drop (comment.Length - 1)) line comment.Location.End.Column

  else if ch.isAlpha then
    let identifier := LexIdentifier source line column
    identifier :: Lex (rest.drop (identifier.Length - 1)) line identifier.Location.End.Column

  else if ch.isDigit then
     let digit := LexNumber source line column
     digit :: Lex (rest.drop (digit.Length - 1)) line digit.Location.End.Column

  else if ch == '"' then
      let string := LexString source line column
      string :: Lex (rest.drop (string.Length - 1)) line string.Location.End.Column

  else if IsOperator ch then
      LexOperator ch line column :: Lex rest line (column + 1)

  else
    Token.Create TokenKind.Invalid (SourceLocation.Create (SourcePosition.Create line column) (SourcePosition.Create line (column + 1))) ch.toString :: Lex rest line (column + 1)

termination_by source.length
decreasing_by
  all_goals simp only [List.length_cons, List.length_drop]
  all_goals omega
