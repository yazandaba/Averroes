import Mathlib.Data.List.TakeWhile
import Averroes.Lexer
import Averroes.Parser
import Averroes.Specification
open Averroes.Lexer
open Averroes.Specification
open Averroes.Parser

open Averroes.Diagnostics

private theorem OperatorClassificationMatchesIsOperator (ch : Char) : (match ch with
| '+'
| '-'
| '*'
| '/'
| '%'
| '!'
| '^'
| '|'
| '&' => true
| _ => false) = IsOperator ch := by rfl

theorem SpanLoopSndIsDropWhile {α : Type} (p : α → Bool) (l : List α) (acc : List α) :
    (List.span.loop p l acc).snd = l.dropWhile p := by
  induction l generalizing acc with
  | nil =>
    rfl
  | cons x xs ih =>
    simp [List.span.loop, List.dropWhile]
    split
    · exact ih (x :: acc)
    · rfl

theorem SpanLoopFstIsTakeWhile {α : Type} (p : α → Bool) (l : List α) (acc : List α) :
   (List.span.loop p l acc).fst = acc.reverse ++ List.takeWhile p l := by
  induction l generalizing acc with
  | nil => simp_all [List.span.loop]

  | cons x xs ih =>
    simp_all [List.takeWhile,List.span.loop]
    split
    · specialize ih (x::acc)
      simp_all

    · simp_all

-----------------   String Lexing Proofs   -----------------
-----------------                          -----------------

mutual

theorem LexStringIsSound
    (text : List Char) (line column : Nat) :
    LexString text line column = lexStringSpecification text line column:= by
  cases text with
  | nil => simpa [lexStringSpecification] using (LexStringEmptyIsInvalid line column)

  | cons head rest =>
      change LexString ('"' :: rest) line column = _
      by_cases hclosingQuote : HasClosingQuote rest
      · simpa [lexStringSpecification, hclosingQuote] using
          (LexValidStringIsSound ('"' :: rest) line column
            (by simp)
            (by simp)
            (by simpa using hclosingQuote))

      · simpa [lexStringSpecification, hclosingQuote] using
          (LexUnterminatedStringIsSound ('"' :: rest) line column
            (by simp)
            (by simp)
            (by simpa using hclosingQuote))



-----------------   Valid String Lexing Proof   -----------------
-----------------                                -----------------
private theorem StringScanStopsBeforeQuote (text : List Char) (_hnonEmpty: text.length > 0) (hhasQuote: HasClosingQuote text) :
  (ScanString text).length < text.length := by
  clear _hnonEmpty
  fun_induction ScanString text <;> simp_all [HasClosingQuote]

private theorem LexValidStringIsSound
  (text : List Char) (line : Nat) (column : Nat)
  (hnonEmpty: text.length > 0) (hstartsWithQuote: text[0] = '"') (hclosingQuote: HasClosingQuote (text.drop 1)):
  LexString text line column =
  let content := ScanString (text.drop 1)
  let literal := s!"\"{String.ofList content}\""
  Token.Create TokenKind.String (SourceLocation.Create (SourcePosition.Create line column) (SourcePosition.Create line (column + literal.length))) literal := by
  simp [LexString]
  cases text with
  | nil => contradiction
  | cons head tail =>
    simp at hstartsWithQuote hclosingQuote
    rw [hstartsWithQuote]
    simp
    exact Nat.ne_of_lt (StringScanStopsBeforeQuote tail (by cases tail <;> simp_all [HasClosingQuote]) hclosingQuote)


-----------------   Invalid String Lexing Proof   -----------------
-----------------                                 -----------------

private theorem UnterminatedStringScanHasTextLength
  (text: List Char)
  (hlenNonNeg: text.length >= 0) (hnoQuote: ¬ HasClosingQuote text) :
  (ScanString text).length = text.length := by
  fun_induction ScanString text <;> simp_all [HasClosingQuote]


private theorem LexUnterminatedStringIsSound
  (text : List Char) (line : Nat) (column : Nat)
  (hnonEmpty: text.length > 0) (hstartsWithQuote: text[0] = '"') (hnoClosingQuote: ¬ HasClosingQuote (text.drop 1)):
  LexString text line column = Token.Create TokenKind.Invalid (SourceLocation.Create (SourcePosition.Create line column) (SourcePosition.Create line (column + text.length))) "unterminated string"
  := by
  simp[LexString]
  cases text with
  | nil => simp at hnonEmpty
  | cons head tail =>
    simp
    exact UnterminatedStringScanHasTextLength tail (Nat.zero_le tail.length) hnoClosingQuote


private theorem LexStringEmptyIsInvalid (line column : Nat) :
  LexString [] line column = Token.Create TokenKind.Invalid (SourceLocation.Create (SourcePosition.Create line column) (SourcePosition.Create line column)) "[FATAL] INVALID EMPTY STRING LEXEM" :=
  by rfl

end

-----------------   Number Lexing Proof   -----------------
-----------------                         -----------------
mutual
theorem IntScanSpecificationIsTakeWhile (text: List Char) :
  intScanSpecification text = text.takeWhile Char.isDigit := by
  induction text with
  | nil => simp [intScanSpecification]
  | cons head tail ih =>
    simp_all [intScanSpecification,List.takeWhile]
    by_cases hheadDigit: head.isDigit <;> simp_all

theorem LexNumberIsSound (text: List Char) (line column: Nat)
                         (hnonEmpty: 0 < text.length) (hstartsWithDigit: text[0].isDigit):
  LexNumber text line column = lexNumberSpecification text line column := by
  cases text with
  | nil => simp_all [LexNumber,lexNumberSpecification]
  | cons head tail =>
    simp_all [lexNumberSpecification,LexNumber,List.span,SpanLoopSndIsDropWhile,IntScanSpecificationIsTakeWhile,-List.takeWhile_eq_nil_iff]
    have hcharAfterDigits: (List.dropWhile Char.isDigit tail)[0]? = tail[(intScanSpecification  tail).length]? := by
        simp [IntScanSpecificationIsTakeWhile]
        simpa using (List.getElem?_append_right
                      (l₁ := tail.takeWhile Char.isDigit)
                      (l₂ := tail.dropWhile Char.isDigit)
                      (i := (tail.takeWhile Char.isDigit).length)
                      (Nat.le_refl _)).symm
    split
    . simp_all [IntScanSpecificationIsTakeWhile,-List.takeWhile_eq_nil_iff]

      have hdropDigits : List.drop (List.takeWhile Char.isDigit tail).length tail = List.dropWhile Char.isDigit tail := by
          simpa only [List.takeWhile_append_dropWhile] using
            (List.drop_left
              (l₁ := List.takeWhile Char.isDigit tail)
              (l₂ := List.dropWhile Char.isDigit tail))

      have hafterDot: (List.drop ((List.takeWhile Char.isDigit tail).length + 1) tail) =
                (List.dropWhile Char.isDigit tail).tail := by
                 rw [← List.tail_drop]
                 exact congrArg List.tail hdropDigits

      by_cases hmantissaEmpty: List.takeWhile Char.isDigit (List.dropWhile Char.isDigit tail).tail = [] <;>
      simp_all [SpanLoopFstIsTakeWhile,Nat.add_comm,-List.takeWhile_eq_nil_iff]

    . simp_all [IntScanSpecificationIsTakeWhile,SpanLoopFstIsTakeWhile]

theorem NoFloatingPointInValidInt (text: List Char) (hallDigits: ∀ n ∈ text, Char.isDigit n): '.' ∉ List.dropWhile Char.isDigit text := by
  induction text with
  | nil => simp
  | cons head tail ih => --simp_all [List.dropWhile]
    simp [List.dropWhile]
    by_cases head.isDigit
    . simp_all
    . rename_i hheadNotDigit
      simp at hheadNotDigit
      exfalso
      specialize hallDigits head
      simp at hallDigits
      simp_all

theorem LexValidInteger
  (text intPart rest: List Char) (line column: Nat)
  (hintNonEmpty: 0 < intPart.length) (hallDigits: ∀ n ∈ intPart, Char.isDigit n)
  (hrestNoDot: rest[0]? != some '.') (hrestNoDigit: !rest[0]?.any Char.isDigit)(htext: text = intPart ++ rest):
  LexNumber text line column =
  Token.Create TokenKind.Number (SourceLocation.Create (SourcePosition.Create line column) (SourcePosition.Create line (column + intPart.length))) (String.ofList intPart) := by
  simp [LexNumber]
  have hfirstDigit: intPart[0].isDigit := by simp_all
  have hnoDotInInt: '.' ∉ intPart := by specialize hallDigits '.' ; simp_all
  cases text with
  | nil =>
    simp
    have hintNeNil : intPart ≠ [] := List.length_pos_iff.mp hintNonEmpty
    have htextNeNil : ¬ [] = intPart ++ rest := by simp [hintNeNil]
    contradiction
    --have hne: ¬ [] = intPart ++ rest := by omega
  | cons head tail =>
    simp only
    split
    . rename_i hdotAfterDigits
      exfalso
      simp [List.span,List.span.loop] at hdotAfterDigits
      have hintFirstIsHead: intPart[0] = head := by
        cases intPart with
        | nil => exfalso ; simp at hintNonEmpty
        | cons h t => simp_all

      rw [hintFirstIsHead] at hfirstDigit
      simp [hfirstDigit,SpanLoopSndIsDropWhile] at hdotAfterDigits
      have hintAllDigits : List.takeWhile Char.isDigit intPart = intPart := List.takeWhile_eq_self_iff.mpr hallDigits
      have htail: tail = intPart.tail ++ rest := by cases intPart <;> simp_all ; simp at hintNonEmpty
      have hintTailDigits: ∀ (n: Char), n ∈ intPart.tail -> Char.isDigit n = true := by
        intro n hnInTail
        have hnInIntCons: n ∈ intPart[0] :: intPart.tail := List.mem_cons_of_mem intPart[0] hnInTail
        rw [List.length_pos_iff] at hintNonEmpty
        have hintCons : intPart = intPart[0] :: intPart.tail := by
          cases intPart with
          | nil =>
              contradiction
          | cons head tail =>
              rfl
        symm at hintCons
        rw [hintCons] at hnInIntCons
        exact hallDigits n hnInIntCons

      simp_all

      have hrestNoDigitPrefix: rest = List.dropWhile Char.isDigit rest := by
        unfold List.dropWhile
        split <;> simp_all

      symm at hrestNoDigitPrefix
      rw [hrestNoDigitPrefix] at hdotAfterDigits
      contradiction

    . simp_all [List.span,SpanLoopFstIsTakeWhile]
      intro hrestNonEmpty
      simp_all


theorem LexValidFloat
  (text intPart mantissa rest: List Char) (line column: Nat)
  (hintDigits: ∀ n ∈ intPart, Char.isDigit n) (hmantissaDigits: ∀ n ∈ mantissa, Char.isDigit n)
  (hmantissaNonEmpty : mantissa ≠ []) (htext : text = intPart ++ ['.'] ++ mantissa ++ rest)
  (hrestNoDigit: !rest[0]?.any Char.isDigit ):
  let float :=  intPart ++ ['.'] ++ mantissa
  LexNumber text line column = Token.Create TokenKind.Number (SourceLocation.Create (SourcePosition.Create line column) (SourcePosition.Create line (column + float.length))) (String.ofList float) := by
  cases text with
  | nil =>
    unfold LexNumber
    exfalso
    simp at htext
  | cons head tail =>
    unfold LexNumber
    have hmantissaAllDigits : (List.takeWhile Char.isDigit mantissa) = mantissa := by
           simpa using List.takeWhile_append_of_pos  (p := Char.isDigit) (l₁ := mantissa) (l₂ := []) hmantissaDigits
    simp_all [-hmantissaAllDigits]
    split
    . split
      . rename_i hdotAfterDigits hmantissaEmpty
        rw [<- htext] at hmantissaEmpty
        simp [List.span,SpanLoopSndIsDropWhile] at hmantissaEmpty hdotAfterDigits
        simp_all
        have hmantissaLen : 0 < mantissa.length := by exact List.length_pos_iff.mpr hmantissaNonEmpty
        have hmantissaFirstDigit: (mantissa[0]'hmantissaLen).isDigit := by
          specialize hmantissaDigits mantissa[0]
          simp_all
        simp_all

      . have hrestDigitsLen: (List.takeWhile Char.isDigit rest).length = 0 := by
          cases rest <;> simp_all [List.takeWhile]
        simp_all [-hrestDigitsLen,List.span,SpanLoopFstIsTakeWhile,SpanLoopSndIsDropWhile]
        constructor
        . rw [hrestDigitsLen]
          simp_all [Nat.add_comm,Nat.add_left_comm]
          rfl

        . simp [String.append_assoc]
          intro hrestNonEmpty
          have hrestDigitsNil : List.takeWhile Char.isDigit rest = [] := by simpa using hrestDigitsLen
          have hrestFirstNotDigit := (List.takeWhile_eq_nil_iff.mp hrestDigitsNil)
          specialize hrestFirstNotDigit hrestNonEmpty
          simp_all

    . rename_i hnoDotAfterDigits
      have hdotInText: '.' ∈ head::tail := by simp_all
      rw [<- htext]
      exfalso
      simp_all [List.span,SpanLoopSndIsDropWhile,List.dropWhile]

-----------------   Invalid Number Lexing Proof   -----------------
-----------------                                 -----------------

theorem LexInvalidFloatEmptyMantissa
  (text intPart mantissa rest: List Char) (line column: Nat)
  (hintDigits: ∀ n ∈ intPart, Char.isDigit n) (hmantissaEmpty: mantissa = []) (htext: text = intPart ++ ['.'] ++ mantissa ++ rest)
  (hrestNoDigit: !rest[0]?.any Char.isDigit ):
  LexNumber text line column = Token.Create TokenKind.Invalid (SourceLocation.Create (SourcePosition.Create line column) (SourcePosition.Create line (column + (String.ofList intPart ++ ".").length))) s!"malformed floating point literal '{String.ofList intPart}.'"
  := by
  cases text with
  | nil =>
    exfalso
    simp at htext
  | cons head tail =>
    unfold LexNumber
    simp_all
    split <;>
    simp_all [List.span,SpanLoopSndIsDropWhile,SpanLoopFstIsTakeWhile]
    intro hrestNonEmpty
    specialize hintDigits rest[0]
    simp_all


theorem LexNumberEmptyIsInvalid (line column: Nat) :
  LexNumber [] line column = Token.Create TokenKind.Invalid (SourceLocation.Create (SourcePosition.Create line column) (SourcePosition.Create line column)) "[FATAL] INVALID EMPTY NUMBER LEXEM"
  := by rfl

end


-----------------   Operator Lexing Proof   -----------------
-----------------                           -----------------

theorem LexValidOperator (op: Char) (line column: Nat) (hisOperator: IsOperator op) :
  LexOperator op line column = Token.Create TokenKind.Operator (SourceLocation.Create (SourcePosition.Create line column) (SourcePosition.Create line (column + 1))) op.toString := by
  simp_all [LexOperator]

theorem LexInvalidOperator (op: Char) (line column: Nat) (hnotOperator: ¬ IsOperator op) :
  LexOperator op line column = Token.Create TokenKind.Invalid (SourceLocation.Create (SourcePosition.Create line column) (SourcePosition.Create line column)) "[FATAL] INVALID NON OPERATOR LEXEM" := by
  simp_all[LexOperator]


theorem LexOperatorIsSound (op: Char) (line column: Nat) :
  LexOperator op line column =
 if IsOperator op then
    Token.Create TokenKind.Operator (SourceLocation.Create (SourcePosition.Create line column) (SourcePosition.Create line (column + 1))) op.toString
  else
    Token.Create TokenKind.Invalid (SourceLocation.Create (SourcePosition.Create line column) (SourcePosition.Create line column)) "[FATAL] INVALID NON OPERATOR LEXEM" := by
  split <;>
  simp_all [LexValidOperator,LexInvalidOperator]


-----------------   Identifier Lexing Proof   -----------------
-----------------                             -----------------

theorem LexValidIdentifier
  (text: List Char) {id rest: List Char} (line column: Nat)
  (hidAlphanum: ∀ c ∈ id , c.isAlphanum) (hidScan: id = (text.takeWhile (Char.isAlphanum .))) (htext: text = id ++ rest)
  (hidNonEmpty: id ≠ [])(htextNonEmpty: text ≠ []):
  LexIdentifier text line column = Token.Create TokenKind.Identifier (SourceLocation.Create (SourcePosition.Create line column) (SourcePosition.Create line (column + id.length))) (String.ofList id) := by
  cases text with
  | nil => contradiction
  | cons head tail =>
    have hheadInId: head ∈ id := by
      cases id with
      | nil => contradiction
      | cons idHead idTail =>
        have hidHeadIsHead: idHead = head := by
          injection htext with hheadEq htailEq
          symm at hheadEq
          exact hheadEq
        rw[hidHeadIsHead]
        simp_all
    have hheadAlphanum: head.isAlphanum := by specialize hidAlphanum head hheadInId ; exact hidAlphanum
    simp [LexIdentifier]
    rw [hidScan] at htext
    constructor <;> rw [hidScan] <;> simp[hheadAlphanum]

theorem LexIdentifierEmptyIsInvalid (line column: Nat) :
  LexIdentifier [] line column = Token.Create TokenKind.Invalid (SourceLocation.Create (SourcePosition.Create line column) (SourcePosition.Create line column)) "[FATAL] INVALID EMPTY IDENTEFIER LEXEM" := by rfl

theorem IdentifierScanSpecificationIsTakeWhile (text: List Char):
  text.takeWhile (Char.isAlphanum .) = identifierScanSpecification text := by
  induction text with
  | nil => simp_all [identifierScanSpecification]
  | cons head tail =>
    simp_all[identifierScanSpecification,List.takeWhile]
    by_cases hheadAlphanum: head.isAlphanum <;> simp_all

theorem LexIdentifierIsSound (text: List Char) (line column: Nat) :
  LexIdentifier text line column = lexIdentifierSpecification text line column := by
  cases text with
  | nil => simp_all [LexIdentifier,lexIdentifierSpecification]
  | cons head tail =>
    simp_all [LexIdentifier,lexIdentifierSpecification,IdentifierScanSpecificationIsTakeWhile]

-----------------   Fragment Lexing Proof     -----------------
-----------------                             -----------------

theorem LexFragmentsCoreWithAccumulatorIsSound
  (text: List Char) (fragment: String) (line column: Nat) :
  LexFragmentsCore text fragment line column =
  let token := lexFragmentsCoreSpecification text line column
  { token with Text := fragment ++ token.Text } := by

  fun_induction LexFragmentsCore text fragment line column <;>
    simp_all [lexFragmentsCoreSpecification, FragmentsText, FragmentsLocation,
      String.ofList_cons, String.append_assoc]
  rw [← String.append_assoc]
  rfl

theorem LexFragmentsCoreIsSound (text: List Char) (line column: Nat) :
  LexFragmentsCore text "" line column = lexFragmentsCoreSpecification text line column := by
  simpa using LexFragmentsCoreWithAccumulatorIsSound text "" line column

theorem LexFragmentsIsSound (text: List Char) (line column: Nat):
  LexFragments text line column = lexFragmentsSpecification text line column := by
  cases text <;> simp_all[LexFragments,lexFragmentsSpecification,LexFragmentsCoreIsSound]

-----------------   Comment Lexing Proof      -----------------
-----------------                             -----------------

theorem CommentScanSpecificationIsTakeWhile (text: List Char) :
  text.takeWhile (. != '\n') = lexCommentScanSpecification text := by
  fun_induction lexCommentScanSpecification text <;> simp_all

theorem LexCommentIsSound (text: List Char) (line column: Nat) :
 LexComment text line column = lexCommentSpecification text line column := by
 cases text with
 | nil => simp_all [LexComment,lexCommentSpecification]
 | cons head tail =>
  simp_all [LexComment,lexCommentSpecification,CommentScanSpecificationIsTakeWhile]
  rfl


-----------------      Lexing Proof      -----------------
-----------------                        -----------------

theorem LexIsSound (text: List Char) (line column: Nat) :
  Lex text line column = lexSpecification text line column := by
  fun_induction Lex text line column
  . simp [lexSpecification]
  . simp_all [lexSpecification]
  . simp_all [lexSpecification]

  . rename_i hfragments ih
    simp_all [lexSpecification,LexFragmentsIsSound,LexFragmentsCoreIsSound,
              lexFragmentsSpecification,lexFragmentsCoreSpecification]
    obtain ⟨hfragmentLocation, rfl⟩ := hfragments
    simp_all

  . rename_i line column head tail _ _ _ hsemicolon comment ih
    have hcomment : comment = LexComment (head :: tail) line column := by rfl
    simp_all [lexSpecification,LexCommentIsSound]

  . rename_i line column head tail _ _ _ _ halpha identifier ih
    have hidentifier : identifier = LexIdentifier (head :: tail) line column := by rfl
    simp_all [lexSpecification,LexIdentifierIsSound]

  . rename_i line column head tail _ _ _ _ _ hdigit num ih
    have hnum : num = LexNumber (head :: tail) line column := by rfl
    simp_all [lexSpecification,LexNumberIsSound]

  . rename_i line column head tail _ _ _ _ _ _ hquote string ih
    have hstring : string = LexString (head :: tail) line column := by rfl
    simp_all [lexSpecification,LexStringIsSound]

  . simp_all [LexOperatorIsSound,lexSpecification]
  . simp_all [lexSpecification]


--============================       Parsing Proofs     ============================
--============================                          ============================

private def loc : SourceLocation := SourceLocation.Create ⟨0,0⟩ ⟨0,1⟩
private def lp  : Token := Token.Create .LeftParnthesis   loc "("
private def rp  : Token := Token.Create .RightParenthesis loc ")"
private def eof : Token := Token.Create .Eof              loc "\x00"
private def bad : Token := Token.Create .Invalid          loc "#"

theorem ParseAtomsProgress {tokens : List Token} (hnonEmpty : tokens ≠ []) :
    (ParseAtoms tokens).2.length < tokens.length := by
  have hconsume := ParseAtomsConsumes tokens
  have hlength := List.length_pos_iff.mpr hnonEmpty
  omega

theorem ParseAtomsNonEmptyInputHasAtoms
  (tokens: List Token) (rest: List Token) (finish: Token)
  (htokens: tokens = rest ++ [finish]):
  (ParseAtoms tokens).fst ≠ [] := by
  fun_induction ParseAtoms tokens <;> simp_all

example : ∃ (head : LispAtomSyntax) (tail : List LispAtomSyntax) (sent : LispSentinelSyntax),
  ParseAtoms ([] ++ [rp]) = (head :: tail, []) ∧
  (head :: tail).getLast (by simp) = .Sent sent ∧ sent.SentinelToken = rp :=
  ⟨.Sent ⟨rp, [], none⟩, [], ⟨rp, [], none⟩, by simp [ParseAtoms, rp], rfl, rfl⟩

-- head::tail is used instead of single atoms to avoid providing atoms ≠ [] hypothesis
-- the empty case is proofed later
theorem ParseAtomsClosedListWithoutSiblings
  (tokens : List Token)
  {rest : List Token}
  {start finish : Token}
  (hstart : start.Kind = TokenKind.LeftParnthesis)
  (htokens : tokens = [start] ++ rest ++ [finish])
  (hclosed :
    ∃ (head : LispAtomSyntax)
      (tail : List LispAtomSyntax)
      (sent : LispSentinelSyntax),
      ParseAtoms (rest ++ [finish]) = (head :: tail, []) ∧
      (head :: tail).getLast (by simp) = .Sent sent ∧
      sent.SentinelToken = finish) :

  (ParseAtoms tokens).fst =
    let (atoms, rem) := ParseAtoms (rest ++ [finish])
    let len := rest.length - rem.length
    let (sibling, _) := ParseAtoms (rest.drop len)
    .List {
      Start := start,
      End := finish,
      Atoms := atoms
    } :: sibling := by
  obtain ⟨head, tail, sent, hparse, hlast, hend⟩ := hclosed
  rw [htokens]
  simp [ParseAtoms, hstart, hparse, hlast, hend]


--============================    proofed by codex    ============================

-----------------   Remaining List Parsing Proofs   -----------------

theorem ParseAtomsEmptyInput :
  ParseAtoms [] = ([], []) := by
  simp [ParseAtoms]

-- ParseAtomsClosedListWithSiblings   (input: `)`)
example : ∃ (rem : List Token) (head : LispAtomSyntax) (tail : List LispAtomSyntax) (sent : LispSentinelSyntax),
    ParseAtoms [rp] = (head :: tail, rem) ∧ (head :: tail).getLast (by simp) = .Sent sent :=
  ⟨[], .Sent ⟨rp, [], none⟩, [], ⟨rp, [], none⟩, by simp [ParseAtoms, rp], rfl⟩

theorem ParseAtomsClosedListWithSiblings
  (start : Token) (rest rem : List Token)
  (head : LispAtomSyntax) (tail : List LispAtomSyntax) (sent : LispSentinelSyntax)
  (hstart : start.Kind = TokenKind.LeftParnthesis)
  (hparse : ParseAtoms rest = (head :: tail, rem))
  (hlast : (head :: tail).getLast (by simp) = .Sent sent) :
  ParseAtoms (start :: rest) =
    let len := rest.length - rem.length
    let (sibling, siblingRem) := ParseAtoms (rest.drop len)
    (.List {
      Start := start,
      End := sent.SentinelToken,
      Atoms := head :: tail
    } :: sibling, siblingRem) := by
  simp [ParseAtoms, hstart, hparse, hlast]

-- ParseAtomsListWithoutAtoms   (input: empty)
example : ∃ (rest rem : List Token), ParseAtoms rest = ([], rem) :=
  ⟨[], [], by simp [ParseAtoms]⟩

theorem ParseAtomsListWithoutAtoms
  (start : Token) (rest rem : List Token)
  (hstart : start.Kind = TokenKind.LeftParnthesis)
  (hparse : ParseAtoms rest = ([], rem)) :
  ParseAtoms (start :: rest) =
    ([.List {
      Start := start,
      End := start,
      Diagnostic := MissingListClosingError start.Location,
      Atoms := []
    }], rem) := by
  simp [ParseAtoms, hstart, hparse]

-- ParseAtomsListWithoutClosingParen   (input: EOF)
example : ∃ (rem : List Token) (head : LispAtomSyntax) (tail : List LispAtomSyntax),
    ParseAtoms [eof] = (head :: tail, rem) ∧
    ∀ sent, (head :: tail).getLast (by simp) ≠ .Sent sent :=
  ⟨[], .Leaf { Atom := eof }, [], by simp [ParseAtoms, eof], by intro s; simp⟩

theorem ParseAtomsListWithoutClosingParen
  (start : Token) (rest rem : List Token)
  (head : LispAtomSyntax) (tail : List LispAtomSyntax)
  (hstart : start.Kind = TokenKind.LeftParnthesis)
  (hparse : ParseAtoms rest = (head :: tail, rem))
  (hlast : ∀ sent, (head :: tail).getLast (by simp) ≠ .Sent sent) :
  ParseAtoms (start :: rest) =
    let len := rest.length - rem.length
    let (sibling, siblingRem) := ParseAtoms (rest.drop len)
    (.List {
      Start := start,
      End := start,
      Diagnostic := MissingListClosingError start.Location,
      Atoms := head::tail
    } :: sibling, siblingRem) := by
  cases hlastAtom : (head :: tail).getLast (by simp) <;>
    simp_all [ParseAtoms]

theorem ParseAtomsRightParen
  (finish : Token) (rest : List Token)
  (hfinish : finish.Kind = TokenKind.RightParenthesis) :
  ParseAtoms (finish :: rest) = ([.Sent { SentinelToken := finish }], rest) := by
  simp [ParseAtoms, hfinish]

-----------------   Leaf Parsing Proofs   -----------------

theorem ParseAtomsIdentifier
  (token : Token) (rest : List Token)
  (hkind : token.Kind = TokenKind.Identifier) :
  ParseAtoms (token :: rest) =
    let (atoms, rem) := ParseAtoms rest
    (.Leaf { Atom := token } :: atoms, rem) := by
  simp [ParseAtoms, hkind]

theorem ParseAtomsString
  (token : Token) (rest : List Token)
  (hkind : token.Kind = TokenKind.String) :
  ParseAtoms (token :: rest) =
    let (atoms, rem) := ParseAtoms rest
    (.Leaf { Atom := token } :: atoms, rem) := by
  simp [ParseAtoms, hkind]

theorem ParseAtomsNumber
  (token : Token) (rest : List Token)
  (hkind : token.Kind = TokenKind.Number) :
  ParseAtoms (token :: rest) =
    let (atoms, rem) := ParseAtoms rest
    (.Leaf { Atom := token } :: atoms, rem) := by
  simp [ParseAtoms, hkind]

theorem ParseAtomsOperator
  (token : Token) (rest : List Token)
  (hkind : token.Kind = TokenKind.Operator) :
  ParseAtoms (token :: rest) =
    let (atoms, rem) := ParseAtoms rest
    (.Leaf { Atom := token } :: atoms, rem) := by
  simp [ParseAtoms, hkind]

-----------------   Fragment Parsing Proofs   -----------------

-- ParseAtomsFragmentWithoutAtom   (input: empty)
example : ∃ (rest rem : List Token), ParseAtoms rest = ([], rem) :=
  ⟨[], [], by simp [ParseAtoms]⟩

theorem ParseAtomsFragmentWithoutAtom
  (fragment : Token) (rest rem : List Token)
  (hkind : fragment.Kind = TokenKind.Fragment)
  (hparse : ParseAtoms rest = ([], rem)) :
  ParseAtoms (fragment :: rest) =
    ([.Error { Diagnostic := ParsingInvalidStateError fragment.Location }], rem) := by
  simp [ParseAtoms, hkind, hparse]

-- ParseAtomsFragmentBeforeLeaf   (input: EOF)
example : ∃ rem atom tail, ParseAtoms [eof] = (.Leaf atom :: tail, rem) := by
  simp [ParseAtoms, eof]

theorem ParseAtomsFragmentBeforeLeaf
  (fragment : Token) (rest rem : List Token)
  (atom : LispLeafAtomSyntax) (tail : List LispAtomSyntax)
  (hkind : fragment.Kind = TokenKind.Fragment)
  (hparse : ParseAtoms rest = (.Leaf atom :: tail, rem)) :
  ParseAtoms (fragment :: rest) =
    (.Leaf { atom with Fragments := { Fragment := fragment } :: atom.Fragments } :: tail, rem) := by
  simp [ParseAtoms, hkind, hparse]

-- ParseAtomsFragmentBeforeList   (input: `(`)
example : ∃ rem list tail, ParseAtoms [lp] = (.List list :: tail, rem) := by
  simp [ParseAtoms, lp]

theorem ParseAtomsFragmentBeforeList
  (fragment : Token) (rest rem : List Token)
  (list : LispListSyntax) (tail : List LispAtomSyntax)
  (hkind : fragment.Kind = TokenKind.Fragment)
  (hparse : ParseAtoms rest = (.List list :: tail, rem)) :
  ParseAtoms (fragment :: rest) =
    (.List { list with Fragments := { Fragment := fragment } :: list.Fragments } :: tail, rem) := by
  simp [ParseAtoms, hkind, hparse]

-- ParseAtomsFragmentBeforeSentinel   (input: `)`)
example : ∃ rem sent tail, ParseAtoms [rp] = (.Sent sent :: tail, rem) := by
  simp [ParseAtoms, rp]

theorem ParseAtomsFragmentBeforeSentinel
  (fragment : Token) (rest rem : List Token)
  (sent : LispSentinelSyntax) (tail : List LispAtomSyntax)
  (hkind : fragment.Kind = TokenKind.Fragment)
  (hparse : ParseAtoms rest = (.Sent sent :: tail, rem)) :
  ParseAtoms (fragment :: rest) =
    (.Sent { sent with Fragments := { Fragment := fragment } :: sent.Fragments } :: tail, rem) := by
  simp [ParseAtoms, hkind, hparse]

-- ParseAtomsFragmentBeforeError   (input: invalid token)
example : ∃ rem err tail, ParseAtoms [bad] = (.Error err :: tail, rem) := by
  simp [ParseAtoms, bad]

theorem ParseAtomsFragmentBeforeError
  (fragment : Token) (rest rem : List Token)
  (err : LispErrorSyntax) (tail : List LispAtomSyntax)
  (hkind : fragment.Kind = TokenKind.Fragment)
  (hparse : ParseAtoms rest = (.Error err :: tail, rem)) :
  ParseAtoms (fragment :: rest) = (.Error err :: tail, rem) := by
  simp [ParseAtoms, hkind, hparse]

-----------------   EOF and Invalid Token Parsing Proofs   -----------------

theorem ParseAtomsEof
  (token : Token) (rest : List Token)
  (hkind : token.Kind = TokenKind.Eof) :
  ParseAtoms (token :: rest) = ([.Leaf { Atom := token }], []) := by
  simp [ParseAtoms, hkind]

theorem ParseAtomsInvalidToken
  (token : Token) (rest : List Token)
  (hkind : token.Kind = TokenKind.Invalid) :
  ParseAtoms (token :: rest) =
    let (atoms, rem) := ParseAtoms rest
    (.Error { Diagnostic := UnrecognizedTokenError token token.Location } :: atoms, rem) := by
  simp [ParseAtoms, hkind]

-----------------   Top Level Parsing Proofs   -----------------

theorem ParseTopEmptyInput :
  ParseTop [] = [.Error { Diagnostic := EmptyProgramError }] := by
  simp [ParseTop]

theorem ParseTopWithoutAtoms
  (token : Token) (rest rem : List Token)
  (hparse : ParseAtoms (token :: rest) = ([], rem)) :
  ParseTop (token :: rest) = [.Error { Diagnostic := EmptyProgramError }] := by
  simp [ParseTop, hparse]

-- ParseTopWithStrayRightParen   (input: `)`)
example : ∃ program rem sent, ParseAtoms [rp] = (program, rem) ∧
    program.getLast? = some (.Sent sent) := by
  simp [ParseAtoms, rp]

theorem ParseTopWithStrayRightParen
  (token : Token) (rest rem : List Token)
  (program : List LispAtomSyntax) (sent : LispSentinelSyntax)
  (hparse : ParseAtoms (token :: rest) = (program, rem))
  (hlast : program.getLast? = some (.Sent sent)) :
  ParseTop (token :: rest) =
    program.dropLast ++
      .Sent { sent with Diagnostic := MissingListOpeningError sent.SentinelToken.Location } ::
      ParseTop rem := by
  simp [ParseTop, hparse, hlast]

-- ParseTopWithLeaf   (input: EOF)
example : ∃ program rem atom, ParseAtoms [eof] = (program, rem) ∧
    program.getLast? = some (.Leaf atom) := by
  simp [ParseAtoms, eof]

theorem ParseTopWithLeaf
  (token : Token) (rest rem : List Token)
  (program : List LispAtomSyntax) (atom : LispLeafAtomSyntax)
  (hparse : ParseAtoms (token :: rest) = (program, rem))
  (hlast : program.getLast? = some (.Leaf atom)) :
  ParseTop (token :: rest) = program := by
  simp [ParseTop, hparse, hlast]

-- ParseTopWithList   (input: `(`)
example : ∃ program rem list, ParseAtoms [lp] = (program, rem) ∧
    program.getLast? = some (.List list) := by
  simp [ParseAtoms, lp]

theorem ParseTopWithList
  (token : Token) (rest rem : List Token)
  (program : List LispAtomSyntax) (list : LispListSyntax)
  (hparse : ParseAtoms (token :: rest) = (program, rem))
  (hlast : program.getLast? = some (.List list)) :
  ParseTop (token :: rest) = program := by
  simp [ParseTop, hparse, hlast]

-- ParseTopWithError   (input: invalid token)
example : ∃ program rem err, ParseAtoms [bad] = (program, rem) ∧
    program.getLast? = some (.Error err) := by
  simp [ParseAtoms, bad]

theorem ParseTopWithError
  (token : Token) (rest rem : List Token)
  (program : List LispAtomSyntax) (err : LispErrorSyntax)
  (hparse : ParseAtoms (token :: rest) = (program, rem))
  (hlast : program.getLast? = some (.Error err)) :
  ParseTop (token :: rest) = program := by
  simp [ParseTop, hparse, hlast]
