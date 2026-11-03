import Averroes.Parser
open Averroes.Parser

def main (args : List String) : IO Unit := do
  let text := " ".intercalate args
  let .Unit atoms := Parse text
  IO.println s!"Parsed {atoms.length} top-level atoms"
