module

public import VerifiedGarbage.TCB.Code

/-!
# Indirect calls of a list of functions

`Code.icalls i targets` is the indirect call by the instruction `i` of
whichever of the functions `targets` (names and code) is at the address it
calls (`Code.icall`): the chain of their `icall`s, ending in code that is
never run (`Exec.icallNext` only steps to an indirect call). A caller taking
a table of functions (`Abi.withTables`) calls the functions of a slot by it,
with `targets` those of every table's slot (`Proof/Framework/ICall.lean`).
-/

@[expose] public section

namespace VG

/-- The indirect call by `i` of the functions `targets`. -/
def Code.icalls {I C : Type} (i : I) : List (String × Code I C) → Code I C
  | [] => .block []
  | (n, b) :: ts => .icall i n b (Code.icalls i ts)

end VG
