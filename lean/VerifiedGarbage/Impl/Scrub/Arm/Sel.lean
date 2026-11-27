module

public import VerifiedGarbage.Impl.Scrub.Arm

/-!
# Clearing only the words of the stack that may hold secrets (ARMv7)

`scrubSel rb n ws c` is `scrubAll rb n c` (`Impl/Scrub/Arm.lean`), but zeroes,
of the `n` bytes below the stack pointer, only the words `ws` (word `k` the
four bytes at `4 k` from the frame's base, its lowest address), one store
each (`wipeSel`), and opens no frame for no word. They are the words that the
residue analysis of the whole, cleanup included (`Arm.rtaint`,
`Proof/Framework/Arm/ResidueTaint.lean`), finds may differ between two runs:
what is left of a function that wipes its own scratch space is the few words
it does not wipe (the arguments it copies, its innermost frames).

It is a module of its own so that adding it rebuilds none of the functions
that import `scrubAll`. `Proof/Framework/Arm/ScrubSel.lean` states what makes a
function so emitted return without secret residue.
-/

@[expose] public section

namespace VG.Impl.Scrub.Arm

open VG.Arm

/-- `str r2, [r12, #4k]` for each word `k` of `ws`. -/
def wipeWords (ws : List Nat) : List Instr := ws.map fun k => .str .r2 .r12 (4 * k)

/-- Zero the words `ws` of the `n` bytes below the stack pointer, in a frame
of them, through `r12` (its base) and `r2` (zero); nothing for no word. -/
def wipeSel (n : Nat) : List Nat → Prog isa
  | [] => .block []
  | w :: ws =>
    .frame (.alloc n) (.block (.addSp .r12 0 :: .mov .r2 (.imm 0) :: wipeWords (w :: ws))) (.free n)

/-- `c`, then the words `ws` of the `n` bytes below the stack pointer
zeroed, then `tail rb`: the function as emitted, for code that the residue
analysis finds leaves secrets on the stack only in those words. -/
def scrubSel (rb n : Nat) (ws : List Nat) (c : Prog isa) : Prog isa :=
  .seq c (.seq (wipeSel n ws) (.block (tail rb)))

end VG.Impl.Scrub.Arm
