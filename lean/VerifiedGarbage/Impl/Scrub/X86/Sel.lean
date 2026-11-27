module

public import VerifiedGarbage.Impl.Scrub.X86

/-!
# Clearing only the doublewords of the stack that may hold secrets (x86, 32-bit)

`scrubSel rb n ws c` is `scrubAll rb n c` (`Impl/Scrub/X86.lean`), but zeroes,
of the `n` bytes below `esp`, only the doublewords `ws` (doubleword `k` the
four bytes at `4 k` from the frame's base, its lowest address), one
`mov [esp + 4k], ecx` each, `ecx` zero (`wipeSel`), and opens no frame for
no doubleword, as ARMv7's does (`Impl/Scrub/Arm/Sel.lean`). They are the
doublewords that the residue analysis of the whole, cleanup included
(`X86.rtaint`, `Proof/Framework/X86/ResidueTaint.lean`), finds may differ
between two runs: what is left of a function that wipes its own scratch
space is the few doublewords it does not wipe (the frame header of
`withStackScratch`, its innermost frames).

It is a module of its own so that adding it rebuilds none of the functions
that import `scrubAll`. `Proof/Framework/X86/ScrubSel.lean` states what makes
a function so emitted return without secret residue.
-/

@[expose] public section

namespace VG.Impl.Scrub.X86

open VG.X86

/-- `mov [esp + 4k], ecx` for each doubleword `k` of `ws`. -/
def wipeWords (ws : List Nat) : List Instr := ws.map fun k => .store ⟨.esp, 4 * k⟩ .ecx

/-- Zero the doublewords `ws` of the `n` bytes below `esp`, in a frame of
them, through `ecx`; nothing for no doubleword. -/
def wipeSel (n : Nat) : List Nat → Prog isa
  | [] => .block []
  | w :: ws => .frame (.alloc n) (.block (.mov .ecx (.imm 0) :: wipeWords (w :: ws))) (.free n)

/-- `c`, then the doublewords `ws` of the `n` bytes below `esp` zeroed, then
`tail rb`: the function as emitted, for code that the residue analysis
finds leaves secrets on the stack only in those doublewords. -/
def scrubSel (rb n : Nat) (ws : List Nat) (c : Prog isa) : Prog isa :=
  .seq c (.seq (wipeSel n ws) (.block (tail rb)))

end VG.Impl.Scrub.X86
