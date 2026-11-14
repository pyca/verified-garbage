module

public import VerifiedGarbage.Impl.Scrub.X86_64

/-!
# Returning without secret residue, the wipe chosen by a public argument (x86-64)

`scrubSel` clears as `scrub` does (`Impl/Scrub/X86_64.lean`), but wipes the
granules `ksT` if the 64-bit word at `[rsp + off]` on return (a stack
argument, which the code leaves as it found it) is below `lim`, and the
granules `ksF` otherwise: for code whose short inputs, by a public length,
write less of its stack than its long ones.
-/

@[expose] public section

namespace VG.Impl.Scrub.X86_64

open VG.X86_64

/-- `mov r11, QWORD PTR [rsp + off]; cmp r11, lim`. -/
def selHead (off : Nat) (lim : BitVec 32) : List Instr :=
  [.mov .r11 (.mem { base := .rsp, disp := (off : Int) }), .alu .cmp .r11 (.imm lim)]

/-- The clearing, with the wipe of `ksT` or `ksF` chosen by `selHead`. -/
def scrubSelTail (v : VecLevel) (retBits : Nat) (xs : List XReg) (ps gs : List Reg) (ksT ksF cs : List Nat)
    (off : Nat) (lim : BitVec 32) (f : VecLevel := v) : Prog isa :=
  .seq (.block (selHead off lim))
    (.ite .b (scrubTail v retBits xs ps gs ksT cs f) (scrubTail v retBits xs ps gs ksF cs f))

/-- `c`, then the clearing chosen by the word at `[rsp + off]`. -/
def scrubSel (v : VecLevel) (retBits : Nat) (xs : List XReg) (ps gs : List Reg) (ksT ksF cs : List Nat)
    (off : Nat) (lim : BitVec 32) (c : Prog isa) (f : VecLevel := v) : Prog isa :=
  .seq c (scrubSelTail v retBits xs ps gs ksT ksF cs off lim f)

end VG.Impl.Scrub.X86_64
