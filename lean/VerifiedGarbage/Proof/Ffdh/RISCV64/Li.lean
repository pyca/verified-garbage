module

public import VerifiedGarbage.TCB.RISCV64.Isa
import VerifiedGarbage.Proof.Framework.RISCV64.MRun

/-! # `li` of a numeral in FFDH's RISC-V proofs

`fin64_exec_li_lit`: `li` of a numeral below 2048, written as an `Int`
literal as the code writes it (`.li d 3`), which `exec_li_nat`'s cast does
not match.
-/

@[expose] public section

namespace VG.Proof.Ffdh.RISCV64

open VG VG.RISCV64

/-- `li` of a numeral below 2048, as an `Int` literal. -/
theorem fin64_exec_li_lit {s : State} {d : Reg} {m : Nat} (h : m < 2048) :
    exec (.li d (OfNat.ofNat m : Int)) s = some (s.write d (BitVec.ofNat 64 m)) :=
  exec_li_nat h

end VG.Proof.Ffdh.RISCV64
