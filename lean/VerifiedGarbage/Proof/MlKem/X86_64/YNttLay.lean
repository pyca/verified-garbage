module

public import VerifiedGarbage.Proof.MlKem.X86_64.YNtt
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlKem.X86_64.VLay42

/-!
# ML-KEM on x86-64: AVX2 registers, more pieces

`GOnly` keeps the lanes of the vector registers if it keeps their upper
halves (`GOnly.lane`), an `add` of an immediate (`addR_ok`), and `sel` of
`0x55` (`sel_55`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem

/-- `GOnly` keeps the lanes of the vector registers if it keeps their upper halves. -/
theorem GOnly.lane {rs : List Reg} {s s' : State} (h : GOnly rs s s') (hy : s'.ymmHi = s.ymmHi) (r : XReg) (l : Nat) :
    s'.lane r l = s.lane r l := by
  simp only [State.lane]; rw [h.xmm, hy]

/-- `add r, v`. -/
theorem addR_ok (r : Reg) (v : BitVec 32) (s : State) :
    WP isa (.block [.alu .add r (.imm v)]) s fun s' =>
      s'.gpr r = s.gpr r + BitVec.signExtend 64 v ∧ GOnly [r] s s' ∧ s'.ymmHi = s.ymmHi := by
  vrunm [RegUpd.ymmHi_setReg]
  exact ⟨by gonly, rfl⟩

theorem sel_55 {j : Nat} (hj : j < 4) : sel 0x55 j = 1 := by
  rcases (by bdd_omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;> decide

end VG.Proof.MlKem.X86_64
