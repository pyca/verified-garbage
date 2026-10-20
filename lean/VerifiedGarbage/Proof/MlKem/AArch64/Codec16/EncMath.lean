module
public import VerifiedGarbage.Impl.MlKem.AArch64.Codec16
public import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.Lanes

import VerifiedGarbage.Proof.Rc4.AArch64.Vec
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit

/-! # Encoding arithmetic block -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Codec16
open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Proof.Rc4.AArch64
open VG.Impl.MlKem.AArch64.Codec16 (encMath)

theorem math_ok (s : State) (hm : s.v .v16 = encMask) :
    WP isa (.block encMath) s fun t =>
      t.gpr .x9 = (tbl (packed (s.v .v0) (s.v .v1)) encMask).extractLsb' 0 64 ∧
      t.gpr .x10 = (tbl (packed (s.v .v0) (s.v .v1)) encMask).extractLsb' 64 64 ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      (∀ r, r ≠ .x9 → r ≠ .x10 → t.gpr r = s.gpr r) ∧ t.v .v16 = s.v .v16 := by
  unfold encMath
  rrun [hm,VShiftOp.eval,packed,tbl,RegUpd.sp_setV,RegUpd.sp_write]
  refine ⟨by rfl,by rfl,?_⟩
  intro r h9 h10
  simp only [h9,h10,ite_false]

end VG.Proof.MlKem.AArch64.Codec16
