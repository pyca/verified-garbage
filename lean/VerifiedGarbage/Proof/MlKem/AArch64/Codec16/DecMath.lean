module
public import VerifiedGarbage.Impl.MlKem.AArch64.Codec16
public import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.DecLanes

import VerifiedGarbage.Proof.Framework.AArch64.Simd64
import VerifiedGarbage.Proof.Rc4.AArch64.Vec
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit

/-! # SIMD decoder arithmetic -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Codec16
open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Proof.Rc4.AArch64
open VG.Impl.MlKem.AArch64.Codec16 (decMath)

def decoded (x : BitVec 128) (part : VPermOp) : BitVec 128 :=
  VPermOp.eval part .s4 (reduced (low x)) (reduced (high x))

theorem dec_math_ok (s : State) (h16 : s.v .v16 = decMask) (h17 : s.v .v17 = mask12)
    (h18 : s.v .v18 = qvec) : WP isa (.block decMath) s fun t =>
    t.v .v0 = decoded (ofVDwords (s.gpr .x9) (s.gpr .x10)) .zip1 ∧
    t.v .v1 = decoded (ofVDwords (s.gpr .x9) (s.gpr .x10)) .zip2 ∧
    t.gpr=s.gpr ∧ t.mem=s.mem ∧ t.rd=s.rd ∧ t.wr=s.wr ∧ t.sp=s.sp ∧
    (∀ r, r ≠ .v0 → r ≠ .v1 → r ≠ .v2 → r ≠ .v3 → r ≠ .v4 → t.v r = s.v r) := by
  unfold decMath
  rrun [h16,h17,h18,VG.AArch64.setLane_pair_hi,VShiftOp.eval,decoded,low,high,reduced,tbl,
    RegUpd.sp_setV]
  refine ⟨by rfl,by rfl,?_⟩
  intro r h0 h1 h2 h3 h4
  simp only [h0,h1,h2,h3,h4,ite_false]

end VG.Proof.MlKem.AArch64.Codec16
