module

import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.CT
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.P256RD
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.CT
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JacChecks
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JacChecks
public import VerifiedGarbage.Proof.Weierstrass.AArch64.CachedAddTiming
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.CachedAddTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticJacTail
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticJacTail

/-! ## `NafChecks` -/

@[expose] public section

/-! ## `CachedChecks` -/

section

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Proof.Weierstrass.AArch64

theorem cachedAdd_checks : CachedField.Checks where
  zero := by
    intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> jac_field_ct
  copyP := by jac_field_ct
  copyQ := by jac_field_ct
  head := by
    dsimp only [CachedField.ops]
    exact Forward.ArithmeticCachedHead.ct
  tail := by
    dsimp only [CachedField.ops]
    exact Forward.ArithmeticJacTail.ct
  double := by
    dsimp only [CachedField.ops]
    exact Forward.rd_ct
  infinity := by jac_field_ct

end VG.Proof.Ecdsa.Verify.AArch64

end
