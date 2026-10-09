import VerifiedGarbage.Proof.Ecdsa.X86.CombCode

/-!
# ECDSA over P-256 on x86 (32-bit): the constant time of the comb's last step
-/

namespace VG.Proof.Ecdsa.X86
open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Proof.Mont.X86 VG.Proof.Mont
open VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass Spec.Weierstrass

variable {scratchSecond : Bool}

/-- The last step's code. -/
def combFinish : Prog isa := .seq (.block p256K.outFix) (Impl.Weierstrass.X86.fprog p256K.F p256K.outOps)
materialize_code combFinish

theorem combFinish_rel : RelCT isa (VG.X86.Taint.Agree (combτAt scratchSecond))
    (.seq (.block p256K.outFix) (Impl.Weierstrass.X86.fprog p256K.F p256K.outOps)) (fun _ _ => True) := by
  change RelCT isa _ combFinish _
  cases scratchSecond <;>
    exact RelCT.taint (A := sseTaint) _ (fun _ _ h => h) (by taint_decide)

end VG.Proof.Ecdsa.X86
