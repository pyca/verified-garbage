import VerifiedGarbage.Proof.Ecdsa.X86.CombCode

/-!
# ECDSA over P-256 on x86 (32-bit): the constant time of the comb's iteration
-/

namespace VG.Proof.Ecdsa.X86
open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Proof.Mont.X86 VG.Proof.Mont
open VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass Spec.Weierstrass

variable {scratchSecond : Bool}

/-- One iteration reads a public table address, scans every entry, then
performs scalar arithmetic. The loop invariant supplies that address again
at the next iteration. -/
theorem combStep_rel : RelCT isa (VG.X86.Taint.Agree (combτAt scratchSecond)) combStep (fun _ _ => True) :=
  by
    cases scratchSecond <;>
      exact RelCT.taint (A := sseTaint) _ (fun _ _ h => h)
        (by taint_decide_weak VG.Proof.Ecdsa.X86.combWeak)

end VG.Proof.Ecdsa.X86
