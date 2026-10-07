import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedInverse
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedPoints
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedAbi

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64

/-- Both allocated stages restore the additional callee-saved registers before
returning to the unchanged verifier stages. -/
theorem allocatedVerify_restored (hL : Law Spec.P256.curve) (hI : InvSounds)
    (hTInv : InvToM p256.C.n)
    (hTcomb : CombOkW Spec.P256.curve 7 37 Impl.P256.p256Comb7 Impl.P256.p256Comb7Start)
    {s t : State} {tr : List Leak} (hp : VPre p256 s)
    (he : Exec isa P256Allocated.verify s tr t) : ∀ r∈untouched,t.gpr r=s.gpr r := by
  refine allocatedVerify_extra_preserved (p256_ok hI)
    (fun _ h => allocatedPrefix_ok hI hTInv h) ?_
    (fun _ _ _ h m => Allocated.points_untouched (p256_ok hI) hL hTcomb h m) hp he
  intro s₀ a ha
  refine WP.mono (allocatedInverse_ok hI hTInv ha.scr ha.mod ha.lt) fun b hb r hr => ?_
  exact hb.1.gpr r ((show ∀ r∈untouched,r∉invAllocatedOuterRegs from by decide) r hr)

end VG.Proof.Ecdsa.Verify.AArch64
