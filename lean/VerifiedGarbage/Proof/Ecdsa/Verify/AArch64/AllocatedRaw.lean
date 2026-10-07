import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedField
import VerifiedGarbage.Proof.P256.VerifySparse.Fprog

namespace VG.Proof.Ecdsa.Verify.AArch64.Allocated
open VG VG.Proof.Mont VG.Proof.Weierstrass

/-- All sparse arithmetic obligations are discharged for the concrete P-256 field. -/
theorem raw_correct : RawCorrect := by
  intro ops base V E s hi hs hr
  exact Proof.P256.VerifySparse.fprog_ok rfl (by decide)
    JointLayout.layout.lay JointLayout.layout.aligned (unitMod_pow_two (by decide) _) ops hi hs hr

end VG.Proof.Ecdsa.Verify.AArch64.Allocated
