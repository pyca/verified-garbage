module

public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedFieldTiming
public import VerifiedGarbage.Proof.P256.VerifySparse.Fprog
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Ecdsa.AArch64.Layout
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowEntryTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowSum
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowSumTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafArithmeticTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafEntryTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafSum
import VerifiedGarbage.Proof.Weierstrass.AArch64.TComb
import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowQuad

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.AArch64.Allocated
open VG VG.Proof.Mont VG.Proof.Weierstrass

/-- All sparse arithmetic obligations are discharged for the concrete P-256 field. -/
theorem raw_correct : RawCorrect := by
  intro ops base V E s hi hs hr
  exact Proof.P256.VerifySparse.fprog_ok rfl (by decide)
    JointLayout.layout.lay JointLayout.layout.aligned (unitMod_pow_two (by decide) _) ops hi hs hr

end VG.Proof.Ecdsa.Verify.AArch64.Allocated
