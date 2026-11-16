module

public import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.Joint
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.ForwardLit
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Snapshot
meta import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.Joint
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.ForwardLit
meta import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Snapshot

/-! P-256 joint verification on AArch64 as a literal. Its forwarded field
programs, which the kernel evaluates slowly, have literals of their own
(`ForwardLit`), which this one reads. -/

@[expose] public section

namespace VG
namespace Proof.Ecdsa.Verify.AArch64.JointLit
open VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Weierstrass.AArch64.Jacobian VG.Impl.Ecdsa.Verify.AArch64.P256Joint

/-- `Joint.mixedAdd` with its `let`s written out: its two forwarded programs
are then closed terms, which `materialize_code` finds and reads from their
literals (`ForwardLit`), where the kernel would run the forwarding pass on
programs bound by a `let`. -/
def mixedAdd (K : WinCfg) (p q o : Pt) : Prog isa :=
  .seq (.block (zeroMask K.M.n p.z)) <|
  .ite (.nonzero .x .x2) (.block (copyPt K.M.n o q)) <|
  .seq (.block (copy K.M.n K.S.t2 p.x ++ copy K.M.n K.S.t4 p.y)) <|
  .seq (VG.Impl.P256.VerifyArithmetic.program K.M (jacMixedHead K.S p q)) <|
  .seq (.block (zeroMask K.M.n K.S.t3)) <|
  .ite (.nonzero .x .x2)
    (.seq (.block (zeroMask K.M.n K.S.t5)) <|
      .ite (.nonzero .x .x2) (VG.Impl.P256.VerifyDouble.double K.M K.S p o) (.block (infinity K o)))
    (VG.Impl.P256.VerifyArithmetic.program K.M (jacMixedTail K.S p q o))

materialize_code mixed := mixedAdd cfg.K cfg.K.R cfg.K.E cfg.K.D

/-- The literal of the verification's mixed addition, under the term its code
has (`P256Joint.ops`): equal to `mixedAdd`'s by unfolding both. -/
noncomputable abbrev jointMixedAdd.lit := mixed.lit
theorem jointMixedAdd.lit_eq :
    Joint.mixedAdd cfg.K cfg.K.R cfg.K.E cfg.K.D = jointMixedAdd.lit := mixed.lit_eq

end Proof.Ecdsa.Verify.AArch64.JointLit

materialize_code Impl.Ecdsa.Verify.AArch64.P256Joint.verify
end VG
