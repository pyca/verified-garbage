import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CombMain
import VerifiedGarbage.Proof.Ecdsa.X86.CombStagesCT

/-!
# ECDSA verification over P-256 on x86 (32-bit): the point tail as a literal

The saving of the comb's point, the window method of `Q` and the sum
(`NafCallerCT`), as a literal, checked in a module of its own, in parallel
with the constant-time checks (`CombStagesCT`).
-/

namespace VG.Proof.Ecdsa.Verify.X86
open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Proof.Mont.X86 VG.Proof.Mont
open VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.X86
open VG.Impl.Ecdsa.Verify.X86

def vPointTailCode : Prog isa :=
  .seq (.block (Impl.Ecdsa.Verify.X86.Cfg.save p256Comb)) <|
  .seq (Impl.Ecdsa.Verify.X86.Cfg.windowMulQ p256Comb)
    (Impl.Ecdsa.Verify.X86.Cfg.sum p256Comb)
materialize_code vPointTailCode

end VG.Proof.Ecdsa.Verify.X86
