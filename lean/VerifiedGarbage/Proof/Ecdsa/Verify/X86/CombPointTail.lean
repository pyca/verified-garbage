module

public import VerifiedGarbage.Impl.Ecdsa.Verify.X86
public import VerifiedGarbage.Impl.Ecdsa.P256.X86Comb
public import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.P256
import VerifiedGarbage.Proof.Ecdsa.X86.CombFinishCT
import VerifiedGarbage.Proof.Ecdsa.X86.CombLit
import VerifiedGarbage.Proof.Ecdsa.X86.CombStagesCT
import VerifiedGarbage.Proof.Weierstrass.WinLay
import VerifiedGarbage.Proof.Weierstrass.X86.TComb
meta import VerifiedGarbage.Impl.Ecdsa.Verify.X86
meta import VerifiedGarbage.Impl.Ecdsa.P256.X86Comb
meta import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.P256
meta import VerifiedGarbage.Proof.Ecdsa.X86.CombFinishCT
meta import VerifiedGarbage.Proof.Ecdsa.X86.CombLit
meta import VerifiedGarbage.Proof.Ecdsa.X86.CombStagesCT
meta import VerifiedGarbage.Proof.Weierstrass.WinLay
meta import VerifiedGarbage.Proof.Weierstrass.X86.TComb
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit

/-!
# ECDSA verification over P-256 on x86 (32-bit): the point tail as a literal

The saving of the comb's point, the window method of `Q` and the sum
(`NafCallerCT`), as a literal, checked in a module of its own, in parallel
with the constant-time checks (`CombStagesCT`).
-/

@[expose] public section

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
