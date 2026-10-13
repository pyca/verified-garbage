module

public import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CombMain
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CombMain
public import VerifiedGarbage.Proof.Ecdsa.X86.CombStagesCT
meta import VerifiedGarbage.Proof.Ecdsa.X86.CombStagesCT
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Ecdsa.Verify.X86.NafLayout
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.X25519.X86.Column
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86.NafLayout
meta import VerifiedGarbage.Proof.Framework.X86.Sse
meta import VerifiedGarbage.Proof.X25519.X86.Column

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
