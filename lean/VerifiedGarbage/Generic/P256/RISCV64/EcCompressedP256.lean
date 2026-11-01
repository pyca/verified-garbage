module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.EcKey.Compressed.P256.RISCV64
public import VerifiedGarbage.Proof.EcKey.Compressed.RISCV64.P256.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.EcKey.P256
import VerifiedGarbage.Proof.EcKey.Compressed.RISCV64.P256.Lit

/-! # P-256 point compression and decompression (SEC 1 §§2.3.3–2.3.4) on RISC-V -/

@[expose] public section

namespace VG.Generic.P256.RISCV64.EcCompressedP256

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P256.curve) : List Artifact := [
  Spec.EcKey.P256.inst.compressPublicKeyApi.artifact RISCV64.target {
    code := Impl.EcKey.Compressed.RISCV64.compressP256
    verified := Proof.EcKey.Compressed.RISCV64.P256.compress_verified },
  Spec.EcKey.P256.inst.decompressPublicKeyApi.artifact RISCV64.target {
    code := Impl.EcKey.Compressed.RISCV64.decompressP256
    verified := Proof.EcKey.Compressed.RISCV64.P256.decompress_verified h.law }]

end VG.Generic.P256.RISCV64.EcCompressedP256
