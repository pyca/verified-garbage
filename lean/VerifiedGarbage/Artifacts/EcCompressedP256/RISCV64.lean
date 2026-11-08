module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.EcKey.Compressed.P256.RISCV64
public import VerifiedGarbage.Proof.EcKey.Compressed.RISCV64.P256.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.EcKey.P256
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.EcKey.Compressed.RISCV64.P256.Lit
public import VerifiedGarbage.Proof.P256.RISCV64.Law

/-! # P-256 point compression and decompression (SEC 1 §§2.3.3–2.3.4) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.EcCompressedP256.RISCV64

open VG.Proof.P256.RISCV64 (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.P256.inst.compressPublicKeyApi.artifact RISCV64.target {
    code := Impl.EcKey.Compressed.RISCV64.compressP256
    verified := Proof.EcKey.Compressed.RISCV64.P256.compress_verified },
  Spec.EcKey.P256.inst.decompressPublicKeyApi.artifact RISCV64.target {
    code := Impl.EcKey.Compressed.RISCV64.decompressP256
    verified := Proof.EcKey.Compressed.RISCV64.P256.decompress_verified hasLaw.law }]

end VG.Artifacts.EcCompressedP256.RISCV64
