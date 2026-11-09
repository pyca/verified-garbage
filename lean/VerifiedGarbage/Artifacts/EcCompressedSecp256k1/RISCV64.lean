module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.EcKey.Compressed.Secp256k1.RISCV64
public import VerifiedGarbage.Proof.EcKey.Compressed.RISCV64.Secp256k1.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.EcKey.Secp256k1
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.EcKey.Compressed.RISCV64.Secp256k1.Lit
public import VerifiedGarbage.Proof.Secp256k1.RISCV64.Law

/-! # secp256k1 point compression and decompression (SEC 1 §§2.3.3–2.3.4) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.EcCompressedSecp256k1.RISCV64

open VG.Proof.Secp256k1.RISCV64 (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.Secp256k1.inst.compressPublicKeyApi.artifact RISCV64.target {
    code := Impl.EcKey.Compressed.RISCV64.compressSecp256k1
    verified := Proof.EcKey.Compressed.RISCV64.Secp256k1.compress_verified },
  Spec.EcKey.Secp256k1.inst.decompressPublicKeyApi.artifact RISCV64.target {
    code := Impl.EcKey.Compressed.RISCV64.decompressSecp256k1
    verified := Proof.EcKey.Compressed.RISCV64.Secp256k1.decompress_verified hasLaw.law }]

end VG.Artifacts.EcCompressedSecp256k1.RISCV64
