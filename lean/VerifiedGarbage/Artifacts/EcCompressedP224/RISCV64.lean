module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.EcKey.Compressed.P224.RISCV64
public import VerifiedGarbage.Proof.EcKey.Compressed.RISCV64.P224.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.EcKey.P224
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.EcKey.Compressed.RISCV64.P224.Lit
public import VerifiedGarbage.Proof.P224.RISCV64.Law

/-! # P-224 point compression and decompression (SEC 1 §§2.3.3–2.3.4) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.EcCompressedP224.RISCV64

open VG.Proof.P224.RISCV64 (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.P224.inst.compressPublicKeyApi.artifact RISCV64.target {
    code := Impl.EcKey.Compressed.RISCV64.compressP224
    verified := Proof.EcKey.Compressed.RISCV64.P224.compress_verified },
  Spec.EcKey.P224.inst.decompressPublicKeyApi.artifact RISCV64.target {
    code := Impl.EcKey.Compressed.RISCV64.decompressP224
    verified := Proof.EcKey.Compressed.RISCV64.P224.decompress_verified hasLaw.law }]

end VG.Artifacts.EcCompressedP224.RISCV64
