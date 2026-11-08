module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.EcKey.Compressed.P384.RISCV64
public import VerifiedGarbage.Proof.EcKey.Compressed.RISCV64.P384.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.EcKey.P384
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.EcKey.Compressed.RISCV64.P384.Lit
public import VerifiedGarbage.Proof.P384.RISCV64.Law

/-! # P-384 point compression and decompression (SEC 1 §§2.3.3–2.3.4) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.EcCompressedP384.RISCV64

open VG.Proof.P384.RISCV64 (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.P384.inst.compressPublicKeyApi.artifact RISCV64.target {
    code := Impl.EcKey.Compressed.RISCV64.compressP384
    verified := Proof.EcKey.Compressed.RISCV64.P384.compress_verified },
  Spec.EcKey.P384.inst.decompressPublicKeyApi.artifact RISCV64.target {
    code := Impl.EcKey.Compressed.RISCV64.decompressP384
    verified := Proof.EcKey.Compressed.RISCV64.P384.decompress_verified hasLaw.law }]

end VG.Artifacts.EcCompressedP384.RISCV64
