module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.EcKey.Compressed.P192.RISCV64
public import VerifiedGarbage.Proof.EcKey.Compressed.RISCV64.P192.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.EcKey.P192
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.EcKey.Compressed.RISCV64.P192.Lit

/-! # P-192 point compression and decompression (SEC 1 §§2.3.3–2.3.4) on RISC-V -/

@[expose] public section

namespace VG.Generic.P192.RISCV64.EcCompressedP192

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P192.curve) : List Artifact := [
  Spec.EcKey.P192.inst.compressPublicKeyApi.artifact RISCV64.target {
    code := Impl.EcKey.Compressed.RISCV64.compressP192
    verified := Proof.EcKey.Compressed.RISCV64.P192.compress_verified },
  Spec.EcKey.P192.inst.decompressPublicKeyApi.artifact RISCV64.target {
    code := Impl.EcKey.Compressed.RISCV64.decompressP192
    verified := Proof.EcKey.Compressed.RISCV64.P192.decompress_verified h.law }]

end VG.Generic.P192.RISCV64.EcCompressedP192
