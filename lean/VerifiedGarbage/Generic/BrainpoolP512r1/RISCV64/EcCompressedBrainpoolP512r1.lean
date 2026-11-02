module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.EcKey.Compressed.BrainpoolP512r1.RISCV64
public import VerifiedGarbage.Proof.EcKey.Compressed.RISCV64.BrainpoolP512r1.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.EcKey.BrainpoolP512r1
import VerifiedGarbage.Proof.EcKey.Compressed.RISCV64.BrainpoolP512r1.Lit

/-! # brainpoolP512r1 point compression and decompression (SEC 1 §§2.3.3–2.3.4) on RISC-V -/

@[expose] public section

namespace VG.Generic.BrainpoolP512r1.RISCV64.EcCompressedBrainpoolP512r1

def artifacts (h : Proof.Weierstrass.HasLaw Spec.BrainpoolP512r1.curve) : List Artifact := [
  Spec.EcKey.BrainpoolP512r1.inst.compressPublicKeyApi.artifact RISCV64.target {
    code := Impl.EcKey.Compressed.RISCV64.compressBrainpoolP512r1
    verified := Proof.EcKey.Compressed.RISCV64.BrainpoolP512r1.compress_verified },
  Spec.EcKey.BrainpoolP512r1.inst.decompressPublicKeyApi.artifact RISCV64.target {
    code := Impl.EcKey.Compressed.RISCV64.decompressBrainpoolP512r1
    verified := Proof.EcKey.Compressed.RISCV64.BrainpoolP512r1.decompress_verified h.law }]

end VG.Generic.BrainpoolP512r1.RISCV64.EcCompressedBrainpoolP512r1
