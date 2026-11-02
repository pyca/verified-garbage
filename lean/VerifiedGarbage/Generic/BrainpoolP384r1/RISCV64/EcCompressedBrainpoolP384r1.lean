module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.EcKey.Compressed.BrainpoolP384r1.RISCV64
public import VerifiedGarbage.Proof.EcKey.Compressed.RISCV64.BrainpoolP384r1.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.EcKey.BrainpoolP384r1
import VerifiedGarbage.Proof.EcKey.Compressed.RISCV64.BrainpoolP384r1.Lit

/-! # brainpoolP384r1 point compression and decompression (SEC 1 §§2.3.3–2.3.4) on RISC-V -/

@[expose] public section

namespace VG.Generic.BrainpoolP384r1.RISCV64.EcCompressedBrainpoolP384r1

def artifacts (h : Proof.Weierstrass.HasLaw Spec.BrainpoolP384r1.curve) : List Artifact := [
  Spec.EcKey.BrainpoolP384r1.inst.compressPublicKeyApi.artifact RISCV64.target {
    code := Impl.EcKey.Compressed.RISCV64.compressBrainpoolP384r1
    verified := Proof.EcKey.Compressed.RISCV64.BrainpoolP384r1.compress_verified },
  Spec.EcKey.BrainpoolP384r1.inst.decompressPublicKeyApi.artifact RISCV64.target {
    code := Impl.EcKey.Compressed.RISCV64.decompressBrainpoolP384r1
    verified := Proof.EcKey.Compressed.RISCV64.BrainpoolP384r1.decompress_verified h.law }]

end VG.Generic.BrainpoolP384r1.RISCV64.EcCompressedBrainpoolP384r1
