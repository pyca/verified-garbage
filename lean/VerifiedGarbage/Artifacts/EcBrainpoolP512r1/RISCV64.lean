module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdh.BrainpoolP512r1.RISCV64
public import VerifiedGarbage.Proof.Ecdh.RISCV64.BrainpoolP512r1.PublicKeyVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.EcKey.RISCV64.Scrub
public import VerifiedGarbage.Spec.EcKey.BrainpoolP512r1
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Ecdh.RISCV64.BrainpoolP512r1.EcdhLit
public import VerifiedGarbage.Proof.BrainpoolP512r1.RISCV64.Law
public import VerifiedGarbage.Impl.EcKey.Compressed.BrainpoolP512r1.RISCV64
public import VerifiedGarbage.Proof.EcKey.Compressed.RISCV64.BrainpoolP512r1.Verified
import VerifiedGarbage.Proof.EcKey.Compressed.RISCV64.BrainpoolP512r1.Lit

/-! # brainpoolP512r1 public keys (FIPS 186-5 §A.2) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.EcBrainpoolP512r1.RISCV64

open VG.Proof.BrainpoolP512r1.RISCV64 (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.BrainpoolP512r1.publicKeyApi.artifact RISCV64.target (RISCV64.Scrub.withScrub {
    code := Impl.Ecdh.RISCV64.publicKeyBrainpoolP512r1
    verified := Proof.Ecdh.RISCV64.BrainpoolP512r1.pk_verified hasLaw.law }
    (Proof.EcKey.RISCV64.Scrub.publicKeyOut _ _ [])),
  Spec.EcKey.BrainpoolP512r1.inst.compressPublicKeyApi.artifact RISCV64.target (RISCV64.Scrub.withScrub {
    code := Impl.EcKey.Compressed.RISCV64.compressBrainpoolP512r1
    verified := Proof.EcKey.Compressed.RISCV64.BrainpoolP512r1.compress_verified }
    (Proof.EcKey.RISCV64.Scrub.compressOut _ _ [])),
  Spec.EcKey.BrainpoolP512r1.inst.decompressPublicKeyApi.artifact RISCV64.target (RISCV64.Scrub.withScrub {
    code := Impl.EcKey.Compressed.RISCV64.decompressBrainpoolP512r1
    verified := Proof.EcKey.Compressed.RISCV64.BrainpoolP512r1.decompress_verified hasLaw.law }
    (Proof.EcKey.RISCV64.Scrub.decompressOut _ _ []))]

end VG.Artifacts.EcBrainpoolP512r1.RISCV64
