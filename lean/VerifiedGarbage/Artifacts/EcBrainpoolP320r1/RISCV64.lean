module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.EcKey.BrainpoolP320r1
public import VerifiedGarbage.Spec.EcKey.Compressed.Contract
import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Impl.Ecdh.BrainpoolP320r1.RISCV64
import VerifiedGarbage.Proof.Ecdh.RISCV64.BrainpoolP320r1.PublicKeyVerified
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Ecdh.RISCV64.BrainpoolP320r1.EcdhLit
import VerifiedGarbage.Proof.BrainpoolP320r1.RISCV64.Law
import VerifiedGarbage.Impl.EcKey.Compressed.BrainpoolP320r1.RISCV64
import VerifiedGarbage.Proof.EcKey.Compressed.RISCV64.BrainpoolP320r1.Verified
import VerifiedGarbage.Proof.EcKey.Compressed.RISCV64.BrainpoolP320r1.Lit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # brainpoolP320r1 public keys (FIPS 186-5 §A.2) on RISC-V -/

namespace VG.Artifacts.EcBrainpoolP320r1.RISCV64

open VG.Proof.BrainpoolP320r1.RISCV64 (hasLaw)

public def artifacts : List (Artifact RISCV64.target) := [
  Spec.EcKey.BrainpoolP320r1.publicKeyApi.artifact RISCV64.target {
    code := Impl.Ecdh.RISCV64.Fn.publicKeyBrainpoolP320r1
    verified := Proof.Ecdh.RISCV64.BrainpoolP320r1.publicKey_scrubbed hasLaw.law },
  Spec.EcKey.BrainpoolP320r1.inst.compressPublicKeyApi.artifact RISCV64.target {
    code := Impl.EcKey.Compressed.RISCV64.Fn.compressBrainpoolP320r1
    verified := Proof.EcKey.Compressed.RISCV64.BrainpoolP320r1.compress_scrubbed },
  Spec.EcKey.BrainpoolP320r1.inst.decompressPublicKeyApi.artifact RISCV64.target {
    code := Impl.EcKey.Compressed.RISCV64.Fn.decompressBrainpoolP320r1
    verified := Proof.EcKey.Compressed.RISCV64.BrainpoolP320r1.decompress_scrubbed hasLaw.law }]

spec_apis artifacts

end VG.Artifacts.EcBrainpoolP320r1.RISCV64
