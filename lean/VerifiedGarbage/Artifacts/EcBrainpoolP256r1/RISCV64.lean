module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdh.BrainpoolP256r1.RISCV64
public import VerifiedGarbage.Proof.Ecdh.RISCV64.BrainpoolP256r1.PublicKeyVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.EcKey.BrainpoolP256r1
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Ecdh.RISCV64.BrainpoolP256r1.EcdhLit
public import VerifiedGarbage.Proof.BrainpoolP256r1.RISCV64.Law
public import VerifiedGarbage.Impl.EcKey.Compressed.BrainpoolP256r1.RISCV64
public import VerifiedGarbage.Proof.EcKey.Compressed.RISCV64.BrainpoolP256r1.Verified
import VerifiedGarbage.Proof.EcKey.Compressed.RISCV64.BrainpoolP256r1.Lit

/-! # brainpoolP256r1 public keys (FIPS 186-5 §A.2) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.EcBrainpoolP256r1.RISCV64

open VG.Proof.BrainpoolP256r1.RISCV64 (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.BrainpoolP256r1.publicKeyApi.artifact RISCV64.target {
    code := Impl.Ecdh.RISCV64.Fn.publicKeyBrainpoolP256r1
    verified := Proof.Ecdh.RISCV64.BrainpoolP256r1.publicKey_scrubbed hasLaw.law },
  Spec.EcKey.BrainpoolP256r1.inst.compressPublicKeyApi.artifact RISCV64.target {
    code := Impl.EcKey.Compressed.RISCV64.Fn.compressBrainpoolP256r1
    verified := Proof.EcKey.Compressed.RISCV64.BrainpoolP256r1.compress_scrubbed },
  Spec.EcKey.BrainpoolP256r1.inst.decompressPublicKeyApi.artifact RISCV64.target {
    code := Impl.EcKey.Compressed.RISCV64.Fn.decompressBrainpoolP256r1
    verified := Proof.EcKey.Compressed.RISCV64.BrainpoolP256r1.decompress_scrubbed hasLaw.law }]

end VG.Artifacts.EcBrainpoolP256r1.RISCV64
