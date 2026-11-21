module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdh.P224.RISCV64
public import VerifiedGarbage.Proof.Ecdh.RISCV64.P224.PublicKeyVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.EcKey.P224
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Ecdh.RISCV64.P224.EcdhLit
public import VerifiedGarbage.Proof.P224.RISCV64.Law
public import VerifiedGarbage.Impl.EcKey.Compressed.P224.RISCV64
public import VerifiedGarbage.Proof.EcKey.Compressed.RISCV64.P224.Verified
import VerifiedGarbage.Proof.EcKey.Compressed.RISCV64.P224.Lit

/-! # P-224 public keys (FIPS 186-5 §A.2) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.EcP224.RISCV64

open VG.Proof.P224.RISCV64 (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.P224.inst.compressPublicKeyApi.artifact RISCV64.target {
    code := Impl.EcKey.Compressed.RISCV64.Fn.compressP224
    verified := Proof.EcKey.Compressed.RISCV64.P224.compress_scrubbed },
  Spec.EcKey.P224.inst.decompressPublicKeyApi.artifact RISCV64.target {
    code := Impl.EcKey.Compressed.RISCV64.Fn.decompressP224
    verified := Proof.EcKey.Compressed.RISCV64.P224.decompress_scrubbed hasLaw.law },
  Spec.EcKey.P224.publicKeyApi.artifact RISCV64.target {
    code := Impl.Ecdh.RISCV64.Fn.publicKeyP224
    verified := Proof.Ecdh.RISCV64.P224.publicKey_scrubbed hasLaw.law }]

end VG.Artifacts.EcP224.RISCV64
