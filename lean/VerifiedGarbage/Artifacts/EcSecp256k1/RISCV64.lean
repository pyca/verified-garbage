module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdh.Secp256k1.RISCV64
public import VerifiedGarbage.Proof.Ecdh.RISCV64.Secp256k1.PublicKeyVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.EcKey.Secp256k1
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Ecdh.RISCV64.Secp256k1.EcdhLit
public import VerifiedGarbage.Proof.Secp256k1.RISCV64.Law
public import VerifiedGarbage.Impl.EcKey.Compressed.Secp256k1.RISCV64
public import VerifiedGarbage.Proof.EcKey.Compressed.RISCV64.Secp256k1.Verified
import VerifiedGarbage.Proof.EcKey.Compressed.RISCV64.Secp256k1.Lit

/-! # secp256k1 public keys (FIPS 186-5 §A.2) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.EcSecp256k1.RISCV64

open VG.Proof.Secp256k1.RISCV64 (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.Secp256k1.inst.compressPublicKeyApi.artifact RISCV64.target {
    code := Impl.EcKey.Compressed.RISCV64.Fn.compressSecp256k1
    verified := .scrubbed Proof.EcKey.Compressed.RISCV64.Secp256k1.compress_scrubbed },
  Spec.EcKey.Secp256k1.inst.decompressPublicKeyApi.artifact RISCV64.target {
    code := Impl.EcKey.Compressed.RISCV64.Fn.decompressSecp256k1
    verified := .scrubbed (Proof.EcKey.Compressed.RISCV64.Secp256k1.decompress_scrubbed hasLaw.law) },
  Spec.EcKey.Secp256k1.publicKeyApi.artifact RISCV64.target {
    code := Impl.Ecdh.RISCV64.Fn.publicKeySecp256k1
    verified := .scrubbed (Proof.Ecdh.RISCV64.Secp256k1.publicKey_scrubbed hasLaw.law) }]

end VG.Artifacts.EcSecp256k1.RISCV64
