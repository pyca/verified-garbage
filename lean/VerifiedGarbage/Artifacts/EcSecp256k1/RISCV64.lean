module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.EcKey.Compressed.Contract
public import VerifiedGarbage.Spec.EcKey.Secp256k1
import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Impl.Ecdh.Secp256k1.RISCV64
import VerifiedGarbage.Proof.Ecdh.RISCV64.Secp256k1.PublicKeyVerified
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Ecdh.RISCV64.Secp256k1.EcdhLit
import VerifiedGarbage.Proof.Secp256k1.RISCV64.Law
import VerifiedGarbage.Impl.EcKey.Compressed.Secp256k1.RISCV64
import VerifiedGarbage.Proof.EcKey.Compressed.RISCV64.Secp256k1.Verified
import VerifiedGarbage.Proof.EcKey.Compressed.RISCV64.Secp256k1.Lit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # secp256k1 public keys (FIPS 186-5 §A.2) on RISC-V -/

namespace VG.Artifacts.EcSecp256k1.RISCV64

open VG.Proof.Secp256k1.RISCV64 (hasLaw)

public def artifacts : List (Artifact RISCV64.target) := [
  Spec.EcKey.Secp256k1.inst.compressPublicKeyApi.artifact RISCV64.target {
    code := Impl.EcKey.Compressed.RISCV64.Fn.compressSecp256k1
    verified := Proof.EcKey.Compressed.RISCV64.Secp256k1.compress_scrubbed },
  Spec.EcKey.Secp256k1.inst.decompressPublicKeyApi.artifact RISCV64.target {
    code := Impl.EcKey.Compressed.RISCV64.Fn.decompressSecp256k1
    verified := Proof.EcKey.Compressed.RISCV64.Secp256k1.decompress_scrubbed hasLaw.law },
  Spec.EcKey.Secp256k1.publicKeyApi.artifact RISCV64.target {
    code := Impl.Ecdh.RISCV64.Fn.publicKeySecp256k1
    verified := Proof.Ecdh.RISCV64.Secp256k1.publicKey_scrubbed hasLaw.law }]

spec_apis artifacts

end VG.Artifacts.EcSecp256k1.RISCV64
