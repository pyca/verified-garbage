module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.EcKey.Compressed.Contract
public import VerifiedGarbage.Spec.EcKey.P384
import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Impl.Ecdh.P384.RISCV64
import VerifiedGarbage.Proof.Ecdh.RISCV64.P384.PublicKeyVerified
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Ecdh.RISCV64.P384.EcdhLit
import VerifiedGarbage.Proof.P384.RISCV64.Law
import VerifiedGarbage.Impl.EcKey.Compressed.P384.RISCV64
import VerifiedGarbage.Proof.EcKey.Compressed.RISCV64.P384.Verified
import VerifiedGarbage.Proof.EcKey.Compressed.RISCV64.P384.Lit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # P-384 public keys (FIPS 186-5 §A.2) on RISC-V -/

namespace VG.Artifacts.EcP384.RISCV64

open VG.Proof.P384.RISCV64 (hasLaw)

public def artifacts : List (Artifact RISCV64.target) := [
  Spec.EcKey.P384.inst.compressPublicKeyApi.artifact RISCV64.target {
    code := Impl.EcKey.Compressed.RISCV64.Fn.compressP384
    verified := Proof.EcKey.Compressed.RISCV64.P384.compress_scrubbed },
  Spec.EcKey.P384.inst.decompressPublicKeyApi.artifact RISCV64.target {
    code := Impl.EcKey.Compressed.RISCV64.Fn.decompressP384
    verified := Proof.EcKey.Compressed.RISCV64.P384.decompress_scrubbed hasLaw.law },
  Spec.EcKey.P384.publicKeyApi.artifact RISCV64.target {
    code := Impl.Ecdh.RISCV64.Fn.publicKeyP384
    verified := Proof.Ecdh.RISCV64.P384.publicKey_scrubbed hasLaw.law }]

spec_apis artifacts

end VG.Artifacts.EcP384.RISCV64
