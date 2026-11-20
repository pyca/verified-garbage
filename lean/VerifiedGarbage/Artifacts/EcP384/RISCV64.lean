module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdh.P384.RISCV64
public import VerifiedGarbage.Proof.Ecdh.RISCV64.P384.PublicKeyVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.EcKey.P384
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Ecdh.RISCV64.P384.EcdhLit
public import VerifiedGarbage.Proof.P384.RISCV64.Law
public import VerifiedGarbage.Impl.EcKey.Compressed.P384.RISCV64
public import VerifiedGarbage.Proof.EcKey.Compressed.RISCV64.P384.Verified
import VerifiedGarbage.Proof.EcKey.Compressed.RISCV64.P384.Lit

/-! # P-384 public keys (FIPS 186-5 §A.2) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.EcP384.RISCV64

open VG.Proof.P384.RISCV64 (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.P384.inst.compressPublicKeyApi.artifact RISCV64.target {
    code := Impl.EcKey.Compressed.RISCV64.Fn.compressP384
    verified := .scrubbed Proof.EcKey.Compressed.RISCV64.P384.compress_scrubbed },
  Spec.EcKey.P384.inst.decompressPublicKeyApi.artifact RISCV64.target {
    code := Impl.EcKey.Compressed.RISCV64.Fn.decompressP384
    verified := .scrubbed (Proof.EcKey.Compressed.RISCV64.P384.decompress_scrubbed hasLaw.law) },
  Spec.EcKey.P384.publicKeyApi.artifact RISCV64.target {
    code := Impl.Ecdh.RISCV64.Fn.publicKeyP384
    verified := .scrubbed (Proof.Ecdh.RISCV64.P384.publicKey_scrubbed hasLaw.law) }]

end VG.Artifacts.EcP384.RISCV64
