module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdh.P192.RISCV64
public import VerifiedGarbage.Proof.Ecdh.RISCV64.P192.PublicKeyVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.EcKey.P192
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Ecdh.RISCV64.P192.EcdhLit
public import VerifiedGarbage.Proof.P192.RISCV64.Law
public import VerifiedGarbage.Impl.EcKey.Compressed.P192.RISCV64
public import VerifiedGarbage.Proof.EcKey.Compressed.RISCV64.P192.Verified
import VerifiedGarbage.Proof.EcKey.Compressed.RISCV64.P192.Lit

/-! # P-192 public keys (FIPS 186-5 §A.2) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.EcP192.RISCV64

open VG.Proof.P192.RISCV64 (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.P192.inst.compressPublicKeyApi.artifact RISCV64.target {
    code := Impl.EcKey.Compressed.RISCV64.Fn.compressP192
    verified := .scrubbed Proof.EcKey.Compressed.RISCV64.P192.compress_scrubbed },
  Spec.EcKey.P192.inst.decompressPublicKeyApi.artifact RISCV64.target {
    code := Impl.EcKey.Compressed.RISCV64.Fn.decompressP192
    verified := .scrubbed (Proof.EcKey.Compressed.RISCV64.P192.decompress_scrubbed hasLaw.law) },
  Spec.EcKey.P192.publicKeyApi.artifact RISCV64.target {
    code := Impl.Ecdh.RISCV64.Fn.publicKeyP192
    verified := .scrubbed (Proof.Ecdh.RISCV64.P192.publicKey_scrubbed hasLaw.law) }]

end VG.Artifacts.EcP192.RISCV64
