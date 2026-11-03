module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.BrainpoolP256r1Sha256
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Deterministic ECDSA (RFC 6979) over brainpoolp256r1 with HMAC-SHA-256 on RISC-V -/

@[expose] public section

namespace VG.Generic.BrainpoolP256r1.RISCV64.EcdsaBrainpoolP256r1Sha256

open VG.Proof.Ecdsa.Rfc6979.RISCV64.BrainpoolP256r1Sha256 (pack sign_verified)

def artifacts (h : Proof.Weierstrass.HasLaw Spec.BrainpoolP256r1.curve) : List Artifact := [
  Spec.Ecdsa.Rfc6979.BrainpoolP256r1Sha256.signApi.artifact RISCV64.target {
    code := (pack h.law).c.sign
    consts := Impl.Ecdsa.RISCV64.Comb.brainpoolP256r1CombConsts
    stack := 544
    verified := sign_verified h.law }]

end VG.Generic.BrainpoolP256r1.RISCV64.EcdsaBrainpoolP256r1Sha256
