module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.BrainpoolP512r1Sha512
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Deterministic ECDSA (RFC 6979) over brainpoolP512r1 with HMAC-SHA-512 on RISC-V -/

@[expose] public section

namespace VG.Generic.BrainpoolP512r1.RISCV64.EcdsaBrainpoolP512r1Sha512

open VG.Proof.Ecdsa.Rfc6979.RISCV64.BrainpoolP512r1Sha512 (pack sign_verified)

def artifacts (h : Proof.Weierstrass.HasLaw Spec.BrainpoolP512r1.curve) : List Artifact := [
  Spec.Ecdsa.Rfc6979.BrainpoolP512r1Sha512.signApi.artifact RISCV64.target {
    code := (pack h.law).c.sign
    stack := 784
    verified := sign_verified h.law }]

end VG.Generic.BrainpoolP512r1.RISCV64.EcdsaBrainpoolP512r1Sha512
