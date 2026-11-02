module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.BrainpoolP384r1Sha384
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Deterministic ECDSA (RFC 6979) over brainpoolP384r1 with HMAC-SHA-384 on RISC-V -/

@[expose] public section

namespace VG.Generic.BrainpoolP384r1.RISCV64.EcdsaBrainpoolP384r1Sha384

open VG.Proof.Ecdsa.Rfc6979.RISCV64.BrainpoolP384r1Sha384 (pack sign_verified)

def artifacts (h : Proof.Weierstrass.HasLaw Spec.BrainpoolP384r1.curve) : List Artifact := [
  Spec.Ecdsa.Rfc6979.BrainpoolP384r1Sha384.signApi.artifact RISCV64.target {
    code := (pack h.law).c.sign
    stack := 736
    verified := sign_verified h.law }]

end VG.Generic.BrainpoolP384r1.RISCV64.EcdsaBrainpoolP384r1Sha384
