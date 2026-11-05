module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.BrainpoolP512r1
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Deterministic ECDSA (RFC 6979) over brainpoolP512r1 on RISC-V, with HMAC as a table -/

@[expose] public section

namespace VG.Generic.BrainpoolP512r1.AllMdHash.RISCV64.EcdsaBrainpoolP512r1Rfc6979

open VG.Proof.Ecdsa.Rfc6979.RISCV64 (signCodeT stackT OK)
open VG.Proof.Ecdsa.Rfc6979.RISCV64.BrainpoolP512r1 (curveT verifiedT)
open VG.Proof.HmacTable.RISCV64 (tables names)

def artifacts (h : Proof.Weierstrass.HasLaw Spec.BrainpoolP512r1.curve)
    (vs : List Proof.HmacTable.RISCV64.HVar) : List Artifact :=
  if hv : OK vs then [
    Spec.Ecdsa.Rfc6979.Curves.brainpoolp512r1SignApi.artifact RISCV64.target {
      tables := [("hmac", tables vs)]
      code := signCodeT (curveT h.law) Spec.Ecdsa.Rfc6979.Curves.brainpoolp512r1.tries vs
      stack := stackT
      verified := verifiedT h.law vs hv }]
  else []

end VG.Generic.BrainpoolP512r1.AllMdHash.RISCV64.EcdsaBrainpoolP512r1Rfc6979
