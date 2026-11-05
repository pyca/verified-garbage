module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.P192
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print

/-! # Deterministic ECDSA (RFC 6979) over P-192 on RISC-V, with HMAC as a table -/

@[expose] public section

namespace VG.Generic.P192.AllMdHash.RISCV64.EcdsaP192Rfc6979

open VG.Proof.Ecdsa.Rfc6979.RISCV64 (signCodeT stackT OK)
open VG.Proof.Ecdsa.Rfc6979.RISCV64.P192 (curveT verifiedT)
open VG.Proof.HmacTable.RISCV64 (tables names)

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P192.curve)
    (vs : List Proof.HmacTable.RISCV64.HVar) : List Artifact :=
  if hv : OK vs then [
    Spec.Ecdsa.Rfc6979.Curves.p192SignApi.artifact RISCV64.target {
      tables := [("hmac", tables vs)]
      code := signCodeT (curveT h.law) Spec.Ecdsa.Rfc6979.Curves.p192.tries vs
      stack := stackT
      verified := verifiedT h.law vs hv }]
  else []

end VG.Generic.P192.AllMdHash.RISCV64.EcdsaP192Rfc6979
