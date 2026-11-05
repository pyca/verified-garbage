module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.P224
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print

/-! # Deterministic ECDSA (RFC 6979) over P-224 on RISC-V, with HMAC as a table -/

@[expose] public section

namespace VG.Generic.P224.AllMdHash.RISCV64.EcdsaP224Rfc6979

open VG.Proof.Ecdsa.Rfc6979.RISCV64 (signCodeT stackT OK)
open VG.Proof.Ecdsa.Rfc6979.RISCV64.P224 (curveT verifiedT)
open VG.Proof.HmacTable.RISCV64 (tables names)

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P224.curve)
    (vs : List Proof.HmacTable.RISCV64.HVar) : List Artifact :=
  if hv : OK vs ∧ Impl.Ecdsa.RISCV64.Comb.p224Sym ∉ names vs then [
    Spec.Ecdsa.Rfc6979.Curves.p224SignApi.artifact RISCV64.target {
      tables := [("hmac", tables vs)]
      code := signCodeT (curveT h.law) Spec.Ecdsa.Rfc6979.Curves.p224.tries vs
      consts := Impl.Ecdsa.RISCV64.Comb.p224CombConsts
      stack := stackT
      verified := verifiedT h.law vs hv }]
  else []

end VG.Generic.P224.AllMdHash.RISCV64.EcdsaP224Rfc6979
