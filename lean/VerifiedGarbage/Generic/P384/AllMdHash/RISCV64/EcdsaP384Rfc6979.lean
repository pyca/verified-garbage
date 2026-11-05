module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.P384
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print

/-! # Deterministic ECDSA (RFC 6979) over P-384 on RISC-V, with HMAC as a table -/

@[expose] public section

namespace VG.Generic.P384.AllMdHash.RISCV64.EcdsaP384Rfc6979

open VG.Proof.Ecdsa.Rfc6979.RISCV64 (signCodeT stackT OK)
open VG.Proof.Ecdsa.Rfc6979.RISCV64.P384 (curveT verifiedT)
open VG.Proof.HmacTable.RISCV64 (tables names)

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P384.curve)
    (vs : List Proof.HmacTable.RISCV64.HVar) : List Artifact :=
  if hv : OK vs ∧ Impl.Ecdsa.RISCV64.Comb.p384Sym ∉ names vs then [
    Spec.Ecdsa.Rfc6979.Curves.p384SignApi.artifact RISCV64.target {
      tables := [("hmac", tables vs)]
      code := signCodeT (curveT h.law) Spec.Ecdsa.Rfc6979.Curves.p384.tries vs
      consts := Impl.Ecdsa.RISCV64.Comb.p384CombConsts
      stack := stackT
      verified := verifiedT h.law vs hv }]
  else []

end VG.Generic.P384.AllMdHash.RISCV64.EcdsaP384Rfc6979
