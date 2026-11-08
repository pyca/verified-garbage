module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.P256
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
public import VerifiedGarbage.Proof.P256.RISCV64.Law

/-! # Deterministic ECDSA (RFC 6979) over P-256 on RISC-V, with HMAC as a table -/

@[expose] public section

namespace VG.Generic.AllMdHash.RISCV64.EcdsaP256Rfc6979

open VG.Proof.P256.RISCV64 (hasLaw)
open VG.Proof.Ecdsa.Rfc6979.RISCV64 (signCodeT stackT OK)
open VG.Proof.Ecdsa.Rfc6979.RISCV64.P256 (curveT verifiedT)
open VG.Proof.HmacTable.RISCV64 (tables names)

def artifacts (vs : List Proof.HmacTable.RISCV64.HVar) : List Artifact :=
  if hv : OK vs ∧ Impl.Ecdsa.RISCV64.Comb.p256Sym ∉ names vs then [
    Spec.Ecdsa.Rfc6979.Curves.p256SignApi.artifact RISCV64.target {
      tables := [("hmac", tables vs)]
      code := signCodeT (curveT hasLaw.law) Spec.Ecdsa.Rfc6979.Curves.p256.tries vs
      stack := stackT
      verified := verifiedT hasLaw.law vs hv }]
  else []

end VG.Generic.AllMdHash.RISCV64.EcdsaP256Rfc6979
