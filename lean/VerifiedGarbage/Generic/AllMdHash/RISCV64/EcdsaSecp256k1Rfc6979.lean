module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.Secp256k1
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
public import VerifiedGarbage.Proof.Secp256k1.RISCV64.Law

/-! # Deterministic ECDSA (RFC 6979) over secp256k1 on RISC-V, with HMAC as a table -/

@[expose] public section

namespace VG.Generic.AllMdHash.RISCV64.EcdsaSecp256k1Rfc6979

open VG.Proof.Secp256k1.RISCV64 (hasLaw)
open VG.Proof.Ecdsa.Rfc6979.RISCV64 (signCodeT stackT OK)
open VG.Proof.Ecdsa.Rfc6979.RISCV64.Secp256k1 (curveT verifiedT)
open VG.Proof.HmacTable.RISCV64 (tables names)

def artifacts (vs : List Proof.HmacTable.RISCV64.HVar) : List Artifact :=
  if hv : OK vs ∧ Impl.Ecdsa.RISCV64.Comb.secp256k1Sym ∉ names vs then [
    Spec.Ecdsa.Rfc6979.Curves.secp256k1SignApi.artifact RISCV64.target {
      tables := [("hmac", tables vs)]
      code := signCodeT (curveT hasLaw.law) Spec.Ecdsa.Rfc6979.Curves.secp256k1.tries vs
      stack := stackT
      verified := verifiedT hasLaw.law vs hv }]
  else []

end VG.Generic.AllMdHash.RISCV64.EcdsaSecp256k1Rfc6979
