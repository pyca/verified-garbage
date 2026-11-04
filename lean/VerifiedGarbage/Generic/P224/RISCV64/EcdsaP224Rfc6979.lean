module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.P224
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Deterministic ECDSA (RFC 6979) over P-224 on RISC-V, with the hash function as a table -/

@[expose] public section

namespace VG.Generic.P224.RISCV64.EcdsaP224Rfc6979

open VG.Proof.Ecdsa.Rfc6979.RISCV64 (signCode stackT OK)
open VG.Proof.Ecdsa.Rfc6979.RISCV64.P224 (p224 p224T_verified)
open VG.Proof.HashTable.RISCV64 (vars tables names)

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P224.curve) : List Artifact :=
  if hv : OK vars ∧ "VG_P224_COMB" ∉ names vars then [
    Spec.Ecdsa.Rfc6979.Curves.p224SignApi.artifact RISCV64.target {
      tables := [("hash", tables vars)]
      code := signCode (p224 h.law) Spec.Ecdsa.Rfc6979.Curves.p224.tries vars
      consts := Impl.Ecdsa.RISCV64.Comb.p224CombConsts
      stack := stackT
      verified := p224T_verified h.law vars hv }]
  else []

end VG.Generic.P224.RISCV64.EcdsaP224Rfc6979
