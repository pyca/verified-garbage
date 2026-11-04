module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.P384
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Deterministic ECDSA (RFC 6979) over P-384 on RISC-V, with the hash function as a table -/

@[expose] public section

namespace VG.Generic.P384.RISCV64.EcdsaP384Rfc6979

open VG.Proof.Ecdsa.Rfc6979.RISCV64 (signCode stackT OK)
open VG.Proof.Ecdsa.Rfc6979.RISCV64.P384 (p384 p384T_verified)
open VG.Proof.HashTable.RISCV64 (vars tables names)

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P384.curve) : List Artifact :=
  if hv : OK vars ∧ "VG_P384_COMB" ∉ names vars then [
    Spec.Ecdsa.Rfc6979.Curves.p384SignApi.artifact RISCV64.target {
      tables := [("hash", tables vars)]
      code := signCode (p384 h.law) Spec.Ecdsa.Rfc6979.Curves.p384.tries vars
      consts := Impl.Ecdsa.RISCV64.Comb.p384CombConsts
      stack := stackT
      verified := p384T_verified h.law vars hv }]
  else []

end VG.Generic.P384.RISCV64.EcdsaP384Rfc6979
