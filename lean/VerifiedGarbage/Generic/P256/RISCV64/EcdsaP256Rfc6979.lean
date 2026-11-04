module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.P256
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Deterministic ECDSA (RFC 6979) over P-256 on RISC-V, with the hash function as a table -/

@[expose] public section

namespace VG.Generic.P256.RISCV64.EcdsaP256Rfc6979

open VG.Proof.Ecdsa.Rfc6979.RISCV64 (signCode stackT OK)
open VG.Proof.Ecdsa.Rfc6979.RISCV64.P256 (p256 p256T_verified)
open VG.Proof.HashTable.RISCV64 (vars tables names)

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P256.curve) : List Artifact :=
  if hv : OK vars ∧ "VG_P256_COMB" ∉ names vars then [
    Spec.Ecdsa.Rfc6979.Curves.p256SignApi.artifact RISCV64.target {
      tables := [("hash", tables vars)]
      code := signCode (p256 h.law) Spec.Ecdsa.Rfc6979.Curves.p256.tries vars
      consts := Impl.Ecdsa.RISCV64.Comb.p256CombConsts
      stack := stackT
      verified := p256T_verified h.law vars hv }]
  else []

end VG.Generic.P256.RISCV64.EcdsaP256Rfc6979
