module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.Secp256k1
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Deterministic ECDSA (RFC 6979) over secp256k1 on RISC-V, with the hash function as a table -/

@[expose] public section

namespace VG.Generic.Secp256k1.RISCV64.EcdsaSecp256k1Rfc6979

open VG.Proof.Ecdsa.Rfc6979.RISCV64 (signCode stackT OK)
open VG.Proof.Ecdsa.Rfc6979.RISCV64.Secp256k1 (secp256k1 secp256k1T_verified)
open VG.Proof.HashTable.RISCV64 (vars tables names)

def artifacts (h : Proof.Weierstrass.HasLaw Spec.Secp256k1.curve) : List Artifact :=
  if hv : OK vars ∧ "VG_SECP256K1_COMB" ∉ names vars then [
    Spec.Ecdsa.Rfc6979.Curves.secp256k1SignApi.artifact RISCV64.target {
      tables := [("hash", tables vars)]
      code := signCode (secp256k1 h.law) Spec.Ecdsa.Rfc6979.Curves.secp256k1.tries vars
      consts := Impl.Ecdsa.RISCV64.Comb.secp256k1CombConsts
      stack := stackT
      verified := secp256k1T_verified h.law vars hv }]
  else []

end VG.Generic.Secp256k1.RISCV64.EcdsaSecp256k1Rfc6979
