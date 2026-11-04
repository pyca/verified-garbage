module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.P192
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Deterministic ECDSA (RFC 6979) over P-192 on RISC-V, with the hash function as a table -/

@[expose] public section

namespace VG.Generic.P192.RISCV64.EcdsaP192Rfc6979

open VG.Proof.Ecdsa.Rfc6979.RISCV64 (signCode stackT OK)
open VG.Proof.Ecdsa.Rfc6979.RISCV64.P192 (p192 p192T_verified)
open VG.Proof.HashTable.RISCV64 (vars tables names)

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P192.curve) : List Artifact :=
  if hv : OK vars then [
    Spec.Ecdsa.Rfc6979.Curves.p192SignApi.artifact RISCV64.target {
      tables := [("hash", tables vars)]
      code := signCode (p192 h.law) Spec.Ecdsa.Rfc6979.Curves.p192.tries vars
      stack := stackT
      verified := p192T_verified h.law vars hv }]
  else []

end VG.Generic.P192.RISCV64.EcdsaP192Rfc6979
