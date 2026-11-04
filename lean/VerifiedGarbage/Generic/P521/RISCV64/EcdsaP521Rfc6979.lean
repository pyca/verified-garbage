module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.P521
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Deterministic ECDSA (RFC 6979) over P-521 on RISC-V, with the hash function as a table -/

@[expose] public section

namespace VG.Generic.P521.RISCV64.EcdsaP521Rfc6979

open VG.Proof.Ecdsa.Rfc6979.RISCV64 (signCode stackT OK)
open VG.Proof.Ecdsa.Rfc6979.RISCV64.P521 (p521 p521T_verified)
open VG.Proof.HashTable.RISCV64 (vars tables names)

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P521.curve) : List Artifact :=
  if hv : OK vars then [
    Spec.Ecdsa.Rfc6979.Curves.p521SignApi.artifact RISCV64.target {
      tables := [("hash", tables vars)]
      code := signCode (p521 h.law) Spec.Ecdsa.Rfc6979.Curves.p521.tries vars
      stack := stackT
      verified := p521T_verified h.law vars hv }]
  else []

end VG.Generic.P521.RISCV64.EcdsaP521Rfc6979
