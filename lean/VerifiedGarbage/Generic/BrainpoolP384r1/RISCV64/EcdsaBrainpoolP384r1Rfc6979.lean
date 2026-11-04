module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.BrainpoolP384r1
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Deterministic ECDSA (RFC 6979) over brainpoolP384r1 on RISC-V, with the hash function as a table -/

@[expose] public section

namespace VG.Generic.BrainpoolP384r1.RISCV64.EcdsaBrainpoolP384r1Rfc6979

open VG.Proof.Ecdsa.Rfc6979.RISCV64 (signCode stackT OK)
open VG.Proof.Ecdsa.Rfc6979.RISCV64.BrainpoolP384r1 (brainpoolp384r1 brainpoolp384r1T_verified)
open VG.Proof.HashTable.RISCV64 (vars tables names)

def artifacts (h : Proof.Weierstrass.HasLaw Spec.BrainpoolP384r1.curve) : List Artifact :=
  if hv : OK vars then [
    Spec.Ecdsa.Rfc6979.Curves.brainpoolp384r1SignApi.artifact RISCV64.target {
      tables := [("hash", tables vars)]
      code := signCode (brainpoolp384r1 h.law) Spec.Ecdsa.Rfc6979.Curves.brainpoolp384r1.tries vars
      stack := stackT
      verified := brainpoolp384r1T_verified h.law vars hv }]
  else []

end VG.Generic.BrainpoolP384r1.RISCV64.EcdsaBrainpoolP384r1Rfc6979
