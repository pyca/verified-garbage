module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.BrainpoolP256r1
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print

/-! # Deterministic ECDSA (RFC 6979) over brainpoolP256r1 on RISC-V, with HMAC as a table -/

@[expose] public section

namespace VG.Generic.BrainpoolP256r1.AllMdHash.RISCV64.EcdsaBrainpoolP256r1Rfc6979

open VG.Proof.Ecdsa.Rfc6979.RISCV64 (signCodeT stackT OK)
open VG.Proof.Ecdsa.Rfc6979.RISCV64.BrainpoolP256r1 (curveT verifiedT)
open VG.Proof.HmacTable.RISCV64 (tables names)

def artifacts (h : Proof.Weierstrass.HasLaw Spec.BrainpoolP256r1.curve)
    (vs : List Proof.HmacTable.RISCV64.HVar) : List Artifact :=
  if hv : OK vs ∧ Impl.Ecdsa.RISCV64.Comb.brainpoolP256r1Sym ∉ names vs then [
    Spec.Ecdsa.Rfc6979.Curves.brainpoolp256r1SignApi.artifact RISCV64.target {
      tables := [("hmac", tables vs)]
      code := signCodeT (curveT h.law) Spec.Ecdsa.Rfc6979.Curves.brainpoolp256r1.tries vs
      consts := Impl.Ecdsa.RISCV64.Comb.brainpoolP256r1CombConsts
      stack := stackT
      verified := verifiedT h.law vs hv }]
  else []

end VG.Generic.BrainpoolP256r1.AllMdHash.RISCV64.EcdsaBrainpoolP256r1Rfc6979
