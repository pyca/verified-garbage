module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.BrainpoolP256r1
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
public import VerifiedGarbage.Proof.BrainpoolP256r1.RISCV64.Law
public import VerifiedGarbage.Proof.Variants.MdHash.RISCV64

/-! # Deterministic ECDSA (RFC 6979) over brainpoolP256r1 on RISC-V, with HMAC as a table -/

@[expose] public section

namespace VG.Artifacts.EcdsaBrainpoolP256r1Rfc6979.RISCV64

open VG.Proof.BrainpoolP256r1.RISCV64 (hasLaw)
open VG.Proof.Ecdsa.Rfc6979.RISCV64 (signCodeT stackT OK)
open VG.Proof.Ecdsa.Rfc6979.RISCV64.BrainpoolP256r1 (curveT verifiedT)
open VG.Proof.HmacTable.RISCV64 (tables names)

def artifactsFor (vs : List Proof.HmacTable.RISCV64.HVar) : List Artifact :=
  if hv : OK vs ∧ Impl.Ecdsa.RISCV64.Comb.brainpoolP256r1Sym ∉ names vs then [
    Spec.Ecdsa.Rfc6979.Curves.brainpoolp256r1SignApi.artifact RISCV64.target {
      tables := [("hmac", tables vs)]
      code := signCodeT (curveT hasLaw.law) Spec.Ecdsa.Rfc6979.Curves.brainpoolp256r1.tries vs
      stack := stackT
      verified := verifiedT hasLaw.law vs hv }]
  else []

def artifacts : List Artifact :=
  artifactsFor VG.Proof.Variants.MdHash.RISCV64.variants

end VG.Artifacts.EcdsaBrainpoolP256r1Rfc6979.RISCV64
