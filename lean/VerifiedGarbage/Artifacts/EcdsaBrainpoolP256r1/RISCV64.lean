module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.BrainpoolP256r1.SignVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.EcKey.RISCV64.Scrub
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.Scrub
public import VerifiedGarbage.Spec.Ecdsa.BrainpoolP256r1
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP256r1.RISCV64.Ecdsa
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.BrainpoolP256r1.VerifyVerified
public import VerifiedGarbage.Spec.Ecdsa.Verify.BrainpoolP256r1
public import VerifiedGarbage.Impl.Ecdsa.RISCV64.VerifyHash
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Ecdsa.RISCV64.BrainpoolP256r1.SignLit
import VerifiedGarbage.Proof.Ecdsa.RISCV64.BrainpoolP256r1.VerifyLit
public import VerifiedGarbage.Proof.BrainpoolP256r1.RISCV64.Law
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.BrainpoolP256r1
public import VerifiedGarbage.Proof.Variants.MdHash.RISCV64

/-! # ECDSA over brainpoolP256r1 (FIPS 186-5) on RISC-V -/

@[expose] public section

-- Deterministic ECDSA (RFC 6979) over brainpoolP256r1 on RISC-V, with HMAC as a table
namespace VG.Artifacts.EcdsaBrainpoolP256r1.RISCV64.Rfc6979

open VG.Proof.BrainpoolP256r1.RISCV64 (hasLaw)
open VG.Proof.Ecdsa.Rfc6979.RISCV64 (signCodeT OK)
open VG.Proof.Ecdsa.Rfc6979.RISCV64.BrainpoolP256r1 (curveT verifiedT)
open VG.Proof.HmacTable.RISCV64 (tables names)

def artifactsFor (vs : List Proof.HmacTable.RISCV64.HVar) : List Artifact :=
  if hv : OK vs ∧ Impl.Ecdsa.RISCV64.Comb.brainpoolP256r1Sym ∉ names vs then [
    Spec.Ecdsa.Rfc6979.Curves.brainpoolp256r1SignApi.artifact RISCV64.target (RISCV64.Scrub.withScrub {
      tables := [("hmac", tables vs)]
      code := signCodeT (curveT hasLaw.law) Spec.Ecdsa.Rfc6979.Curves.brainpoolp256r1.tries vs
      verified := verifiedT hasLaw.law vs hv }
      (Proof.Ecdsa.Rfc6979.RISCV64.Scrub.signOut Spec.Ecdsa.Rfc6979.Curves.brainpoolp256r1
        (Proof.Ecdsa.Rfc6979.RISCV64.BrainpoolP256r1.kit hasLaw.law).K vs))]
  else []

def artifacts : List Artifact :=
  artifactsFor VG.Proof.Variants.MdHash.RISCV64.variants

end VG.Artifacts.EcdsaBrainpoolP256r1.RISCV64.Rfc6979

namespace VG.Artifacts.EcdsaBrainpoolP256r1.RISCV64

open VG.Proof.BrainpoolP256r1.RISCV64 (hasLaw)

def artifacts : List Artifact := [
  Spec.Ecdsa.BrainpoolP256r1.verifyHashApi.artifact RISCV64.target (RISCV64.Scrub.withScrub {
    code := Impl.Ecdsa.RISCV64.VerifyHash.verifyHash Spec.Ecdsa.BrainpoolP256r1.inst.curve.len false
      Impl.Ecdsa.RISCV64.verifyBrainpoolP256r1
    verified := Proof.Ecdsa.RISCV64.BrainpoolP256r1.verifyHash_verified hasLaw.law }
    (Proof.EcKey.RISCV64.Scrub.verifyHashOut _ Impl.Ecdsa.RISCV64.Comb.brainpoolP256r1CombConsts _))] ++
  Rfc6979.artifacts

end VG.Artifacts.EcdsaBrainpoolP256r1.RISCV64
