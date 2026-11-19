module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.Secp256k1.SignVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.EcKey.RISCV64.Scrub
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.Scrub
public import VerifiedGarbage.Spec.Ecdsa.Secp256k1
public import VerifiedGarbage.Impl.Ecdsa.Secp256k1.RISCV64.Ecdsa
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.Secp256k1.VerifyVerified
public import VerifiedGarbage.Spec.Ecdsa.Verify.Secp256k1
public import VerifiedGarbage.Impl.Ecdsa.RISCV64.VerifyHash
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Ecdsa.RISCV64.Secp256k1.SignLit
import VerifiedGarbage.Proof.Ecdsa.RISCV64.Secp256k1.VerifyLit
public import VerifiedGarbage.Proof.Secp256k1.RISCV64.Law
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.Secp256k1
public import VerifiedGarbage.Proof.Variants.MdHash.RISCV64
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubProved

/-! # ECDSA over secp256k1 (FIPS 186-5) on RISC-V -/

@[expose] public section

-- Deterministic ECDSA (RFC 6979) over secp256k1 on RISC-V, with HMAC as a table
namespace VG.Artifacts.EcdsaSecp256k1.RISCV64.Rfc6979

open VG.Proof.Secp256k1.RISCV64 (hasLaw)
open VG.Proof.Ecdsa.Rfc6979.RISCV64 (signCodeT OK)
open VG.Proof.Ecdsa.Rfc6979.RISCV64.Secp256k1 (curveT verifiedT)
open VG.Proof.HmacTable.RISCV64 (tables names)

def artifacts : List Artifact :=
  if hv : OK VG.Proof.Variants.MdHash.RISCV64.variants ∧ Impl.Ecdsa.RISCV64.Comb.secp256k1Sym ∉ names VG.Proof.Variants.MdHash.RISCV64.variants then [
    Spec.Ecdsa.Rfc6979.Curves.secp256k1SignApi.artifact RISCV64.target (RISCV64.Scrub.scrubOf {
      tables := [("hmac", tables VG.Proof.Variants.MdHash.RISCV64.variants)]
      code := signCodeT (curveT hasLaw.law) Spec.Ecdsa.Rfc6979.Curves.secp256k1.tries VG.Proof.Variants.MdHash.RISCV64.variants
      verified := verifiedT hasLaw.law VG.Proof.Variants.MdHash.RISCV64.variants hv }
      (Proof.Ecdsa.Rfc6979.RISCV64.Scrub.signOut Spec.Ecdsa.Rfc6979.Curves.secp256k1
        (Proof.Ecdsa.Rfc6979.RISCV64.Secp256k1.kit hasLaw.law).K VG.Proof.Variants.MdHash.RISCV64.variants))]
  else []

end VG.Artifacts.EcdsaSecp256k1.RISCV64.Rfc6979

namespace VG.Artifacts.EcdsaSecp256k1.RISCV64

open VG.Proof.Secp256k1.RISCV64 (hasLaw)

def artifacts : List Artifact := [
  Spec.Ecdsa.Secp256k1.verifyHashApi.artifact RISCV64.target (RISCV64.Scrub.scrubOf {
    code := Impl.Ecdsa.RISCV64.VerifyHash.verifyHash Spec.Ecdsa.Secp256k1.inst.curve.len false
      Impl.Ecdsa.RISCV64.verifySecp256k1
    verified := Proof.Ecdsa.RISCV64.Secp256k1.verifyHash_verified hasLaw.law }
    (Proof.EcKey.RISCV64.Scrub.verifyHashOut _ Impl.Ecdsa.RISCV64.Comb.secp256k1CombConsts _))] ++
  Rfc6979.artifacts

end VG.Artifacts.EcdsaSecp256k1.RISCV64
