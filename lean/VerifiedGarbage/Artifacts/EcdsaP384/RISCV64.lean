module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdsa.RISCV64.Sign
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.P384.SignVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.EcKey.RISCV64.Scrub
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.Scrub
public import VerifiedGarbage.Spec.Ecdsa.P384
public import VerifiedGarbage.Impl.Ecdsa.RISCV64.VerifyComb
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.P384.VerifyVerified
public import VerifiedGarbage.Spec.Ecdsa.Verify.P384
public import VerifiedGarbage.Impl.Ecdsa.RISCV64.VerifyHash
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Ecdsa.RISCV64.P384.SignLit
import VerifiedGarbage.Proof.Ecdsa.RISCV64.P384.VerifyLit
public import VerifiedGarbage.Proof.P384.RISCV64.Law
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.P384
public import VerifiedGarbage.Proof.Variants.MdHash.RISCV64
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubProved

/-! # ECDSA over P-384 (FIPS 186-5) on RISC-V -/

@[expose] public section

-- Deterministic ECDSA (RFC 6979) over P-384 on RISC-V, with HMAC as a table
namespace VG.Artifacts.EcdsaP384.RISCV64.Rfc6979

open VG.Proof.P384.RISCV64 (hasLaw)
open VG.Proof.Ecdsa.Rfc6979.RISCV64 (signCodeT OK)
open VG.Proof.Ecdsa.Rfc6979.RISCV64.P384 (curveT verifiedT)
open VG.Proof.HmacTable.RISCV64 (tables names)

def artifacts : List Artifact :=
  if hv : OK VG.Proof.Variants.MdHash.RISCV64.variants ∧ Impl.Ecdsa.RISCV64.Comb.p384Sym ∉ names VG.Proof.Variants.MdHash.RISCV64.variants then [
    Spec.Ecdsa.Rfc6979.Curves.p384SignApi.artifact RISCV64.target (RISCV64.Scrub.scrubOf {
      tables := [("hmac", tables VG.Proof.Variants.MdHash.RISCV64.variants)]
      code := signCodeT (curveT hasLaw.law) Spec.Ecdsa.Rfc6979.Curves.p384.tries VG.Proof.Variants.MdHash.RISCV64.variants
      verified := verifiedT hasLaw.law VG.Proof.Variants.MdHash.RISCV64.variants hv }
      (Proof.Ecdsa.Rfc6979.RISCV64.Scrub.signOut Spec.Ecdsa.Rfc6979.Curves.p384
        (Proof.Ecdsa.Rfc6979.RISCV64.P384.kit hasLaw.law).K VG.Proof.Variants.MdHash.RISCV64.variants))]
  else []

end VG.Artifacts.EcdsaP384.RISCV64.Rfc6979

namespace VG.Artifacts.EcdsaP384.RISCV64

open VG.Proof.P384.RISCV64 (hasLaw)

def artifacts : List Artifact := [
  Spec.Ecdsa.P384.verifyHashApi.artifact RISCV64.target (RISCV64.Scrub.scrubOf {
    code := Impl.Ecdsa.RISCV64.VerifyHash.verifyHash Spec.Ecdsa.P384.inst.curve.len false
      Impl.Ecdsa.RISCV64.VerifyComb.verifyP384
    verified := Proof.Ecdsa.RISCV64.P384.verifyHash_verified hasLaw.law }
    (Proof.EcKey.RISCV64.Scrub.verifyHashOut _ Impl.Ecdsa.RISCV64.Comb.p384CombConsts _))] ++
  Rfc6979.artifacts

end VG.Artifacts.EcdsaP384.RISCV64
