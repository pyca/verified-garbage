module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdsa.RISCV64.P521
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.EcKey.RISCV64.Scrub
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.Scrub
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.P521.VerifyVerified
public import VerifiedGarbage.Spec.Ecdsa.Verify.P521
public import VerifiedGarbage.Impl.Ecdsa.RISCV64.VerifyHash
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Ecdsa.RISCV64.P521.VerifyLit
public import VerifiedGarbage.Proof.P521.RISCV64.Law
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.P521
public import VerifiedGarbage.Proof.Variants.MdHash.RISCV64
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubProved

/-! # ECDSA over P-521 (FIPS 186-5) on RISC-V -/

@[expose] public section

-- Deterministic ECDSA (RFC 6979) over P-521 on RISC-V, with HMAC as a table
namespace VG.Artifacts.EcdsaP521.RISCV64.Rfc6979

open VG.Proof.P521.RISCV64 (hasLaw)
open VG.Proof.Ecdsa.Rfc6979.RISCV64 (signCodeT OK)
open VG.Proof.Ecdsa.Rfc6979.RISCV64.P521 (curveT verifiedT)
open VG.Proof.HmacTable.RISCV64 (tables names)

def artifacts : List Artifact :=
  if hv : OK VG.Proof.Variants.MdHash.RISCV64.variants ∧ Impl.Ecdsa.RISCV64.CombU.p521Sym ∉ names VG.Proof.Variants.MdHash.RISCV64.variants then [
    Spec.Ecdsa.Rfc6979.Curves.p521SignApi.artifact RISCV64.target (RISCV64.Scrub.scrubOf {
      tables := [("hmac", tables VG.Proof.Variants.MdHash.RISCV64.variants)]
      code := signCodeT (curveT hasLaw.law) Spec.Ecdsa.Rfc6979.Curves.p521.tries VG.Proof.Variants.MdHash.RISCV64.variants
      verified := verifiedT hasLaw.law VG.Proof.Variants.MdHash.RISCV64.variants hv }
      (Proof.Ecdsa.Rfc6979.RISCV64.Scrub.signOut Spec.Ecdsa.Rfc6979.Curves.p521
        (Proof.Ecdsa.Rfc6979.RISCV64.P521.kit hasLaw.law).K VG.Proof.Variants.MdHash.RISCV64.variants))]
  else []

end VG.Artifacts.EcdsaP521.RISCV64.Rfc6979

namespace VG.Artifacts.EcdsaP521.RISCV64

open VG.Proof.P521.RISCV64 (hasLaw)

def artifacts : List Artifact := [
  Spec.Ecdsa.P521.verifyHashApi.artifact RISCV64.target (RISCV64.Scrub.scrubOf {
    code := Impl.Ecdsa.RISCV64.VerifyHash.verifyHash Spec.Ecdsa.P521.inst.curve.len true
      Impl.Ecdsa.RISCV64.P521.verifyP521
    verified := Proof.Ecdsa.RISCV64.P521.verifyHash_verified hasLaw.law }
    (Proof.EcKey.RISCV64.Scrub.verifyHashOut _ Impl.Ecdsa.RISCV64.CombU.p521CombConsts _))] ++
  Rfc6979.artifacts

end VG.Artifacts.EcdsaP521.RISCV64
