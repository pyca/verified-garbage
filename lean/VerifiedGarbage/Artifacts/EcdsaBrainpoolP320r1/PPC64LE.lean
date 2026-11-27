module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ecdsa.Verify.BrainpoolP320r1
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Impl.Ecdsa.BrainpoolP320r1.PPC64LE
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Spec.Ecdsa.BrainpoolP320r1
import VerifiedGarbage.Impl.Ecdsa.Verify.BrainpoolP320r1.PPC64LE
import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.BrainpoolP320r1.Verified
import VerifiedGarbage.Impl.Ecdsa.PPC64LE.VerifyHash
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Scrub
import VerifiedGarbage.Impl.Ecdsa.Rfc6979.PPC64LE.Fn
import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.Scrub
import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.BrainpoolP320r1.Lit
import VerifiedGarbage.Proof.BrainpoolP320r1.PPC64LE.Law
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.BrainpoolP320r1
import VerifiedGarbage.Proof.HmacTable.PPC64LE.Vars
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.BrainpoolP320r1.CombLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # ECDSA over brainpoolP320r1 (FIPS 186-5) on PPC64LE -/

namespace VG.Artifacts.EcdsaBrainpoolP320r1.PPC64LE

open VG.Proof.Ecdsa.Rfc6979.PPC64LE (OK)
open VG.Proof.HmacTable.PPC64LE (vars names tables fnsOf)

open VG.Proof.BrainpoolP320r1.PPC64LE (hasLaw)

public def artifacts : List (Artifact PPC64LE.target) := [
  Spec.Ecdsa.BrainpoolP320r1.verifyHashApi.artifact PPC64LE.target {
    code := Impl.Ecdsa.Verify.PPC64LE.Fn.brainpoolp320r1Verify
    verified := Proof.Ecdsa.Verify.PPC64LE.Scrub.brainpoolp320r1Verify_scrubbed hasLaw.law }] ++
  (if hv : OK vars ∧ "VG_BRAINPOOLP320R1_COMB" ∉ names vars ∧ "VG_BRAINPOOLP320R1_FRAME_CONSTS" ∉ names vars then [
    Spec.Ecdsa.Rfc6979.Curves.brainpoolp320r1SignApi.artifact PPC64LE.target {
      tables := [("hmac", tables vars)]
      code := Impl.Ecdsa.Rfc6979.PPC64LE.Fn.brainpoolp320r1 (fnsOf vars)
      verified := Proof.Ecdsa.Rfc6979.PPC64LE.Scrub.brainpoolp320r1Sign_scrubbed hasLaw.law hv }]
  else [])

spec_apis artifacts

end VG.Artifacts.EcdsaBrainpoolP320r1.PPC64LE
