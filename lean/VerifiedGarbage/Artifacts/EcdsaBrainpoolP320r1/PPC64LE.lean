module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP320r1.PPC64LE
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Ecdsa.BrainpoolP320r1
public import VerifiedGarbage.Impl.Ecdsa.Verify.BrainpoolP320r1.PPC64LE
public import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.BrainpoolP320r1.Verified
public import VerifiedGarbage.Spec.Ecdsa.Verify.BrainpoolP320r1
public import VerifiedGarbage.Impl.Ecdsa.PPC64LE.VerifyHash
public import VerifiedGarbage.TCB.PPC64LE.Print
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Scrub
public import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.Scrub
import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.BrainpoolP320r1.Lit
public import VerifiedGarbage.Proof.BrainpoolP320r1.PPC64LE.Law
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.BrainpoolP320r1
public import VerifiedGarbage.Proof.HmacTable.PPC64LE.Vars
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.BrainpoolP320r1.CombLit

/-! # ECDSA over brainpoolP320r1 (FIPS 186-5) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.EcdsaBrainpoolP320r1.PPC64LE

open VG.Proof.Ecdsa.Rfc6979.PPC64LE (OK)
open VG.Proof.HmacTable.PPC64LE (vars names)

open VG.Proof.BrainpoolP320r1.PPC64LE (hasLaw)

def artifacts : List Artifact := [
  Spec.Ecdsa.BrainpoolP320r1.verifyHashApi.artifact PPC64LE.target {
    code := Impl.Ecdsa.Verify.PPC64LE.Fn.brainpoolp320r1Verify
    verified := .scrubbed (Proof.Ecdsa.Verify.PPC64LE.Scrub.brainpoolp320r1Verify_scrubbed hasLaw.law) }] ++
  (if hv : OK vars ∧ "VG_BRAINPOOLP320R1_COMB" ∉ names vars then [
    Spec.Ecdsa.Rfc6979.Curves.brainpoolp320r1SignApi.artifact PPC64LE.target
      (Proof.Ecdsa.Rfc6979.PPC64LE.Scrub.brainpoolp320r1Sign hasLaw.law hv)]
  else [])

end VG.Artifacts.EcdsaBrainpoolP320r1.PPC64LE
