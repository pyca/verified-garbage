module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdsa.P224.PPC64LE
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Ecdsa.P224
public import VerifiedGarbage.Impl.Ecdsa.Verify.P224.PPC64LE
public import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.P224.Verified
public import VerifiedGarbage.Spec.Ecdsa.Verify.P224
public import VerifiedGarbage.Impl.Ecdsa.PPC64LE.VerifyHash
public import VerifiedGarbage.TCB.PPC64LE.Print
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Scrub
public import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.Scrub
import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.P224.Lit
public import VerifiedGarbage.Proof.P224.PPC64LE.Law
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.P224
public import VerifiedGarbage.Proof.HmacTable.PPC64LE.Vars
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P224.CombLit

/-! # ECDSA over P-224 (FIPS 186-5) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.EcdsaP224.PPC64LE

open VG.Proof.Ecdsa.Rfc6979.PPC64LE (OK)
open VG.Proof.HmacTable.PPC64LE (vars names)

open VG.Proof.P224.PPC64LE (hasLaw)

def artifacts : List Artifact := [
  Spec.Ecdsa.P224.verifyHashApi.artifact PPC64LE.target
    (Proof.Ecdsa.Verify.PPC64LE.Scrub.p224Verify hasLaw.law)] ++
  (if hv : OK vars ∧ "VG_P224_COMB" ∉ names vars then [
    Spec.Ecdsa.Rfc6979.Curves.p224SignApi.artifact PPC64LE.target
      (Proof.Ecdsa.Rfc6979.PPC64LE.Scrub.p224Sign hasLaw.law hv)]
  else [])

end VG.Artifacts.EcdsaP224.PPC64LE
