module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP384r1.PPC64LE
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.BrainpoolP384r1.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Ecdsa.BrainpoolP384r1
public import VerifiedGarbage.Impl.Ecdsa.Verify.BrainpoolP384r1.PPC64LE
public import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.BrainpoolP384r1.Verified
public import VerifiedGarbage.Spec.Ecdsa.Verify.BrainpoolP384r1
public import VerifiedGarbage.Impl.Ecdsa.PPC64LE.VerifyHash
public import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.BrainpoolP384r1.Lit
import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.BrainpoolP384r1.Lit

/-! # ECDSA signatures over brainpoolP384r1 (FIPS 186-5 §6.4.1) on PPC64LE -/

@[expose] public section

namespace VG.Generic.BrainpoolP384r1.PPC64LE.EcdsaBrainpoolP384r1

def artifacts (h : Proof.Weierstrass.HasLaw Spec.BrainpoolP384r1.curve) : List Artifact := [
  Spec.Ecdsa.BrainpoolP384r1.verifyHashApi.artifact PPC64LE.target {
    code := Impl.Ecdsa.PPC64LE.VerifyHash.verifyHash Spec.Ecdsa.BrainpoolP384r1.inst.curve.len false
      Impl.Ecdsa.Verify.PPC64LE.verifyBrainpoolP384r1
    stack := 112
    verified := Proof.Ecdsa.Verify.PPC64LE.BrainpoolP384r1.verifyHash_verified h.law }]

end VG.Generic.BrainpoolP384r1.PPC64LE.EcdsaBrainpoolP384r1
