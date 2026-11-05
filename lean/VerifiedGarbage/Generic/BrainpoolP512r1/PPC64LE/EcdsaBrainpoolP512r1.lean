module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP512r1.PPC64LE
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.BrainpoolP512r1.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Ecdsa.BrainpoolP512r1
public import VerifiedGarbage.Impl.Ecdsa.Verify.BrainpoolP512r1.PPC64LE
public import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.BrainpoolP512r1.Verified
public import VerifiedGarbage.Spec.Ecdsa.Verify.BrainpoolP512r1
public import VerifiedGarbage.Impl.Ecdsa.PPC64LE.VerifyHash
public import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.BrainpoolP512r1.Lit
import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.BrainpoolP512r1.Lit

/-! # ECDSA signatures over brainpoolP512r1 (FIPS 186-5 §6.4.1) on PPC64LE -/

@[expose] public section

namespace VG.Generic.BrainpoolP512r1.PPC64LE.EcdsaBrainpoolP512r1

def artifacts (h : Proof.Weierstrass.HasLaw Spec.BrainpoolP512r1.curve) : List Artifact := [
  Spec.Ecdsa.BrainpoolP512r1.verifyHashApi.artifact PPC64LE.target {
    code := Impl.Ecdsa.PPC64LE.VerifyHash.verifyHash Spec.Ecdsa.BrainpoolP512r1.inst.curve.len false
      Impl.Ecdsa.Verify.PPC64LE.verifyBrainpoolP512r1
    stack := 112
    verified := Proof.Ecdsa.Verify.PPC64LE.BrainpoolP512r1.verifyHash_verified h.law }]

end VG.Generic.BrainpoolP512r1.PPC64LE.EcdsaBrainpoolP512r1
