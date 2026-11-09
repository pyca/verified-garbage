module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP512r1.PPC64LE
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Ecdsa.BrainpoolP512r1
public import VerifiedGarbage.Impl.Ecdsa.Verify.BrainpoolP512r1.PPC64LE
public import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.BrainpoolP512r1.Verified
public import VerifiedGarbage.Spec.Ecdsa.Verify.BrainpoolP512r1
public import VerifiedGarbage.Impl.Ecdsa.PPC64LE.VerifyHash
public import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.BrainpoolP512r1.Lit
public import VerifiedGarbage.Proof.BrainpoolP512r1.PPC64LE.Law
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.BrainpoolP512r1
public import VerifiedGarbage.Proof.HmacTable.PPC64LE.Vars
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.BrainpoolP512r1.CombLit

/-! # ECDSA signatures over brainpoolP512r1 (FIPS 186-5 §6.4.1) on PPC64LE -/

@[expose] public section

-- Deterministic ECDSA (RFC 6979) over brainpoolP512r1 on PPC64LE, with HMAC as a table
namespace VG.Artifacts.EcdsaBrainpoolP512r1.PPC64LE.Rfc6979

open VG.Proof.BrainpoolP512r1.PPC64LE (hasLaw)
open VG.Proof.Ecdsa.Rfc6979.PPC64LE (signCodeT stackT OK brainpoolp512r1R brainpoolp512r1T_verified)
open VG.Proof.HmacTable.PPC64LE (vars tables names)

def artifacts : List Artifact :=
  if hv : OK vars ∧ "VG_BRAINPOOLP512R1_COMB" ∉ names vars then [
    Spec.Ecdsa.Rfc6979.Curves.brainpoolp512r1SignApi.artifact PPC64LE.target {
      tables := [("hmac", tables vars)]
      code := signCodeT (brainpoolp512r1R hasLaw.law) Spec.Ecdsa.Rfc6979.Curves.brainpoolp512r1.tries vars
      stack := stackT
      verified := brainpoolp512r1T_verified hasLaw.law vars hv }]
  else []

end VG.Artifacts.EcdsaBrainpoolP512r1.PPC64LE.Rfc6979

namespace VG.Artifacts.EcdsaBrainpoolP512r1.PPC64LE

open VG.Proof.BrainpoolP512r1.PPC64LE (hasLaw)

def artifacts : List Artifact := [
  Spec.Ecdsa.BrainpoolP512r1.verifyHashApi.artifact PPC64LE.target {
    code := Impl.Ecdsa.PPC64LE.VerifyHash.verifyHash Spec.Ecdsa.BrainpoolP512r1.inst.curve.len false
      Impl.Ecdsa.Verify.PPC64LE.verifyBrainpoolP512r1
    stack := 112
    verified := Proof.Ecdsa.Verify.PPC64LE.BrainpoolP512r1.verifyHash_verified hasLaw.law }] ++
  Rfc6979.artifacts

end VG.Artifacts.EcdsaBrainpoolP512r1.PPC64LE
