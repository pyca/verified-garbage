module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.BrainpoolP256r1
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.HmacTable.PPC64LE.Vars
public import VerifiedGarbage.TCB.PPC64LE.Print
public import VerifiedGarbage.Proof.BrainpoolP256r1.PPC64LE.Law
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.BrainpoolP256r1.CombLit

/-! # Deterministic ECDSA (RFC 6979) over brainpoolP256r1 on PPC64LE, with HMAC as a table -/

@[expose] public section

namespace VG.Artifacts.EcdsaBrainpoolP256r1Rfc6979.PPC64LE

open VG.Proof.BrainpoolP256r1.PPC64LE (hasLaw)
open VG.Proof.Ecdsa.Rfc6979.PPC64LE (signCodeT stackT OK brainpoolp256r1R brainpoolp256r1T_verified)
open VG.Proof.HmacTable.PPC64LE (vars tables names)

def artifacts : List Artifact :=
  if hv : OK vars ∧ "VG_BRAINPOOLP256R1_COMB" ∉ names vars then [
    Spec.Ecdsa.Rfc6979.Curves.brainpoolp256r1SignApi.artifact PPC64LE.target {
      tables := [("hmac", tables vars)]
      code := signCodeT (brainpoolp256r1R hasLaw.law) Spec.Ecdsa.Rfc6979.Curves.brainpoolp256r1.tries vars
      stack := stackT
      verified := brainpoolp256r1T_verified hasLaw.law vars hv }]
  else []

end VG.Artifacts.EcdsaBrainpoolP256r1Rfc6979.PPC64LE
