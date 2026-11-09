module

public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvInterface
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.BrainpoolP256r1
public import VerifiedGarbage.TCB.X86_64.Print
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
public import VerifiedGarbage.Proof.BrainpoolP256r1.X86_64.Law
public import VerifiedGarbage.Proof.Variants.MdHash.X86_64

/-! # Deterministic ECDSA (RFC 6979) over brainpoolP256r1 on x86-64, with HMAC as a table -/

@[expose] public section

namespace VG.Artifacts.EcdsaBrainpoolP256r1Rfc6979.X86_64

open VG.Proof.BrainpoolP256r1.X86_64 (hasLaw)
open VG.Proof.Ecdsa.Rfc6979.X86_64 (signCodeT stackT OK brainpoolp256r1 brainpoolp256r1T_verified signCode_sp)
open VG.Proof.HmacTable.X86_64 (tables names)

def artifactsFor (vs : List Proof.Pbkdf2.Md.X86_64.MdHash) : List Artifact :=
  if hv : OK vs ∧ "VG_BRAINPOOLP256R1_COMB" ∉ names vs then [
    Spec.Ecdsa.Rfc6979.Curves.brainpoolp256r1SignApi.artifact X86_64.target {
      suffix := ""
      tables := [("hmac", tables vs)]
      code := signCodeT (brainpoolp256r1 hasLaw.law hasLaw.inv) Spec.Ecdsa.Rfc6979.Curves.brainpoolp256r1.tries vs
      stack := stackT
      verified := brainpoolp256r1T_verified hasLaw.law hasLaw.inv vs hv
      spSafe := signCode_sp _ _ _
      features := [] }]
  else []

def artifacts : List Artifact :=
  artifactsFor VG.Proof.Variants.MdHash.X86_64.variants

end VG.Artifacts.EcdsaBrainpoolP256r1Rfc6979.X86_64
