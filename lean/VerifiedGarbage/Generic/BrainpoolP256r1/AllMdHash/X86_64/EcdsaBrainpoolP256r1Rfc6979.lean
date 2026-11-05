module

public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvInterface
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.BrainpoolP256r1
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find

/-! # Deterministic ECDSA (RFC 6979) over brainpoolP256r1 on x86-64, with HMAC as a table -/

@[expose] public section

namespace VG.Generic.BrainpoolP256r1.AllMdHash.X86_64.EcdsaBrainpoolP256r1Rfc6979

open VG.Proof.Ecdsa.Rfc6979.X86_64 (signCodeT stackT OK brainpoolp256r1 brainpoolp256r1T_verified signCode_sp)
open VG.Proof.HmacTable.X86_64 (tables names)

def artifacts (h : Proof.Weierstrass.X86_64.HasLawInv Spec.BrainpoolP256r1.curve)
    (vs : List Proof.Pbkdf2.Md.X86_64.MdHash) : List Artifact :=
  if hv : OK vs then [
    Spec.Ecdsa.Rfc6979.Curves.brainpoolp256r1SignApi.artifact X86_64.target {
      suffix := ""
      tables := [("hmac", tables vs)]
      code := signCodeT (brainpoolp256r1 h.law h.inv) Spec.Ecdsa.Rfc6979.Curves.brainpoolp256r1.tries vs
      stack := stackT
      verified := brainpoolp256r1T_verified h.law h.inv vs hv
      spSafe := signCode_sp _ _ _
      features := [] }]
  else []

end VG.Generic.BrainpoolP256r1.AllMdHash.X86_64.EcdsaBrainpoolP256r1Rfc6979
