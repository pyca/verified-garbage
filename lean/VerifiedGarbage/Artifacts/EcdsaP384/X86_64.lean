module

public import VerifiedGarbage.Proof.Framework.X86_64.ScrubUp
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public import VerifiedGarbage.Proof.EcKey.X86_64.Scrub.Out
public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvInterface
public import VerifiedGarbage.Proof.P384.Comb7
public import VerifiedGarbage.Proof.Ecdsa.X86_64.P384.Verified
public import VerifiedGarbage.Proof.Ecdsa.X86_64.P384.Lit
import VerifiedGarbage.Impl.Ecdsa.Verify.P384.X86_64
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.P384.JointVerified
public import VerifiedGarbage.Proof.Ecdsa.X86_64.P384.VerifiedAdx
public import VerifiedGarbage.Proof.Ecdsa.X86_64.P384.LitAdx
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.P384.JointLitAdx
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.P384.JointChecks
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.P384.JointLit
public import VerifiedGarbage.Spec.Ecdsa.Verify.P384
public import VerifiedGarbage.Impl.Ecdsa.X86_64.VerifyHash
public import VerifiedGarbage.Proof.P384.GTable9 -- shake: keep (the artifacts' bodies use `gtabOk9`)
import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Impl.Ecdsa.P384.X86_64
import VerifiedGarbage.Proof.Mont.X86_64.Wide
import VerifiedGarbage.Proof.Weierstrass.X86_64.FieldErase
import VerifiedGarbage.Proof.X25519.X86_64.Adx.MulProd
import VerifiedGarbage.Proof.X25519.X86_64.Adx.SqrProd
public import VerifiedGarbage.Impl.Ecdh.P384.X86_64
public import VerifiedGarbage.Proof.EcKey.PublicKey
public import VerifiedGarbage.Proof.Ecdh.X86_64.Check
public import VerifiedGarbage.Proof.Ecdh.X86_64.Peer
public import VerifiedGarbage.Proof.Ecdsa.Sign
public import VerifiedGarbage.Proof.Ecdsa.Verify
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Final
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointInput
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointMain
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointTail
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.P384.JointCT
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.ProjectiveFlags
public import VerifiedGarbage.Proof.Ecdsa.X86_64.CombLays
public import VerifiedGarbage.Proof.Ecdsa.X86_64.Main
public import VerifiedGarbage.Proof.Ecdsa.X86_64.MulFn
public import VerifiedGarbage.Proof.Ecdsa.X86_64.SharedSlots
public import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
public import VerifiedGarbage.Proof.Framework.X86_64.Lit
public import VerifiedGarbage.Proof.P384.Point
public import VerifiedGarbage.Proof.P384.X86_64.JointLayout
public import VerifiedGarbage.Proof.Weierstrass.CombCheckFast
public import VerifiedGarbage.Proof.Weierstrass.X86_64.Bytes
public import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
public import VerifiedGarbage.Proof.Weierstrass.X86_64.FastNafChoose
public import VerifiedGarbage.Proof.Weierstrass.X86_64.FastNafOdd
public import VerifiedGarbage.Proof.Weierstrass.X86_64.FastNafPrep
public import VerifiedGarbage.Proof.Weierstrass.X86_64.FastNafSubtract
public import VerifiedGarbage.Proof.Weierstrass.X86_64.FprogJ
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JacMixedAdd
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointFixedLoad
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointFixedPoint
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointInitTiming
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointMulTiming
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointPrepTiming
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointSeed
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointTables
public import VerifiedGarbage.Proof.Weierstrass.X86_64.NafTable
public import VerifiedGarbage.Proof.Weierstrass.X86_64.NafTableCopy
public import VerifiedGarbage.Proof.Weierstrass.X86_64.NafTableFields
public import VerifiedGarbage.Proof.Weierstrass.X86_64.NafTableInit
public import VerifiedGarbage.Proof.Weierstrass.X86_64.NafTableStoreTiming
public import VerifiedGarbage.Proof.Weierstrass.X86_64.NafTableTiming
public import VerifiedGarbage.Proof.Weierstrass.X86_64.NafTableTimingStep
public import VerifiedGarbage.Proof.Weierstrass.X86_64.SpillUnch
public import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombJ
public import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombJDigit
public import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombSelectY
public import VerifiedGarbage.Proof.Weierstrass.X86_64.WinLoop
public import VerifiedGarbage.TCB.X86_64.Print
public import VerifiedGarbage.Proof.P384.X86_64.Law
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.P384Adx
public import VerifiedGarbage.Proof.Variants.MdHash.X86_64

/-! # ECDSA over P-384 (FIPS 186-5) on x86-64 -/

@[expose] public section

-- Deterministic ECDSA (RFC 6979) over P-384 on x86-64, with HMAC as a table
namespace VG.Artifacts.EcdsaP384.X86_64.Rfc6979

open VG.Proof.P384.X86_64 (hasLaw)
open VG.Proof.Ecdsa.Rfc6979.X86_64 (signCodeT stackT OK p384Of p384T_verified signCode_sp)
open VG.Proof.HmacTable.X86_64 (tables names)
open VG.Proof.Variants.MdHash.X86_64 (variants)

def artifacts : List Artifact :=
  if hv : OK variants ∧ "VG_P384_COMB" ∉ names variants then [
    Spec.Ecdsa.Rfc6979.Curves.p384SignApi.artifact X86_64.target (X86_64.Scrub.withScrubAllUp {
      tables := [("hmac", tables variants)]
      code := signCodeT (p384Of false hasLaw.law (Proof.P384.combOk7 hasLaw.law) hasLaw.inv)
        Spec.Ecdsa.Rfc6979.Curves.p384.tries variants
      stack := stackT
      verified := p384T_verified false hasLaw.law (Proof.P384.combOk7 hasLaw.law) hasLaw.inv variants hv
      spSafe := signCode_sp _ _ _ } (Proof.Ecdsa.Rfc6979.X86_64.signOut _ Impl.Ecdsa.X86_64.p384.combConsts _ _)),
    Spec.Ecdsa.Rfc6979.Curves.p384SignApi.artifact X86_64.target (X86_64.Scrub.withScrubAllUp {
      suffix := "_adx"
      tables := [("hmac", tables variants)]
      code := signCodeT (p384Of true hasLaw.law (Proof.P384.combOk7 hasLaw.law) hasLaw.inv)
        Spec.Ecdsa.Rfc6979.Curves.p384.tries variants
      stack := stackT
      verified := p384T_verified true hasLaw.law (Proof.P384.combOk7 hasLaw.law) hasLaw.inv variants hv
      spSafe := signCode_sp _ _ _ } (Proof.Ecdsa.Rfc6979.X86_64.signOut _ Impl.Ecdsa.X86_64.p384.combConsts _ _))]
  else []

end VG.Artifacts.EcdsaP384.X86_64.Rfc6979

namespace VG.Artifacts.EcdsaP384.X86_64

open VG.Proof.P384.X86_64 (hasLaw)

def artifacts : List Artifact := [
  Spec.Ecdsa.P384.verifyHashApi.artifact X86_64.target (X86_64.Scrub.withScrubAll {
    code := Impl.Ecdsa.X86_64.VerifyHash.verifyHash Spec.Ecdsa.P384.inst.curve.len false
      Impl.Ecdsa.Verify.X86_64.jointVerifyP384
    stack := 96
    verified := Proof.Ecdsa.Verify.X86_64.P384.verifyHash_verified hasLaw.law (Proof.P384.gtabOk9 hasLaw.law) hasLaw.inv
      hasLaw.prime }
    (Proof.EcKey.X86_64.Scrub.verifyHashOut_consts 96 Spec.Ecdsa.P384.inst Impl.P384.X86_64.p384v.combConsts)),
  Spec.Ecdsa.P384.verifyHashApi.artifact X86_64.target (X86_64.Scrub.withScrubAll {
    suffix := "_adx"
    code := Impl.Ecdsa.X86_64.VerifyHash.verifyHash Spec.Ecdsa.P384.inst.curve.len false
      Impl.Ecdsa.Verify.X86_64.jointVerifyP384Adx
    stack := 96
    verified := Proof.Ecdsa.Verify.X86_64.P384.verifyHash_verified_adx hasLaw.law (Proof.P384.gtabOk9 hasLaw.law)
      hasLaw.inv
      hasLaw.prime }
    (Proof.EcKey.X86_64.Scrub.verifyHashOut_consts 96 Spec.Ecdsa.P384.inst Impl.P384.X86_64.p384v.combConsts))] ++
  Rfc6979.artifacts

end VG.Artifacts.EcdsaP384.X86_64
