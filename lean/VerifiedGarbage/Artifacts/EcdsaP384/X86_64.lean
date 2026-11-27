module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ecdsa.Verify.P384
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
import VerifiedGarbage.Proof.Framework.X86_64.ScrubUp
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Scrub
import VerifiedGarbage.Proof.Framework.X86_64.Scrub
import VerifiedGarbage.Proof.EcKey.X86_64.Scrub.Out
import VerifiedGarbage.Proof.Weierstrass.X86_64.InvInterface
import VerifiedGarbage.Proof.P384.Comb7
import VerifiedGarbage.Proof.Ecdsa.X86_64.P384.Verified
import VerifiedGarbage.Proof.Ecdsa.X86_64.P384.Lit
import VerifiedGarbage.Impl.Ecdsa.Verify.P384.X86_64
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.P384.JointVerified
import VerifiedGarbage.Proof.Ecdsa.X86_64.P384.VerifiedAdx
import VerifiedGarbage.Proof.Ecdsa.X86_64.P384.LitAdx
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.P384.JointLitAdx
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.P384.JointChecks
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.P384.JointLit
import VerifiedGarbage.Impl.Ecdsa.X86_64.VerifyHash
import VerifiedGarbage.Proof.P384.GTable9
import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Impl.Ecdsa.P384.X86_64
import VerifiedGarbage.Proof.Mont.X86_64.Wide
import VerifiedGarbage.Proof.Weierstrass.X86_64.FieldErase
import VerifiedGarbage.Proof.X25519.X86_64.Adx.MulProd
import VerifiedGarbage.Proof.X25519.X86_64.Adx.SqrProd
import VerifiedGarbage.Impl.Ecdh.P384.X86_64
import VerifiedGarbage.Proof.EcKey.PublicKey
import VerifiedGarbage.Proof.Ecdh.X86_64.Check
import VerifiedGarbage.Proof.Ecdh.X86_64.Peer
import VerifiedGarbage.Proof.Ecdsa.Sign
import VerifiedGarbage.Proof.Ecdsa.Verify
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Final
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointInput
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointMain
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointTail
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.P384.JointCT
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.ProjectiveFlags
import VerifiedGarbage.Proof.Ecdsa.X86_64.CombLays
import VerifiedGarbage.Proof.Ecdsa.X86_64.Main
import VerifiedGarbage.Proof.Ecdsa.X86_64.MulFn
import VerifiedGarbage.Proof.Ecdsa.X86_64.SharedSlots
import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.P384.Point
import VerifiedGarbage.Proof.P384.X86_64.JointLayout
import VerifiedGarbage.Proof.Weierstrass.CombCheckFast
import VerifiedGarbage.Proof.Weierstrass.X86_64.Bytes
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import VerifiedGarbage.Proof.Weierstrass.X86_64.FastNafChoose
import VerifiedGarbage.Proof.Weierstrass.X86_64.FastNafOdd
import VerifiedGarbage.Proof.Weierstrass.X86_64.FastNafPrep
import VerifiedGarbage.Proof.Weierstrass.X86_64.FastNafSubtract
import VerifiedGarbage.Proof.Weierstrass.X86_64.FprogJ
import VerifiedGarbage.Proof.Weierstrass.X86_64.JacMixedAdd
import VerifiedGarbage.Proof.Weierstrass.X86_64.JointFixedLoad
import VerifiedGarbage.Proof.Weierstrass.X86_64.JointFixedPoint
import VerifiedGarbage.Proof.Weierstrass.X86_64.JointInitTiming
import VerifiedGarbage.Proof.Weierstrass.X86_64.JointMulTiming
import VerifiedGarbage.Proof.Weierstrass.X86_64.JointPrepTiming
import VerifiedGarbage.Proof.Weierstrass.X86_64.JointSeed
import VerifiedGarbage.Proof.Weierstrass.X86_64.JointTables
import VerifiedGarbage.Proof.Weierstrass.X86_64.NafTable
import VerifiedGarbage.Proof.Weierstrass.X86_64.NafTableCopy
import VerifiedGarbage.Proof.Weierstrass.X86_64.NafTableFields
import VerifiedGarbage.Proof.Weierstrass.X86_64.NafTableInit
import VerifiedGarbage.Proof.Weierstrass.X86_64.NafTableStoreTiming
import VerifiedGarbage.Proof.Weierstrass.X86_64.NafTableTiming
import VerifiedGarbage.Proof.Weierstrass.X86_64.NafTableTimingStep
import VerifiedGarbage.Proof.Weierstrass.X86_64.SpillUnch
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombJ
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombJDigit
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombSelectY
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinLoop
import VerifiedGarbage.Proof.P384.X86_64.Law
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.P384Adx
import VerifiedGarbage.Proof.Variants.MdHash.X86_64
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # ECDSA over P-384 (FIPS 186-5) on x86-64 -/

-- Deterministic ECDSA (RFC 6979) over P-384 on x86-64, with HMAC as a table
namespace VG.Artifacts.EcdsaP384.X86_64.Rfc6979

open VG.Proof.P384.X86_64 (hasLaw)
open VG.Proof.Ecdsa.Rfc6979.X86_64 (signCodeT OK p384Of p384T_verified signCode_sp)
open VG.Proof.HmacTable.X86_64 (tables names)
open VG.Proof.Variants.MdHash.X86_64 (variants)

def artifacts : List (Artifact X86_64.target) :=
  if hv : OK variants ∧ "VG_P384_COMB" ∉ names variants then [
    Spec.Ecdsa.Rfc6979.Curves.p384SignApi.artifact X86_64.target
      { tables := [("hmac", tables variants)]
        code := Impl.Ecdsa.Rfc6979.X86_64.Fn.sign (Proof.Ecdsa.Rfc6979.X86_64.cfgT (p384Of false hasLaw.law (Proof.P384.combOk7 hasLaw.law) hasLaw.inv) Spec.Ecdsa.Rfc6979.Curves.p384.tries variants)
        verified := Proof.Ecdsa.Rfc6979.X86_64.p384T_scrubbed false hasLaw.law (Proof.P384.combOk7 hasLaw.law) hasLaw.inv variants hv Proof.HmacTable.X86_64.variants_up
        spSafe := Proof.Ecdsa.Rfc6979.X86_64.p384T_spSafe false hasLaw.law (Proof.P384.combOk7 hasLaw.law) hasLaw.inv variants },
    Spec.Ecdsa.Rfc6979.Curves.p384SignApi.artifact X86_64.target
      { suffix := "_adx"
        tables := [("hmac", tables variants)]
        code := Impl.Ecdsa.Rfc6979.X86_64.Fn.sign (Proof.Ecdsa.Rfc6979.X86_64.cfgT (p384Of true hasLaw.law (Proof.P384.combOk7 hasLaw.law) hasLaw.inv) Spec.Ecdsa.Rfc6979.Curves.p384.tries variants)
        verified := Proof.Ecdsa.Rfc6979.X86_64.p384T_scrubbed true hasLaw.law (Proof.P384.combOk7 hasLaw.law) hasLaw.inv variants hv Proof.HmacTable.X86_64.variants_up
        spSafe := Proof.Ecdsa.Rfc6979.X86_64.p384T_spSafe true hasLaw.law (Proof.P384.combOk7 hasLaw.law) hasLaw.inv variants }]
  else []

end VG.Artifacts.EcdsaP384.X86_64.Rfc6979

namespace VG.Artifacts.EcdsaP384.X86_64

open VG.Proof.P384.X86_64 (hasLaw)

public def artifacts : List (Artifact X86_64.target) := [
  Spec.Ecdsa.P384.verifyHashApi.artifact X86_64.target
    { code := Impl.Ecdsa.X86_64.VerifyHash.Fn.verifyHash Spec.Ecdsa.P384.inst.curve.len false Impl.Ecdsa.Verify.X86_64.jointVerifyP384 104
      verified := Proof.Ecdsa.Verify.X86_64.P384.verifyHash_scrubbed hasLaw.law (Proof.P384.gtabOk9 hasLaw.law) hasLaw.inv hasLaw.prime
      spSafe := Proof.Ecdsa.Verify.X86_64.P384.verifyHash_spSafe },
  Spec.Ecdsa.P384.verifyHashApi.artifact X86_64.target
    { suffix := "_adx"
      code := Impl.Ecdsa.X86_64.VerifyHash.Fn.verifyHash Spec.Ecdsa.P384.inst.curve.len false Impl.Ecdsa.Verify.X86_64.jointVerifyP384Adx 104
      verified := Proof.Ecdsa.Verify.X86_64.P384.verifyHashAdx_scrubbed hasLaw.law (Proof.P384.gtabOk9 hasLaw.law) hasLaw.inv hasLaw.prime
      spSafe := Proof.Ecdsa.Verify.X86_64.P384.verifyHashAdx_spSafe }] ++
  Rfc6979.artifacts

spec_apis artifacts

end VG.Artifacts.EcdsaP384.X86_64
