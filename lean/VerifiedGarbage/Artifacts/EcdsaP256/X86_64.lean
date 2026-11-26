module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ecdsa.Verify.P256
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
import VerifiedGarbage.Proof.Framework.X86_64.ScrubUp
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Scrub
import VerifiedGarbage.Proof.EcKey.X86_64.Scrub.Out
import VerifiedGarbage.Proof.Weierstrass.X86_64.InvInterface
import VerifiedGarbage.Proof.P256.Comb7
import VerifiedGarbage.Proof.Ecdsa.X86_64.Verified
import VerifiedGarbage.Proof.Ecdsa.X86_64.Lit
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Lit
import VerifiedGarbage.Proof.Ecdsa.X86_64.VerifiedAdx
import VerifiedGarbage.Proof.Ecdsa.X86_64.LitAdx
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointVerified
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointIfmaVerified
import VerifiedGarbage.Proof.Framework.X86_64.Scrub
import VerifiedGarbage.Proof.Framework.X86_64.ScrubOr
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointIfmaLit
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.LitAdx
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointLit
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.LitErase
import VerifiedGarbage.Impl.Ecdsa.X86_64.VerifyHash
import VerifiedGarbage.Proof.P256.GTable9
import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Impl.Ecdsa.P256.X86_64
import VerifiedGarbage.Impl.Ecdsa.Verify.P256.X86_64
import VerifiedGarbage.Proof.Mont.X86_64.Wide
import VerifiedGarbage.Proof.Weierstrass.X86_64.JointCachedDigitTiming
import VerifiedGarbage.Proof.Weierstrass.X86_64.JointDoubler
import VerifiedGarbage.Proof.Weierstrass.X86_64.JointFixedDigitTiming
import VerifiedGarbage.Proof.X25519.X86_64.Adx.MulProd
import VerifiedGarbage.Proof.X25519.X86_64.Adx.SqrProd
import VerifiedGarbage.Impl.Ecdh.P256.X86_64
import VerifiedGarbage.Proof.EcKey.PublicKey
import VerifiedGarbage.Proof.Ecdh.X86_64.Check
import VerifiedGarbage.Proof.Ecdh.X86_64.Peer
import VerifiedGarbage.Proof.Ecdsa.Sign
import VerifiedGarbage.Proof.Ecdsa.Verify
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Final
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointAbi
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.ProjectiveFinal
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.ProjectiveFlags
import VerifiedGarbage.Proof.Ecdsa.X86_64.CombLays
import VerifiedGarbage.Proof.Ecdsa.X86_64.MulFn
import VerifiedGarbage.Proof.Ecdsa.X86_64.SharedSlots
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.BitByte
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Pratt
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Bswap
import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Inline
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Mont.Words128
import VerifiedGarbage.Proof.Mont.X86_64.Blocks
import VerifiedGarbage.Proof.Mont.X86_64.CsubS
import VerifiedGarbage.Proof.Mont.X86_64.Friendly
import VerifiedGarbage.Proof.Mont.X86_64.Ops
import VerifiedGarbage.Proof.Mont.X86_64.Round
import VerifiedGarbage.Proof.Mont.X86_64.Sparse
import VerifiedGarbage.Proof.Mont.X86_64.SparseX
import VerifiedGarbage.Proof.Mont.X86_64.SqrPX
import VerifiedGarbage.Proof.Mont.X86_64.WideOps
import VerifiedGarbage.Proof.P256.Order
import VerifiedGarbage.Proof.P256.Point
import VerifiedGarbage.Proof.P256.Prime
import VerifiedGarbage.Proof.Weierstrass.CombCheckFast
import VerifiedGarbage.Proof.Weierstrass.TCombWords
import VerifiedGarbage.Proof.Weierstrass.X86_64.Bytes
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import VerifiedGarbage.Proof.Weierstrass.X86_64.Copy
import VerifiedGarbage.Proof.Weierstrass.X86_64.FprogJ
import VerifiedGarbage.Proof.Weierstrass.X86_64.Loop
import VerifiedGarbage.Proof.Weierstrass.X86_64.MontCall
import VerifiedGarbage.Proof.Weierstrass.X86_64.MontWide8
import VerifiedGarbage.Proof.Weierstrass.X86_64.SpillUnch
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombJ
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombJDigit
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombSelectY
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinLoop
import VerifiedGarbage.Proof.Weierstrass.X86_64.JacMixedAdd
import VerifiedGarbage.Proof.Weierstrass.X86_64.JointFixedLoad
import VerifiedGarbage.Proof.Weierstrass.X86_64.JointFixedPoint
import VerifiedGarbage.Proof.Weierstrass.X86_64.PointFieldTiming
import VerifiedGarbage.Proof.P256.X86_64.Law
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.P256Adx
import VerifiedGarbage.Proof.Variants.MdHash.X86_64
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # ECDSA over P-256 (FIPS 186-5) on x86-64 -/

-- Deterministic ECDSA (RFC 6979) over P-256 on x86-64, with HMAC as a table
namespace VG.Artifacts.EcdsaP256.X86_64.Rfc6979

open VG.Proof.P256.X86_64 (hasLaw)
open VG.Proof.Ecdsa.Rfc6979.X86_64 (signCodeT OK p256Of p256T_verified signCode_sp)
open VG.Proof.HmacTable.X86_64 (tables names)
open VG.Proof.Variants.MdHash.X86_64 (variants)

def artifacts : List (Artifact X86_64.target) :=
  if hv : OK variants ∧ "VG_P256_COMB" ∉ names variants then [
    Spec.Ecdsa.Rfc6979.Curves.p256SignApi.artifact X86_64.target
      { tables := [("hmac", tables variants)]
        code := Impl.Ecdsa.Rfc6979.X86_64.Fn.sign (Proof.Ecdsa.Rfc6979.X86_64.cfgT (p256Of false hasLaw.law (Proof.P256.combOk7 hasLaw.law) hasLaw.inv) Spec.Ecdsa.Rfc6979.Curves.p256.tries variants)
        verified := Proof.Ecdsa.Rfc6979.X86_64.p256T_scrubbed false hasLaw.law (Proof.P256.combOk7 hasLaw.law) hasLaw.inv variants hv Proof.HmacTable.X86_64.variants_up
        spSafe := Proof.Ecdsa.Rfc6979.X86_64.p256T_spSafe false hasLaw.law (Proof.P256.combOk7 hasLaw.law) hasLaw.inv variants },
    Spec.Ecdsa.Rfc6979.Curves.p256SignApi.artifact X86_64.target
      { suffix := "_adx"
        tables := [("hmac", tables variants)]
        code := Impl.Ecdsa.Rfc6979.X86_64.Fn.sign (Proof.Ecdsa.Rfc6979.X86_64.cfgT (p256Of true hasLaw.law (Proof.P256.combOk7 hasLaw.law) hasLaw.inv) Spec.Ecdsa.Rfc6979.Curves.p256.tries variants)
        verified := Proof.Ecdsa.Rfc6979.X86_64.p256T_scrubbed true hasLaw.law (Proof.P256.combOk7 hasLaw.law) hasLaw.inv variants hv Proof.HmacTable.X86_64.variants_up
        spSafe := Proof.Ecdsa.Rfc6979.X86_64.p256T_spSafe true hasLaw.law (Proof.P256.combOk7 hasLaw.law) hasLaw.inv variants }]
  else []

end VG.Artifacts.EcdsaP256.X86_64.Rfc6979

namespace VG.Artifacts.EcdsaP256.X86_64

open VG.Proof.P256.X86_64 (hasLaw)

public def artifacts : List (Artifact X86_64.target) := [
  Spec.Ecdsa.P256.verifyHashApi.artifact X86_64.target
    { suffix := "_ifma"
      code := Impl.Ecdsa.X86_64.VerifyHash.Fn.verifyHashEvex Spec.Ecdsa.P256.inst.curve.len false Impl.Ecdsa.Verify.X86_64.jointVerifyP256Ifma
      verified := Proof.Ecdsa.Verify.X86_64.verifyHashIfma_scrubbed hasLaw.law (Proof.P256.gtabOk9 hasLaw.law) hasLaw.inv hasLaw.prime
      spSafe := Proof.Ecdsa.Verify.X86_64.verifyHashIfma_spSafe },
  Spec.Ecdsa.P256.verifyHashApi.artifact X86_64.target
    { code := Impl.Ecdsa.X86_64.VerifyHash.Fn.verifyHash Spec.Ecdsa.P256.inst.curve.len false Impl.Ecdsa.Verify.X86_64.jointVerifyP256
      verified := Proof.Ecdsa.Verify.X86_64.verifyHash_scrubbed hasLaw.law (Proof.P256.gtabOk9 hasLaw.law) hasLaw.inv hasLaw.prime
      spSafe := Proof.Ecdsa.Verify.X86_64.verifyHash_spSafe },
  Spec.Ecdsa.P256.verifyHashApi.artifact X86_64.target
    { suffix := "_adx"
      code := Impl.Ecdsa.X86_64.VerifyHash.Fn.verifyHash Spec.Ecdsa.P256.inst.curve.len false Impl.Ecdsa.Verify.X86_64.jointVerifyP256Adx
      verified := Proof.Ecdsa.Verify.X86_64.verifyHashAdx_scrubbed hasLaw.law (Proof.P256.gtabOk9 hasLaw.law) hasLaw.inv hasLaw.prime
      spSafe := Proof.Ecdsa.Verify.X86_64.verifyHashAdx_spSafe }] ++
  Rfc6979.artifacts

spec_apis artifacts

end VG.Artifacts.EcdsaP256.X86_64
