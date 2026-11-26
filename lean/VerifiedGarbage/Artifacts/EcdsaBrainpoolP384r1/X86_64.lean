module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ecdsa.Verify.BrainpoolP384r1
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
import VerifiedGarbage.Proof.Framework.X86_64.ScrubUp
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Scrub
import VerifiedGarbage.Proof.Ecdsa.X86_64.BrainpoolP384r1.Lit
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.BrainpoolP384r1.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Scrub
import VerifiedGarbage.Proof.EcKey.X86_64.Scrub.Out
import VerifiedGarbage.Proof.Weierstrass.X86_64.InvSpec
import VerifiedGarbage.Proof.Ecdsa.X86_64.BrainpoolP384r1.Verified
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.BrainpoolP384r1.Verified
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Impl.Ecdsa.X86_64.VerifyHash
import VerifiedGarbage.Proof.Mont.X86_64.Wide
import VerifiedGarbage.Proof.X25519.X86_64.Adx.MulProd
import VerifiedGarbage.Proof.X25519.X86_64.Adx.SqrProd
import VerifiedGarbage.Spec.EcKey.Generic
import VerifiedGarbage.Impl.Ecdh.BrainpoolP384r1.X86_64
import VerifiedGarbage.Proof.BrainpoolP384r1.Point
import VerifiedGarbage.Proof.EcKey.PublicKey
import VerifiedGarbage.Proof.Ecdh.X86_64.Check
import VerifiedGarbage.Proof.Ecdh.X86_64.Peer
import VerifiedGarbage.Proof.Ecdsa.Sign
import VerifiedGarbage.Proof.Ecdsa.Verify
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Final
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Main
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.ProjectiveFinal
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.ProjectiveFlags
import VerifiedGarbage.Proof.Ecdsa.X86_64.CombLays
import VerifiedGarbage.Proof.Ecdsa.X86_64.Main
import VerifiedGarbage.Proof.Ecdsa.X86_64.MulFn
import VerifiedGarbage.Proof.Ecdsa.X86_64.SharedSlots
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.BitByte
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Bswap
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
import VerifiedGarbage.Proof.Weierstrass.TCombWords
import VerifiedGarbage.Proof.Weierstrass.X86_64.Bytes
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
import VerifiedGarbage.Proof.BrainpoolP384r1.X86_64.Law
import VerifiedGarbage.Proof.Weierstrass.X86_64.InvInterface
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.BrainpoolP384r1
import VerifiedGarbage.Proof.Variants.MdHash.X86_64
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # ECDSA over brainpoolP384r1 (FIPS 186-5) on x86-64 -/

-- Deterministic ECDSA (RFC 6979) over brainpoolP384r1 on x86-64, with HMAC as a table
namespace VG.Artifacts.EcdsaBrainpoolP384r1.X86_64.Rfc6979

open VG.Proof.BrainpoolP384r1.X86_64 (hasLaw)
open VG.Proof.Ecdsa.Rfc6979.X86_64 (signCodeT OK brainpoolp384r1 brainpoolp384r1T_verified signCode_sp)
open VG.Proof.HmacTable.X86_64 (tables names)

def artifactsFor (vs : List Proof.Pbkdf2.Md.X86_64.MdHash)
    (hu : ∀ w ∈ vs, Proof.HmacTable.X86_64.HmacUp w) : List (Artifact X86_64.target) :=
  if hv : OK vs ∧ "VG_BRAINPOOLP384R1_COMB" ∉ names vs then [
    Spec.Ecdsa.Rfc6979.Curves.brainpoolp384r1SignApi.artifact X86_64.target
      { tables := [("hmac", tables vs)]
        code := Impl.Ecdsa.Rfc6979.X86_64.Fn.sign (Proof.Ecdsa.Rfc6979.X86_64.cfgT (brainpoolp384r1 hasLaw.law hasLaw.inv) Spec.Ecdsa.Rfc6979.Curves.brainpoolp384r1.tries vs)
        verified := Proof.Ecdsa.Rfc6979.X86_64.brainpoolp384r1T_scrubbed hasLaw.law hasLaw.inv vs hv hu
        spSafe := Proof.Ecdsa.Rfc6979.X86_64.brainpoolp384r1T_spSafe hasLaw.law hasLaw.inv vs }]
  else []

def artifacts : List (Artifact X86_64.target) :=
  artifactsFor VG.Proof.Variants.MdHash.X86_64.variants Proof.HmacTable.X86_64.variants_up

end VG.Artifacts.EcdsaBrainpoolP384r1.X86_64.Rfc6979

namespace VG.Artifacts.EcdsaBrainpoolP384r1.X86_64

open VG.Proof.BrainpoolP384r1.X86_64 (hasLaw)

public def artifacts : List (Artifact X86_64.target) := [
  Spec.Ecdsa.BrainpoolP384r1.verifyHashApi.artifact X86_64.target
    { code := Impl.Ecdsa.X86_64.VerifyHash.Fn.verifyHash Spec.Ecdsa.BrainpoolP384r1.inst.curve.len false Impl.Ecdsa.Verify.X86_64.verifyBrainpoolP384r1 104
      verified := Proof.Ecdsa.Verify.X86_64.BrainpoolP384r1.verifyHash_scrubbed hasLaw.law hasLaw.inv
      spSafe := Proof.Ecdsa.Verify.X86_64.BrainpoolP384r1.verifyHash_spSafe }] ++
  Rfc6979.artifacts

spec_apis artifacts

end VG.Artifacts.EcdsaBrainpoolP384r1.X86_64
