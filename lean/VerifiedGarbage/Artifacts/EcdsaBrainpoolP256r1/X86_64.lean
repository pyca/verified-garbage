module

public import VerifiedGarbage.Proof.Framework.X86_64.ScrubUp
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Scrub
import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Ecdsa.X86_64.BrainpoolP256r1.Lit
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.BrainpoolP256r1.Lit
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public import VerifiedGarbage.Proof.EcKey.X86_64.Scrub.Out
public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvSpec
public import VerifiedGarbage.Proof.Ecdsa.X86_64.BrainpoolP256r1.Verified
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.BrainpoolP256r1.Verified
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Ecdsa.Verify.BrainpoolP256r1
public import VerifiedGarbage.Impl.Ecdsa.X86_64.VerifyHash
public import VerifiedGarbage.Proof.Mont.X86_64.Wide
import VerifiedGarbage.Proof.X25519.X86_64.Adx.MulProd
public import VerifiedGarbage.Proof.X25519.X86_64.Adx.SqrProd
import VerifiedGarbage.Spec.EcKey.Generic
public import VerifiedGarbage.Impl.Ecdh.BrainpoolP256r1.X86_64
public import VerifiedGarbage.Proof.BrainpoolP256r1.Point
public import VerifiedGarbage.Proof.EcKey.PublicKey
public import VerifiedGarbage.Proof.Ecdh.X86_64.Check
public import VerifiedGarbage.Proof.Ecdh.X86_64.Peer
public import VerifiedGarbage.Proof.Ecdsa.Sign
public import VerifiedGarbage.Proof.Ecdsa.Verify
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Final
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Main
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.ProjectiveFinal
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.ProjectiveFlags
public import VerifiedGarbage.Proof.Ecdsa.X86_64.CombLays
public import VerifiedGarbage.Proof.Ecdsa.X86_64.Main
public import VerifiedGarbage.Proof.Ecdsa.X86_64.MulFn
public import VerifiedGarbage.Proof.Ecdsa.X86_64.SharedSlots
public import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.BitByte
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.X86_64.Abi
public import VerifiedGarbage.Proof.Framework.X86_64.Avx
public import VerifiedGarbage.Proof.Framework.X86_64.Bswap
public import VerifiedGarbage.Proof.Framework.X86_64.Exec
public import VerifiedGarbage.Proof.Framework.X86_64.Inline
public import VerifiedGarbage.Proof.Framework.X86_64.Lit
public import VerifiedGarbage.Proof.Framework.X86_64.Masked
public import VerifiedGarbage.Proof.Framework.X86_64.Sse
public import VerifiedGarbage.Proof.Mont.Words128
public import VerifiedGarbage.Proof.Mont.X86_64.Blocks
public import VerifiedGarbage.Proof.Mont.X86_64.CsubS
public import VerifiedGarbage.Proof.Mont.X86_64.Friendly
public import VerifiedGarbage.Proof.Mont.X86_64.Ops
public import VerifiedGarbage.Proof.Mont.X86_64.Round
public import VerifiedGarbage.Proof.Mont.X86_64.Sparse
public import VerifiedGarbage.Proof.Mont.X86_64.SparseX
public import VerifiedGarbage.Proof.Mont.X86_64.SqrPX
public import VerifiedGarbage.Proof.Mont.X86_64.WideOps
public import VerifiedGarbage.Proof.Weierstrass.TCombWords
public import VerifiedGarbage.Proof.Weierstrass.X86_64.Bytes
public import VerifiedGarbage.Proof.Weierstrass.X86_64.Copy
public import VerifiedGarbage.Proof.Weierstrass.X86_64.FprogJ
public import VerifiedGarbage.Proof.Weierstrass.X86_64.Loop
public import VerifiedGarbage.Proof.Weierstrass.X86_64.MontCall
public import VerifiedGarbage.Proof.Weierstrass.X86_64.MontWide8
public import VerifiedGarbage.Proof.Weierstrass.X86_64.SpillUnch
public import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombJ
public import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombJDigit
public import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombSelectY
public import VerifiedGarbage.Proof.Weierstrass.X86_64.WinLoop
public import VerifiedGarbage.TCB.X86_64.Print
public import VerifiedGarbage.Proof.BrainpoolP256r1.X86_64.Law
public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvInterface
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.BrainpoolP256r1
public import VerifiedGarbage.Proof.Variants.MdHash.X86_64

/-! # ECDSA over brainpoolP256r1 (FIPS 186-5) on x86-64 -/

@[expose] public section

-- Deterministic ECDSA (RFC 6979) over brainpoolP256r1 on x86-64, with HMAC as a table
namespace VG.Artifacts.EcdsaBrainpoolP256r1.X86_64.Rfc6979

open VG.Proof.BrainpoolP256r1.X86_64 (hasLaw)
open VG.Proof.Ecdsa.Rfc6979.X86_64 (signCodeT OK brainpoolp256r1 brainpoolp256r1T_verified signCode_sp)
open VG.Proof.HmacTable.X86_64 (tables names)

def artifactsFor (vs : List Proof.Pbkdf2.Md.X86_64.MdHash)
    (hu : ∀ w ∈ vs, Proof.Ecdsa.Rfc6979.X86_64.HmacUp w) : List Artifact :=
  if hv : OK vs ∧ "VG_BRAINPOOLP256R1_COMB" ∉ names vs then [
    Spec.Ecdsa.Rfc6979.Curves.brainpoolp256r1SignApi.artifact X86_64.target
      { tables := [("hmac", tables vs)]
        code := Impl.Ecdsa.Rfc6979.X86_64.Fn.sign (Proof.Ecdsa.Rfc6979.X86_64.cfgT (brainpoolp256r1 hasLaw.law hasLaw.inv) Spec.Ecdsa.Rfc6979.Curves.brainpoolp256r1.tries vs)
        verified := Proof.Ecdsa.Rfc6979.X86_64.brainpoolp256r1T_scrubbed hasLaw.law hasLaw.inv vs hv hu
        spSafe := Proof.Ecdsa.Rfc6979.X86_64.brainpoolp256r1T_spSafe hasLaw.law hasLaw.inv vs }]
  else []

def artifacts : List Artifact :=
  artifactsFor VG.Proof.Variants.MdHash.X86_64.variants Proof.Ecdsa.Rfc6979.X86_64.variants_up

end VG.Artifacts.EcdsaBrainpoolP256r1.X86_64.Rfc6979

namespace VG.Artifacts.EcdsaBrainpoolP256r1.X86_64

open VG.Proof.BrainpoolP256r1.X86_64 (hasLaw)

def artifacts : List Artifact := [
  Spec.Ecdsa.BrainpoolP256r1.verifyHashApi.artifact X86_64.target
    { code := Impl.Ecdsa.X86_64.VerifyHash.Fn.verifyHash Spec.Ecdsa.BrainpoolP256r1.inst.curve.len false Impl.Ecdsa.Verify.X86_64.verifyBrainpoolP256r1
      verified := Proof.Ecdsa.Verify.X86_64.BrainpoolP256r1.verifyHash_scrubbed hasLaw.law hasLaw.inv
      spSafe := Proof.Ecdsa.Verify.X86_64.BrainpoolP256r1.verifyHash_spSafe }] ++
  Rfc6979.artifacts

end VG.Artifacts.EcdsaBrainpoolP256r1.X86_64
