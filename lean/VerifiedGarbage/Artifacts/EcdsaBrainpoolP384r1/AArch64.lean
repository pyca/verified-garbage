module

public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint.Verified
public import VerifiedGarbage.Impl.Ecdsa.AArch64.VerifyHash
public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvSpec
public import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP384r1.Verified
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1.Verified
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
public import VerifiedGarbage.Proof.Framework.Registration
public import Mathlib.Tactic.ClearExcept
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1.Lit
public import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowBase
public import VerifiedGarbage.Spec.Ecdsa.Verify.BrainpoolP384r1
public import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP384r1.Lit
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
public import VerifiedGarbage.Proof.EcKey.PublicKey
public import VerifiedGarbage.Proof.Ecdh.AArch64.Peer
public import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP384r1.Config
public import VerifiedGarbage.Proof.Ecdsa.AArch64.CombLays
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Lays
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Setup
public import VerifiedGarbage.Proof.Ecdsa.AArch64.SlotOps
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Stages
public import VerifiedGarbage.Proof.Ecdsa.Projective
public import VerifiedGarbage.Proof.Ecdsa.Verify
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1.Sum
public import VerifiedGarbage.Proof.Framework.AArch64.Lit
public import VerifiedGarbage.Proof.Weierstrass.AArch64.AddConst
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Bytes
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Rep
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Window
public import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowQuad
public import VerifiedGarbage.TCB.AArch64.Print
public import VerifiedGarbage.Proof.BrainpoolP384r1.AArch64.Law
public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvInterface
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.BrainpoolP384r1
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.Variants.MdHash.AArch64

/-! # brainpoolP384r1 on AArch64, generic over its proven group law and inversions -/

@[expose] public section

-- Deterministic ECDSA (RFC 6979) over brainpoolP384r1 on AArch64, with HMAC as a table
namespace VG.Artifacts.EcdsaBrainpoolP384r1.AArch64.Rfc6979

open VG.Proof.BrainpoolP384r1.AArch64 (hasLaw)
open VG.Proof.Ecdsa.Rfc6979.AArch64 (signCodeT stackT OK brainpoolp384r1 brainpoolp384r1T_verified)
open VG.Proof.HmacTable.AArch64 (tables names)

def artifactsFor (vs : List Proof.Pbkdf2.Md.AArch64.MdHash) : List Artifact :=
  if hv : OK vs ∧ "VG_BRAINPOOLP384R1_COMB7" ∉ names vs then [
    Spec.Ecdsa.Rfc6979.Curves.brainpoolp384r1SignApi.artifact AArch64.target {
      suffix := ""
      tables := [("hmac", tables vs)]
      code := signCodeT (brainpoolp384r1 hasLaw.law hasLaw.inv) Spec.Ecdsa.Rfc6979.Curves.brainpoolp384r1.tries vs
      stack := stackT
      verified := brainpoolp384r1T_verified hasLaw.law hasLaw.inv vs hv }]
  else []

def artifacts : List Artifact :=
  artifactsFor VG.Proof.Variants.MdHash.AArch64.variants

end VG.Artifacts.EcdsaBrainpoolP384r1.AArch64.Rfc6979

namespace VG.Artifacts.EcdsaBrainpoolP384r1.AArch64

open VG.Proof.BrainpoolP384r1.AArch64 (hasLaw)

def artifacts : List Artifact := [
  Spec.Ecdsa.BrainpoolP384r1.verifyHashApi.artifact AArch64.target {
    code := Impl.Ecdsa.AArch64.VerifyHash.verifyHash Spec.Ecdsa.BrainpoolP384r1.inst.curve.len false
      Impl.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint.verify
    stack := 80
    verified := Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint.verifyHash_verified hasLaw.law hasLaw.inv }] ++
  Rfc6979.artifacts

end VG.Artifacts.EcdsaBrainpoolP384r1.AArch64
