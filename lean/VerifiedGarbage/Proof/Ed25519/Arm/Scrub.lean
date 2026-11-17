module

public import VerifiedGarbage.Proof.Framework.Arm.Scrub
public import VerifiedGarbage.Proof.Ed25519.Arm.KeyPair
public import VerifiedGarbage.Proof.Ed25519.Arm.SignCached.Expanded
public import VerifiedGarbage.Proof.Ed25519.Arm.VerifyMessage.Verified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Ed25519.WholeLocal
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseCTLit
meta import VerifiedGarbage.Proof.Framework.Arm.Scrub
meta import VerifiedGarbage.Proof.Ed25519.Arm.KeyPair
meta import VerifiedGarbage.Proof.Ed25519.Arm.SignCached.Expanded
meta import VerifiedGarbage.Proof.Ed25519.Arm.VerifyMessage.Verified
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Ed25519.WholeLocal
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseCTLit

/-!
# Ed25519 on ARMv7, without secret residue

`vg_ed25519_key_pair`, `vg_ed25519_sign_expanded` and `vg_ed25519_verify`,
with either multiplication of the field (`umaal`), have frames. The
postconditions of the first two read the memory on return only within their
outputs, and that of the third not at all (`Arm.Scrub.PostOut`), so each is
registered followed by a wipe of the stack its contract reserves
(`Arm.Scrub.scrubRegF`), and by instructions that set the registers a callee
may change, but the result, and the flags to constants.
-/

@[expose] public section

namespace VG.Proof.Ed25519.Arm.Scrub

open VG VG.Arm VG.Arm.Scrub VG.Arm.FrameStack VG.Impl.Ed25519.Arm
open VG.Proof.Ed25519.WholeLocal (bytesAt_congr)

theorem keyPairOut (cs : List (String × List (BitVec 64))) (stack : Nat) :
    PostOut (Spec.Ed25519.keyPairContract (abi.withConsts cs) stack) (Spec.Ed25519.keyPairSig.retBits 32) :=
  postOut_of_local (ScrubAbi.consts cs) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [o, ex, sd, sc], _ =>
      simp only [Spec.Ed25519.keyPairSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size, Nat.mul_one] at hb
      show Spec.Ed25519.bytesAt m₂ ex 64 = _ ∧ Spec.Ed25519.bytesAt m₂ o 32 = _
      rw [bytesAt_congr hb.2.1, bytesAt_congr hb.1]
      exact h

theorem signExpandedOut (cs : List (String × List (BitVec 64))) (stack : Nat) :
    PostOut (Spec.Ed25519.signExpandedContract (abi.withConsts cs) stack)
      (Spec.Ed25519.signExpandedSig.retBits 32) :=
  postOut_of_local (ScrubAbi.consts cs) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [o, ex, pk, msg, len, sc], _ =>
      simp only [Spec.Ed25519.signExpandedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
      show ∀ seed : List Byte, _ → _ → Spec.Ed25519.bytesAt m₂ o 64 = _
      rw [bytesAt_congr hb.1]
      exact h

theorem verifyOut (cs : List (String × List (BitVec 64))) (stack : Nat) :
    PostOut (Spec.Ed25519.verifyContract (abi.withConsts cs) stack) (Spec.Ed25519.verifySig.retBits 32) :=
  postOut_of_local (leak := some _) (ScrubAbi.consts cs) fun vs m m₁ m₂ r hlen _ h => by
    match vs, hlen with
    | [_, _, _, _, _], _ => exact h

theorem frameOk_280 : FrameOk 280 := by decide

theorem frameOk_600 : FrameOk 600 := by decide

/-- The code of `vg_ed25519_key_pair`: the digest by `vg_sha512_digest`, and the public key by
`vg_ed25519_public_key_expanded` (with `umaal`, `vg_ed25519_public_key_expanded_umaal`). -/
def keyPairCode (umaal : Bool) : Prog isa :=
  Impl.Ed25519.Arm.KeyPair.keyPair Spec.Sha512.digest512Api.name Proof.Ed25519.Arm.KeyPair.dgCode
    ("vg_ed25519_public_key_expanded" ++ suffix umaal) (PublicKey.codeExpanded umaal)

theorem keyPair_armStack (umaal : Bool) : armStack (keyPairCode umaal) ≤ 600 := by
  have h := Proof.Ed25519.Arm.KeyPair.pk_stack (umaal := umaal)
  simp only [keyPairCode, Impl.Ed25519.Arm.KeyPair.keyPair, armStack, Proof.Ed25519.Arm.KeyPair.dg_stack,
    List.length_cons, List.length_nil]
  omega_using [h]

theorem signExpanded_armStack (umaal : Bool) : armStack (SignCached.codeExpanded umaal) ≤ 280 := by
  cases umaal <;> lit_decide

theorem verify_armStack (umaal : Bool) : armStack (VerifyMessage.code umaal) ≤ 280 := by
  cases umaal <;> lit_decide

def keyPairReg (umaal : Bool) (suffix : String) : Registration Spec.Ed25519.keyPairApi target :=
  Arm.Scrub.scrubRegF {
      suffix := suffix
      code := keyPairCode umaal
      verified := Proof.Ed25519.Arm.KeyPair.verified }
    (keyPair_armStack umaal) frameOk_600 (keyPairOut combConsts 600) rfl

def signExpandedReg (umaal : Bool) (suffix : String) : Registration Spec.Ed25519.signExpandedApi target :=
  Arm.Scrub.scrubRegF {
      suffix := suffix
      code := SignCached.codeExpanded umaal
      verified := Proof.Ed25519.Arm.SignCached.signExpanded_verified }
    (signExpanded_armStack umaal) frameOk_280 (signExpandedOut combConsts 280) rfl

def verifyReg (umaal : Bool) (suffix : String) : Registration Spec.Ed25519.verifyApi target :=
  Arm.Scrub.scrubRegF {
      suffix := suffix
      code := VerifyMessage.code umaal
      verified := Proof.Ed25519.Arm.VerifyMessage.verifyMessage_verified }
    (verify_armStack umaal) frameOk_280 (verifyOut combConsts 280) rfl

end VG.Proof.Ed25519.Arm.Scrub
