module

public import VerifiedGarbage.Proof.Ed25519.X86.KeyPair
public import VerifiedGarbage.Proof.Ed25519.X86.SignCached.Verified
public import VerifiedGarbage.Proof.Ed25519.X86.VerifyMessage.Verified
public import VerifiedGarbage.Proof.Framework.X86.ScrubProved
public import VerifiedGarbage.Impl.Ed25519.X86.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Ed25519.Contract
public import VerifiedGarbage.Spec.Ed25519.ExpandedSign
public import VerifiedGarbage.Spec.Ed25519.KeyPair
import VerifiedGarbage.Proof.Ed25519.WholeLocal
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Ed25519.X86.KeyPair
meta import VerifiedGarbage.Proof.Ed25519.X86.SignCached.Verified
meta import VerifiedGarbage.Proof.Ed25519.X86.VerifyMessage.Verified
meta import VerifiedGarbage.Proof.Framework.X86.ScrubProved
meta import VerifiedGarbage.Impl.Ed25519.X86.Fn
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Spec.Ed25519.Contract
meta import VerifiedGarbage.Spec.Ed25519.ExpandedSign
meta import VerifiedGarbage.Spec.Ed25519.KeyPair
meta import VerifiedGarbage.Proof.Ed25519.WholeLocal
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# Ed25519 on x86 (32-bit), without secret residue

`vg_ed25519_key_pair`, `vg_ed25519_sign_expanded` and `vg_ed25519_verify`
keep their working space in frames of their own and call the SHA-512 and
point functions: each, as emitted (`Impl.Ed25519.X86.Fn`), zeroes the
stack it and its callees use and then clears the registers a callee may
change (`X86.Scrub.verifiedScrubbedAll`), given that the postconditions of the key pair and the signature
read the memory on return only within their outputs, and that of the
verification not at all (as RISC-V's `Proof/Ed25519/RISCV64/Scrub.lean`
proves them).
-/

@[expose] public section

namespace VG.Proof.Ed25519.X86.Scrub

open VG.X86 VG.X86.Scrub
open VG.Proof.Ed25519.WholeLocal (bytesAt_congr)

variable (cs : List (String × List (BitVec 64))) (stack : Nat)

theorem keyPairOut :
    PostOut (Spec.Ed25519.keyPairContract (X86.abi.withConsts cs) stack)
      (Spec.Ed25519.keyPairSig.retBits 32) :=
  postOut_of_local (ScrubAbi.consts cs) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [o, ex, sd, sc], _ =>
      simp only [Spec.Ed25519.keyPairSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size, Nat.mul_one] at hb
      show Spec.Ed25519.bytesAt m₂ ex 64 = _ ∧ Spec.Ed25519.bytesAt m₂ o 32 = _
      rw [bytesAt_congr hb.2.1, bytesAt_congr hb.1]
      exact h

theorem signExpandedOut :
    PostOut (Spec.Ed25519.signExpandedContract (X86.abi.withConsts cs) stack)
      (Spec.Ed25519.signExpandedSig.retBits 32) :=
  postOut_of_local (ScrubAbi.consts cs) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [o, ex, pk, msg, len, sc], _ =>
      simp only [Spec.Ed25519.signExpandedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
      show ∀ seed : List Byte, _ → _ → Spec.Ed25519.bytesAt m₂ o 64 = _
      rw [bytesAt_congr hb.1]
      exact h

theorem verifyOut :
    PostOut (Spec.Ed25519.verifyContract (X86.abi.withConsts cs) stack)
      (Spec.Ed25519.verifySig.retBits 32) :=
  postOut_of_local (ScrubAbi.consts cs) fun vs m m₁ m₂ r hlen _ h => by
    match vs, hlen with
    | [_, _, _, _, _], _ => exact h

/-- `vg_ed25519_key_pair`. -/
theorem keyPair_scrubbed :
    VerifiedScrubbed target Impl.Ed25519.X86.Fn.keyPair
      Proof.Ed25519.X86.KeyPair.spec 0 :=
  verifiedScrubbedAll (api := Spec.Ed25519.keyPairApi)
    { code := Impl.Ed25519.X86.KeyPair.keyPair (Spec.Sha512.digest512Api.name ++ "_core")
        KeyPair.dgCode "vg_ed25519_public_key_expanded" Impl.Ed25519.X86.PublicKey.publicKeyExpanded
      verified := KeyPair.verified }
    (keyPairOut Impl.Ed25519.X86.combConsts 628)

/-- `vg_ed25519_sign_expanded`. -/
theorem signExpanded_scrubbed :
    VerifiedScrubbed target Impl.Ed25519.X86.Fn.signExpanded
      (Spec.Ed25519.signExpandedContract (X86.abi.withConsts Impl.Ed25519.X86.combConsts) 280) 0 :=
  verifiedScrubbedAll (api := Spec.Ed25519.signExpandedApi)
    { code := Impl.Ed25519.X86.SignCached.codeExpanded
      verified := SignCached.signExpanded_verified }
    (signExpandedOut Impl.Ed25519.X86.combConsts 280)

/-- `vg_ed25519_verify`. -/
theorem verify_scrubbed :
    VerifiedScrubbed target Impl.Ed25519.X86.Fn.verify
      (Spec.Ed25519.verifyContract (X86.abi.withConsts Impl.Ed25519.X86.bConsts) 280) 32 :=
  verifiedScrubbedAll (api := Spec.Ed25519.verifyApi)
    { code := Impl.Ed25519.X86.VerifyMessage.code
      verified := VerifyMessage.verifyMessage_verified }
    (verifyOut Impl.Ed25519.X86.bConsts 280)

end VG.Proof.Ed25519.X86.Scrub
