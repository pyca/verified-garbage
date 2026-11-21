module

public import VerifiedGarbage.Impl.Ed25519.PPC64LE.Fn
public import VerifiedGarbage.Spec.Ed25519.Contract
public import VerifiedGarbage.Spec.Ed25519.ExpandedSign
public import VerifiedGarbage.Spec.Ed25519.KeyPair
public import VerifiedGarbage.Proof.Framework.PPC64LE.ScrubProved
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Ed25519.PPC64LE.KeyPair
public import VerifiedGarbage.Proof.Ed25519.PPC64LE.Whole.SignVerified
public import VerifiedGarbage.Proof.Ed25519.PPC64LE.Whole.VerifyMsgVerified
import VerifiedGarbage.Proof.Ed25519.WholeLocal
import VerifiedGarbage.Proof.Framework.Lit

/-!
# Ed25519 on PPC64LE, without secret residue

`vg_ed25519_key_pair`, `vg_ed25519_sign_expanded` and `vg_ed25519_verify`,
each followed by `Impl.Scrub.PPC64LE.scrubTail` (`PPC64LE.Scrub.verifiedScrubbedAll`),
which clears the volatile registers, the vector registers and the stack
their frames use (720, 320 and 224 bytes). The postconditions of
`key_pair` and `sign_expanded` read the memory on return only within
their outputs, and that of `verify` not at all (`PPC64LE.Scrub.PostOut`),
whatever tables of constants their code takes, by RISC-V's proofs
(`Proof/Ed25519/RISCV64/Scrub.lean`). `scrubOf`'s side condition
(`scrubSide`) is proved at each theorem, by the kernel's evaluation of
it when this module is built.
-/

@[expose] public section

namespace VG.Proof.Ed25519.PPC64LE.Scrub

open VG.PPC64LE VG.PPC64LE.Scrub
open VG.Proof.Ed25519.WholeLocal (bytesAt_congr)

/-! ## Postconditions -/

variable (cs : List (String × List (BitVec 64))) (stack : Nat)

theorem keyPairOut :
    PostOut (Spec.Ed25519.keyPairContract (PPC64LE.abi.withConsts cs) stack)
      (Spec.Ed25519.keyPairSig.retBits 64) :=
  postOut_of_local (ScrubAbi.consts cs) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [o, ex, sd, sc], _ =>
      simp only [Spec.Ed25519.keyPairSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size, Nat.mul_one] at hb
      show Spec.Ed25519.bytesAt m₂ ex 64 = _ ∧ Spec.Ed25519.bytesAt m₂ o 32 = _
      rw [bytesAt_congr hb.2.1, bytesAt_congr hb.1]
      exact h

theorem signExpandedOut :
    PostOut (Spec.Ed25519.signExpandedContract (PPC64LE.abi.withConsts cs) stack)
      (Spec.Ed25519.signExpandedSig.retBits 64) :=
  postOut_of_local (ScrubAbi.consts cs) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [o, ex, pk, msg, len, sc], _ =>
      simp only [Spec.Ed25519.signExpandedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
      show ∀ seed : List Byte, _ → _ → Spec.Ed25519.bytesAt m₂ o 64 = _
      rw [bytesAt_congr hb.1]
      exact h

theorem verifyOut :
    PostOut (Spec.Ed25519.verifyContract (PPC64LE.abi.withConsts cs) stack)
      (Spec.Ed25519.verifySig.retBits 64) :=
  postOut_of_local (ScrubAbi.consts cs) fun vs m m₁ m₂ r hlen _ h => by
    match vs, hlen with
    | [_, _, _, _, _], _ => exact h

/-! ## The functions as emitted -/

/-- `vg_ed25519_key_pair` as emitted (`Impl.Ed25519.PPC64LE.Fn.keyPair`) meets
its contract in constant time and returns without secret residue. -/
theorem keyPair_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Ed25519.PPC64LE.Fn.keyPair Proof.Ed25519.PPC64LE.KeyPair.spec 0 :=
  verifiedScrubbedAll (api := Spec.Ed25519.keyPairApi) {
      code := Impl.Ed25519.PPC64LE.KeyPair.keyPair (Spec.Sha512.digest512Api.name ++ "_core")
        Proof.Ed25519.PPC64LE.KeyPair.dgCode "vg_ed25519_public_key_expanded"
        Impl.Ed25519.PPC64LE.Whole.publicKeyExpandedCode
      verified := Proof.Ed25519.PPC64LE.KeyPair.verified }
    720 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16,
        .v17, .v18, .v19]⟩
    (keyPairOut Impl.Ed25519.PPC64LE.combConsts _)
    (by dsimp only; lit_decide)

/-- `vg_ed25519_sign_expanded` as emitted (`Impl.Ed25519.PPC64LE.Fn.signExpanded`)
meets its contract in constant time and returns without secret residue. -/
theorem signExpanded_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Ed25519.PPC64LE.Fn.signExpanded
      (Spec.Ed25519.signExpandedContract (PPC64LE.abi.withConsts Impl.Ed25519.PPC64LE.combConsts) (48 + 320)) 0 :=
  verifiedScrubbedAll (api := Spec.Ed25519.signExpandedApi) {
      code := Impl.Ed25519.PPC64LE.Whole.signExpandedCode
      verified := Proof.Ed25519.PPC64LE.Whole.signExpanded_framed }
    320 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16,
        .v17, .v18, .v19]⟩
    (signExpandedOut Impl.Ed25519.PPC64LE.combConsts _)
    (by dsimp only; lit_decide)

/-- `vg_ed25519_verify` as emitted (`Impl.Ed25519.PPC64LE.Fn.verify`) meets its
contract in constant time and returns without secret residue. -/
theorem verify_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Ed25519.PPC64LE.Fn.verify
      (Spec.Ed25519.verifyContract (PPC64LE.abi.withConsts Impl.Ed25519.PPC64LE.bConsts) (48 + 224)) 32 :=
  verifiedScrubbedAll (api := Spec.Ed25519.verifyApi) {
      code := Impl.Ed25519.PPC64LE.Whole.verifyCode
      verified := Proof.Ed25519.PPC64LE.Whole.verify_framed }
    224 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16,
        .v17, .v18, .v19]⟩
    (verifyOut Impl.Ed25519.PPC64LE.bConsts _)
    (by dsimp only; lit_decide)

end VG.Proof.Ed25519.PPC64LE.Scrub
