module

public import VerifiedGarbage.Proof.Framework.PPC64LE.ScrubProved
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Gcm.Contract
public import VerifiedGarbage.Spec.Gcm.OutOfPlace
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Blocks
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.SplitBlocks.Verified
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.SealSplit.Frame
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Frame
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.GatherSplit.Verified
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.OpenTo.Verified
public import VerifiedGarbage.Proof.AesGcm.RoundsTo
import VerifiedGarbage.Proof.AesGcm.Scratch
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Blocks.Lit
import VerifiedGarbage.Proof.AesGcm.PPC64LE.SplitBlocks.Lit
import VerifiedGarbage.Proof.Aes.PPC64LE.CodeLit
import VerifiedGarbage.Proof.Gcm.PPC64LE.Vpmsum.Lit

/-!
# AES-GCM on PPC64LE, without secret residue

`vg_aes_gcm_init`, `vg_aes_gcm_seal`, `vg_aes_gcm_seal_gather`,
`vg_aes_gcm_open`, `vg_aes_gcm_open_to` and the streaming functions
`vg_aes_gcm_stream_init`, `_aad`, `_encrypt`, `_decrypt`, `_finish` and
`_verify`, each followed by `Impl.Scrub.PPC64LE.scrubTail`
(`PPC64LE.Scrub.scrubOf`), which clears the volatile registers and the
stack its frames used: each keeps its working space (the padded blocks,
the saved registers and the tags compared) in a frame it does not wipe
itself (`withStackScratch`, `withStackScratchArgs`, and the frames of
`vg_aes_gcm_seal_split` and `vg_aes_gcm_open_split`), which the tail wipes
whole. The functions they call need no working space, so `init` and the
streaming functions keep only 288 bytes, in a frame of 320; `seal`, `open`,
`seal_gather` and `open_to` keep their helpers' working space as well, at
`W + 448`, in frames of 2.6 KB or more. Every one
may write every volatile register but CA (and `vg_aes_gcm_init` none of
`v12`–`v18`), so the tail clears them all. The functions they call
(`vg_aes_ctr32`, `vg_ghash`, `vg_aes_expand_key_scratch` and the split
blocks) are internal, and keep their code.

Their postconditions read the memory on return only within their buffers
(`PPC64LE.Scrub.PostOut`): the key context, the streaming state, the data,
the output and the tag, as the postconditions in terms of the key context
do (`Proof/AesGcm/Scratch.lean`), for every key whose context it is.
-/

@[expose] public section

namespace VG.Proof.AesGcm.PPC64LE.Scrub

open VG.PPC64LE VG.PPC64LE.Scrub VG.Proof.AesGcm.PPC64LE
open VG.Proof.AesGcm (agree_of bytesAt_congr streamRepr_congr)

/-! ## Reading memory only within the buffers -/

/-- `postOut_of_local`, for a postcondition that reads the memory on return
only within the buffers when the precondition holds (as RSA's,
`Rsa.PPC64LE.Scrub.postOut_of_local_pre`). -/
theorem postOut_of_local_pre {A : Abi isa} (hA : ScrubAbi A) {sig : Sig}
    {pre : Curry (sig.words A.ptrBits) (Mem → Prop)}
    {post : sig.Post A.ptrBits} {wa : Bool} {stack : Nat}
    {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))}
    (hl : ∀ vs m m₁ m₂ r, vs.length = (sig.words A.ptrBits).length →
      Curry.apply (sig.words A.ptrBits) pre vs m →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words A.ptrBits) post vs m m₁ r →
        Curry.apply (sig.words A.ptrBits) post vs m m₂ r) :
    PostOut (sig.contract A pre post wa stack leak) (sig.retBits A.ptrBits) := by
  intro s u u' hs hp hm hr
  simp only [Sig.contract] at hs hp ⊢
  revert hs hp
  cases hargs : A.args ((sig.words A.ptrBits).map (·.bits A.ptrBits)) with
  | none => intro hs; exact hs.elim
  | some vals =>
    intro hs hp
    simp only at hs hp ⊢
    obtain ⟨-, hrd, hwr, -, -, -, hpre⟩ := hs
    have hpre' : Curry.apply (sig.words A.ptrBits) pre (vals s) (A.mem s) := by
      cases hal : A.alignsBufs
      · rw [hal] at hpre; exact hpre
      · rw [hal] at hpre; exact hpre.1
    rw [hA.ret, hA.mem, hA.mem] at hp ⊢
    rw [hA.mem] at hpre'
    rw [hr]
    refine hl (vals s) _ _ _ _ (by rw [hA.argsLen _ _ hargs s, List.length_map]) hpre' (fun b hb a ha => ?_) hp
    have hin : b.1 ∈ s.rd ++ s.wr := by
      cases hw : b.2
      · apply List.mem_append_left; apply hA.rdSub; rw [hrd]
        exact List.mem_map.mpr ⟨b, List.mem_filter.mpr ⟨List.mem_append_left _ (List.mem_append_left _ hb),
          by simp [hw]⟩, rfl⟩
      · apply List.mem_append_right; rw [← hA.wr, hwr]
        exact List.mem_map.mpr ⟨b, List.mem_filter.mpr ⟨List.mem_append_left _ (List.mem_append_left _ hb),
          hw⟩, rfl⟩
    exact (hm a ⟨b.1, hin, ha⟩).symm

/-- The `n` bytes at `p`, of a buffer of at least `n` bytes there on which
the memories agree. -/
theorem bytesAt_of {m₁ m₂ : Mem} {p : Addr} {L n : Nat} (h : ∀ a, Region.Contains ⟨p, L⟩ a 1 → m₁ a = m₂ a)
    (hn : n ≤ L) : Spec.Aes.bytesAt m₂ p n = Spec.Aes.bytesAt m₁ p n :=
  bytesAt_congr fun i hi => agree_of h i (by omega_using [hn, hi])

theorem len_le (x : BitVec 64) : ((ArgWord.int abi.ptrBits).ofRaw x).toNat ≤ x.toNat := Nat.le_refl _

/-! ## Postconditions -/

theorem initOut (stack : Nat) :
    PostOut (Spec.Gcm.initContract PPC64LE.abi stack) (Spec.Gcm.initSig.retBits 64) :=
  postOut_of_local_pre ScrubAbi.plain (Proof.AesGcm.initPostOut_local _)

theorem streamInitOut (stack : Nat) :
    PostOut (Spec.Gcm.streamInitContract PPC64LE.abi stack) (Spec.Gcm.streamInitSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.AesGcm.streamInitPostOut_local _)

theorem streamAadOut (stack : Nat) :
    PostOut (Spec.Gcm.streamAadContract PPC64LE.abi stack) (Spec.Gcm.streamAadSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.AesGcm.streamAadPostOut_local _)

theorem streamEncryptOut (stack : Nat) :
    PostOut (Spec.Gcm.streamEncryptContract PPC64LE.abi stack) (Spec.Gcm.streamCryptSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [ctx, rounds, st, al, tl, data, len], _ =>
      simp only [Spec.Gcm.streamCryptSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size, Nat.mul_one] at hb
      intro key hk _ _ iv a p hr hA hT _
      obtain ⟨g₁, g₂⟩ := h key hk iv a p hr hA hT
      exact ⟨streamRepr_congr (fun i hi => agree_of hb.2.1 i (by omega_using [hi])) g₁,
        (bytesAt_of hb.2.2 (len_le len)).trans g₂⟩

theorem streamDecryptOut (stack : Nat) :
    PostOut (Spec.Gcm.streamDecryptContract PPC64LE.abi stack) (Spec.Gcm.streamCryptSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [ctx, rounds, st, al, tl, data, len], _ =>
      simp only [Spec.Gcm.streamCryptSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size, Nat.mul_one] at hb
      intro key hk _ _ iv a c hr hA hT _
      obtain ⟨g₁, g₂⟩ := h key hk iv a c hr hA hT
      exact ⟨streamRepr_congr (fun i hi => agree_of hb.2.1 i (by omega_using [hi])) g₁,
        (bytesAt_of hb.2.2 (len_le len)).trans g₂⟩

theorem streamFinishOut (stack : Nat) :
    PostOut (Spec.Gcm.streamFinishContract PPC64LE.abi stack) (Spec.Gcm.streamFinishSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [ctx, rounds, st, al, tl, tag], _ =>
      simp only [Spec.Gcm.streamFinishSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size, Nat.mul_one] at hb
      intro key hk _ _ iv a c hr hA hT
      exact (bytesAt_of hb.2.2 (Nat.le_refl _)).trans (h key hk iv a c hr hA hT)

theorem streamVerifyOut (stack : Nat) :
    PostOut (Spec.Gcm.streamVerifyContract PPC64LE.abi stack) (Spec.Gcm.streamVerifySig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen _ h => by
    match vs, hlen with
    | [ctx, rounds, st, al, tl, tag, tagLen], _ => exact h

theorem sealOut (stack : Nat) :
    PostOut (Spec.Gcm.sealContract PPC64LE.abi stack) (Spec.Gcm.sealSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [ctx, rounds, nonce, nl, aad, al, data, len, tag], _ =>
      simp only [Spec.Gcm.sealSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size, Nat.mul_one] at hb
      intro key hk
      exact (h key hk).trans (Prod.ext (bytesAt_of hb.2.2.2.1 (len_le len)).symm
        (bytesAt_of hb.2.2.2.2 (Nat.le_refl _)).symm)

theorem openOut (stack : Nat) :
    PostOut (Spec.Gcm.openContract PPC64LE.abi stack) (Spec.Gcm.openSig.retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [ctx, rounds, nonce, nl, aad, al, data, len, tag, tagLen], _ =>
      simp only [Spec.Gcm.openSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size, Nat.mul_one] at hb
      intro key hk
      have h' := h key hk
      rw [show Spec.Aes.bytesAt m₂ (ArgWord.addr.ofRaw data) ((ArgWord.int abi.ptrBits).ofRaw len).toNat =
          Spec.Aes.bytesAt m₁ (ArgWord.addr.ofRaw data) ((ArgWord.int abi.ptrBits).ofRaw len).toNat from
        bytesAt_of hb.2.2.2.1 (len_le len)]
      exact h'

theorem sealGatherOut (stack : Nat) :
    PostOut (Spec.Gcm.sealGatherContract PPC64LE.abi stack) (Spec.Gcm.sealGatherSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [ctx, rounds, nonce, nl, aad, al, src, sc, dst, len, tag], _ =>
      simp only [Spec.Gcm.sealGatherSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size, Nat.mul_one] at hb
      intro key hk hl
      exact (h key hk hl).trans (Prod.ext (bytesAt_of hb.2.2.2.1 (len_le len)).symm
        (bytesAt_of hb.2.2.2.2 (Nat.le_refl _)).symm)

theorem openToOut (stack : Nat) :
    PostOut (Spec.Gcm.openToContract PPC64LE.abi stack) (Spec.Gcm.openToSig.retBits 64) :=
  postOut_of_local_pre ScrubAbi.plain fun vs m m₁ m₂ r hlen hpre hb h => by
    match vs, hlen with
    | [ctx, rounds, nonce, nl, aad, al, src, len, dst, dl, tag, tagLen], _ =>
      simp only [Spec.Gcm.openToSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size, Nat.mul_one] at hb
      obtain ⟨-, hd⟩ := hpre
      have hd' : ((ArgWord.int abi.ptrBits).ofRaw len).toNat ≤ dl.toNat := by
        rw [← hd]; exact len_le dl
      intro key hk
      have h' := h key hk
      rw [show Spec.Aes.bytesAt m₂ (ArgWord.addr.ofRaw dst) ((ArgWord.int abi.ptrBits).ofRaw len).toNat =
          Spec.Aes.bytesAt m₁ (ArgWord.addr.ofRaw dst) ((ArgWord.int abi.ptrBits).ofRaw len).toNat from
        bytesAt_of hb.2.2.2.2.1 hd']
      exact h'

/-! ## The registrations

Over the laws of `vg_ghash` (`Gcm.PPC64LE.GhashLaw`, `Gcm.PPC64LE.Vpmsum.FoldLaw`), which the registration
file gives, so that this module does not import their algebra. -/

variable [VG.Proof.Gcm.PPC64LE.GhashLaw] [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw]

/-- The volatile registers all but CA: what every function here may write. -/
def clearAll : Impl.Scrub.PPC64LE.Clear :=
  ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
    [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17,
      .v18, .v19]⟩

/-- `Spec.Gcm.initApi`. -/
def initReg : Registration Spec.Gcm.initApi PPC64LE.target :=
  scrubOf {
      code := Impl.StackScratch.PPC64LE.withStackScratch 320 .r6 Impl.AesGcm.PPC64LE.init
      verified := init_framed }
    320 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v19]⟩
    (initOut _)
    (by dsimp only; lit_decide)

/-- `Spec.Gcm.streamInitApi`. -/
def streamInitReg : Registration Spec.Gcm.streamInitApi PPC64LE.target :=
  scrubOf {
      code := Impl.StackScratch.PPC64LE.withStackScratch 320 .r7 Impl.AesGcm.PPC64LE.streamInit
      verified := streamInit_framed }
    320 clearAll
    (streamInitOut _)
    (by dsimp only; lit_decide)

/-- `Spec.Gcm.streamAadApi`. -/
def streamAadReg : Registration Spec.Gcm.streamAadApi PPC64LE.target :=
  scrubOf {
      code := Impl.StackScratch.PPC64LE.withStackScratch 320 .r8 Impl.AesGcm.PPC64LE.streamAad
      verified := streamAad_framed }
    320 clearAll
    (streamAadOut _)
    (by dsimp only; lit_decide)

/-- `Spec.Gcm.streamEncryptApi`. -/
def streamEncryptReg : Registration Spec.Gcm.streamEncryptApi PPC64LE.target :=
  scrubOf {
      code := Impl.StackScratch.PPC64LE.withStackScratch 320 .r10 Impl.AesGcm.PPC64LE.streamEncrypt
      verified := Proof.AesGcm.streamEncrypt_keyed streamEncrypt_framed }
    320 clearAll
    (streamEncryptOut _)
    (by dsimp only; lit_decide)

/-- `Spec.Gcm.streamDecryptApi`. -/
def streamDecryptReg : Registration Spec.Gcm.streamDecryptApi PPC64LE.target :=
  scrubOf {
      code := Impl.StackScratch.PPC64LE.withStackScratch 320 .r10 Impl.AesGcm.PPC64LE.streamDecrypt
      verified := Proof.AesGcm.streamDecrypt_keyed streamDecrypt_framed }
    320 clearAll
    (streamDecryptOut _)
    (by dsimp only; lit_decide)

/-- `Spec.Gcm.streamFinishApi`. -/
def streamFinishReg : Registration Spec.Gcm.streamFinishApi PPC64LE.target :=
  scrubOf {
      code := Impl.StackScratch.PPC64LE.withStackScratch 320 .r9 Impl.AesGcm.PPC64LE.streamFinish
      verified := Proof.AesGcm.streamFinish_keyed streamFinish_framed }
    320 clearAll
    (streamFinishOut _)
    (by dsimp only; lit_decide)

/-- `Spec.Gcm.streamVerifyApi`. -/
def streamVerifyReg : Registration Spec.Gcm.streamVerifyApi PPC64LE.target :=
  scrubOf {
      code := Impl.StackScratch.PPC64LE.withStackScratch 320 .r10 Impl.AesGcm.PPC64LE.streamVerify
      verified := Proof.AesGcm.streamVerify_keyed streamVerify_framed }
    320 clearAll
    (streamVerifyOut _)
    (by dsimp only; lit_decide)

/-- `Spec.Gcm.sealApi`. -/
def sealReg : Registration Spec.Gcm.sealApi PPC64LE.target :=
  scrubOf {
      code := Impl.StackScratch.PPC64LE.withStackScratchArgs 2672 1 Impl.AesGcm.PPC64LE.SealFused.seal
      verified := Proof.AesGcm.seal_keyed seal_framed }
    2672 clearAll
    (sealOut _)
    (by dsimp only; lit_decide)

/-- `Spec.Gcm.openApi`. -/
def openReg : Registration Spec.Gcm.openApi PPC64LE.target :=
  scrubOf {
      code := Impl.StackScratch.PPC64LE.withStackScratchArgs 2688 2 Impl.AesGcm.PPC64LE.open
      verified := Proof.AesGcm.open_keyed open_framed }
    2688 clearAll
    (openOut _)
    (by dsimp only; lit_decide)

/-- `Spec.Gcm.sealGatherApi`. -/
def sealGatherReg : Registration Spec.Gcm.sealGatherApi PPC64LE.target :=
  scrubOf {
      code := Impl.AesGcm.PPC64LE.GatherSplit.sealGather
      verified := Proof.AesGcm.sealGather_keyed GatherSplit.verified }
    2960 clearAll
    (sealGatherOut _)
    (by dsimp only; lit_decide)

/-- `Spec.Gcm.openToApi`. -/
def openToReg : Registration Spec.Gcm.openToApi PPC64LE.target :=
  scrubOf {
      code := Impl.AesGcm.PPC64LE.OpenTo.openTo
      verified := Proof.AesGcm.openTo_keyed OpenTo.openTo_verified }
    2720 clearAll
    (openToOut _)
    (by dsimp only; lit_decide)

end VG.Proof.AesGcm.PPC64LE.Scrub
