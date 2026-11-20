module

public import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
public import VerifiedGarbage.Impl.AesGcm.Arm.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.AesGcm.Arm.Frame
public import VerifiedGarbage.Proof.AesGcm.Arm.Gather.Verified
public import VerifiedGarbage.Proof.AesGcm.Arm.OpenTo
public import VerifiedGarbage.Proof.AesGcm.RoundsTo
import VerifiedGarbage.Proof.AesGcm.Scratch
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Gcm.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
meta import VerifiedGarbage.Impl.AesGcm.Arm.Fn
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.AesGcm.Arm.Frame
meta import VerifiedGarbage.Proof.AesGcm.Arm.Gather.Verified
meta import VerifiedGarbage.Proof.AesGcm.Arm.OpenTo
meta import VerifiedGarbage.Proof.AesGcm.RoundsTo
meta import VerifiedGarbage.Proof.AesGcm.Scratch
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Gcm.Arm.Lit

/-!
# AES-GCM on ARMv7, without secret residue

Every public function of AES-GCM on ARMv7 keeps its working space in a frame
within the stack its contract reserves and makes no indirect call (evaluated
by `lit_decide`), and its postcondition reads the memory on return only
within its buffers (`Arm.Scrub.PostOut`, from the lemmas of
`Proof/AesGcm/Scratch.lean` and as on PPC64LE, `Proof/AesGcm/PPC64LE/Scrub.lean`).
Each is emitted followed by a wipe of that stack and by instructions that
set the registers a callee may change, but the result, and the flags to
constants (`Impl.AesGcm.Arm.Fn`), and `Fn` below states
that it returns without secret residue (`Arm.Scrub.verifiedScrubbedF`), which
is what its registration binds.

That stack is a frame of the model (`Arm.Scrub.FrameOk`): where the number
of bytes a proof is stated with is not one (2568, 2584, 2600, 2620), the
function is stated with the next that is (2576, 2592, 2608, 2624;
`Arm.Scrub.Verified.stack_le`), whose precondition the same state as before
satisfies.

`vg_aes_gcm_seal_gather` calls `vg_aes_gcm_seal`'s code as it is verified,
without the wipe, under a name of its own (`vg_aes_gcm_seal_entry`,
`sealFnEntry`), which the emitter writes as an internal function: its own
wipe covers the frames of that call.
-/

@[expose] public section

namespace VG.Proof.AesGcm.Arm.Scrub

open VG VG.Arm VG.Arm.Scrub VG.Arm.FrameStack VG.Proof.AesGcm.Arm VG.Impl.AesGcm.Arm
open VG.Proof.AesGcm (agree_of bytesAt_congr streamRepr_congr)

/-! ## Reading memory only within the buffers -/

/-- `postOut_of_local`, for a postcondition that reads the memory on return
only within the buffers when the precondition holds. -/
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

theorem len_le (x : BitVec 64) : ((ArgWord.int abi.ptrBits).ofRaw x).toNat ≤ x.toNat := by
  show (x.setWidth 32).toNat ≤ x.toNat
  rw [BitVec.toNat_setWidth]; exact Nat.mod_le _ _

/-! ## Postconditions -/

theorem initOut (stack : Nat) :
    PostOut (Spec.Gcm.initContract Arm.abi stack) (Spec.Gcm.initSig.retBits 32) :=
  postOut_of_local_pre ScrubAbi.plain (Proof.AesGcm.initPostOut_local _)

theorem streamInitOut (stack : Nat) :
    PostOut (Spec.Gcm.streamInitContract Arm.abi stack) (Spec.Gcm.streamInitSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.AesGcm.streamInitPostOut_local _)

theorem streamAadOut (stack : Nat) :
    PostOut (Spec.Gcm.streamAadContract Arm.abi stack) (Spec.Gcm.streamAadSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.AesGcm.streamAadPostOut_local _)

theorem streamEncryptOut (stack : Nat) :
    PostOut (Spec.Gcm.streamEncryptContract Arm.abi stack) (Spec.Gcm.streamCryptSig.retBits 32) :=
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
    PostOut (Spec.Gcm.streamDecryptContract Arm.abi stack) (Spec.Gcm.streamCryptSig.retBits 32) :=
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
    PostOut (Spec.Gcm.streamFinishContract Arm.abi stack) (Spec.Gcm.streamFinishSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [ctx, rounds, st, al, tl, tag], _ =>
      simp only [Spec.Gcm.streamFinishSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size, Nat.mul_one] at hb
      intro key hk _ _ iv a c hr hA hT
      exact (bytesAt_of hb.2.2 (Nat.le_refl _)).trans (h key hk iv a c hr hA hT)

theorem streamVerifyOut (stack : Nat) :
    PostOut (Spec.Gcm.streamVerifyContract Arm.abi stack) (Spec.Gcm.streamVerifySig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen _ h => by
    match vs, hlen with
    | [ctx, rounds, st, al, tl, tag, tagLen], _ => exact h

theorem sealOut (stack : Nat) :
    PostOut (Spec.Gcm.sealContract Arm.abi stack) (Spec.Gcm.sealSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [ctx, rounds, nonce, nl, aad, al, data, len, tag], _ =>
      simp only [Spec.Gcm.sealSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size, Nat.mul_one] at hb
      intro key hk
      exact (h key hk).trans (Prod.ext (bytesAt_of hb.2.2.2.1 (len_le len)).symm
        (bytesAt_of hb.2.2.2.2 (Nat.le_refl _)).symm)

theorem openOut (stack : Nat) :
    PostOut (Spec.Gcm.openContract Arm.abi stack) (Spec.Gcm.openSig.retBits 32) :=
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
    PostOut (Spec.Gcm.sealGatherContract Arm.abi stack) (Spec.Gcm.sealGatherSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [ctx, rounds, nonce, nl, aad, al, src, sc, dst, len, tag], _ =>
      simp only [Spec.Gcm.sealGatherSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size, Nat.mul_one] at hb
      intro key hk hl
      exact (h key hk hl).trans (Prod.ext (bytesAt_of hb.2.2.2.1 (len_le len)).symm
        (bytesAt_of hb.2.2.2.2 (Nat.le_refl _)).symm)

theorem openToOut (stack : Nat) :
    PostOut (Spec.Gcm.openToContract Arm.abi stack) (Spec.Gcm.openToSig.retBits 32) :=
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

/-! ## The stack, rounded up to a frame of the model -/

theorem frameOk_2576 : FrameOk 2576 := by decide
theorem frameOk_2592 : FrameOk 2592 := by decide
theorem frameOk_2608 : FrameOk 2608 := by decide
theorem frameOk_2624 : FrameOk 2624 := by decide
theorem frameOk_2640 : FrameOk 2640 := by decide

theorem initSat : ∃ s, (Spec.Gcm.initContract Arm.abi 2576).pre s := by
  implies_sat [Spec.Gcm.initContract, Spec.Gcm.initSig, Spec.Gcm.initPre, Spec.Gcm.initPost,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [initFrameSat, mkSat] using initFrameSat

theorem streamInitSat : ∃ s, (Spec.Gcm.streamInitContract Arm.abi 2592).pre s := by
  implies_sat [Spec.Gcm.streamInitContract, Spec.Gcm.streamInitSig, Spec.Gcm.streamInitPost,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [streamInitFrameSat, mkSat] using streamInitFrameSat

theorem streamAadSat : ∃ s, (Spec.Gcm.streamAadContract Arm.abi 2592).pre s := by
  implies_sat [Spec.Gcm.streamAadContract, Spec.Gcm.streamAadSig, Spec.Gcm.streamAadPost,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [streamAadFrameSat, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using streamAadFrameSat

theorem streamEncryptSat : ∃ s, (Proof.AesGcm.streamEncryptRoundsContract Arm.abi 2608).pre s := by
  implies_sat [Proof.AesGcm.streamEncryptRoundsContract, Spec.Gcm.streamCryptSig, Spec.Gcm.streamTextPre,
    Proof.AesGcm.streamEncryptRoundsPost, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [crFrameSat, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using crFrameSat

theorem streamDecryptSat : ∃ s, (Proof.AesGcm.streamDecryptRoundsContract Arm.abi 2608).pre s := by
  implies_sat [Proof.AesGcm.streamDecryptRoundsContract, Spec.Gcm.streamCryptSig, Spec.Gcm.streamTextPre,
    Proof.AesGcm.streamDecryptRoundsPost, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [crFrameSat, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using crFrameSat

theorem streamFinishSat : ∃ s, (Proof.AesGcm.streamFinishRoundsContract Arm.abi 2608).pre s := by
  implies_sat [Proof.AesGcm.streamFinishRoundsContract, Spec.Gcm.streamFinishSig, Spec.Gcm.streamFinishPre,
    Proof.AesGcm.streamFinishRoundsPost, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [finFrameSat, mkSat4, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using finFrameSat

theorem streamVerifySat : ∃ s, (Proof.AesGcm.streamVerifyRoundsContract Arm.abi 2608).pre s := by
  implies_sat [Proof.AesGcm.streamVerifyRoundsContract, Spec.Gcm.streamVerifySig, Spec.Gcm.streamVerifyPre,
    Proof.AesGcm.streamVerifyRoundsPost, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [verFrameSat, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using verFrameSat

theorem sealSat : ∃ s, (Proof.AesGcm.sealRoundsContract Arm.abi 2608).pre s := by
  implies_sat [Proof.AesGcm.sealRoundsContract, Spec.Gcm.sealSig, Spec.Gcm.sealPre, Proof.AesGcm.sealRoundsPost,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [sealFrameSat, mkSat4, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using sealFrameSat

theorem openSat : ∃ s, (Proof.AesGcm.openRoundsContract Arm.abi 2608).pre s := by
  implies_sat [Proof.AesGcm.openRoundsContract, Spec.Gcm.openSig, Spec.Gcm.openPre, Proof.AesGcm.openRoundsPost,
    Spec.Gcm.openLeak, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [openFrameSat, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using openFrameSat

theorem openToSat : ∃ s, (Proof.AesGcm.openToRoundsContract Arm.abi 2624).pre s := by
  implies_sat [Proof.AesGcm.openToRoundsContract, Spec.Gcm.openToSig, Spec.Gcm.openToPre,
    Proof.AesGcm.openToRoundsPost, Spec.Gcm.openToLeak, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
    Arm.State.addr]
    [openToFrameSat, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using openToFrameSat

/-! ## The code: its frames, and no indirect call -/

/-- `vg_aes_gcm_seal`'s code, as `vg_aes_gcm_seal_gather` calls it: under a
name of its own. -/
def sealFnEntry [VG.Proof.Gcm.Arm.GhashLaw] : Gather.SealFn :=
  ⟨Spec.Gcm.sealApi.name ++ "_entry", Gather.sealFn.code, Gather.sealFn.verified, Gather.sealFn.depth⟩

theorem init_code :
    CodeOk (Impl.StackScratch.Arm.withRegScratch 2560 .r3 init) 2576 := by
  lit_decide

theorem streamInit_code :
    CodeOk (Impl.StackScratch.Arm.withStackScratch 2576 0 streamInit) 2592 := by
  lit_decide

theorem streamAad_code :
    CodeOk (Impl.StackScratch.Arm.withStackScratch 2576 2 streamAad) 2592 := by
  lit_decide

theorem streamEncrypt_code :
    CodeOk (Impl.StackScratch.Arm.withStackScratch 2592 6 streamEncrypt) 2608 := by
  lit_decide

theorem streamDecrypt_code :
    CodeOk (Impl.StackScratch.Arm.withStackScratch 2592 6 streamDecrypt) 2608 := by
  lit_decide

theorem streamFinish_code :
    CodeOk (Impl.StackScratch.Arm.withStackScratch 2592 5 streamFinish) 2608 := by
  lit_decide

theorem streamVerify_code :
    CodeOk (Impl.StackScratch.Arm.withStackScratch 2592 6 streamVerify) 2608 := by
  lit_decide

theorem seal_code :
    CodeOk (Impl.StackScratch.Arm.withStackScratch 2592 5 «seal») 2608 := by
  lit_decide

theorem open_code :
    CodeOk (Impl.StackScratch.Arm.withStackScratch 2592 6 «open») 2608 := by
  lit_decide

theorem sealGather_code [VG.Proof.Gcm.Arm.GhashLaw] :
    CodeOk (Impl.AesGcm.Arm.SealGather.sealGather sealFnEntry.name sealFnEntry.code) 2640 := by
  simp only [sealFnEntry, Gather.sealFn]
  lit_decide

theorem openTo_code :
    CodeOk (Impl.StackScratch.Arm.withStackScratch 2608 8 openTo) 2624 := by
  lit_decide

end VG.Proof.AesGcm.Arm.Scrub

namespace VG.Proof.AesGcm.Arm.Fn

open VG VG.Arm VG.Arm.Scrub VG.Arm.FrameStack VG.Proof.AesGcm.Arm VG.Impl.AesGcm.Arm
open VG.Proof.AesGcm (agree_of bytesAt_congr streamRepr_congr)


/-- `vg_aes_gcm_init`. -/
theorem init : VerifiedScrubbed target Impl.AesGcm.Arm.Fn.init (Spec.Gcm.initContract abi 2576) 0 :=
  verifiedScrubbedF (api := Spec.Gcm.initApi)
    { code := Impl.StackScratch.Arm.withRegScratch 2560 .r3 Impl.AesGcm.Arm.init
      verified := (Verified.stack_le (by decide) init_framed Scrub.initSat :
        Verified Arm.target _ (Spec.Gcm.initContract Arm.abi 2576)) }
    (Scrub.initOut _) (scrubSideF_of Scrub.init_code Scrub.frameOk_2576 _)

/-- `vg_aes_gcm_stream_init`. -/
theorem streamInit [VG.Proof.Gcm.Arm.GhashLaw] : VerifiedScrubbed target Impl.AesGcm.Arm.Fn.streamInit (Spec.Gcm.streamInitContract abi 2592) 0 :=
  verifiedScrubbedF (api := Spec.Gcm.streamInitApi)
    { code := Impl.StackScratch.Arm.withStackScratch 2576 0 Impl.AesGcm.Arm.streamInit
      verified := (Verified.stack_le (by decide) streamInit_framed Scrub.streamInitSat :
        Verified Arm.target _ (Spec.Gcm.streamInitContract Arm.abi 2592)) }
    (Scrub.streamInitOut _) (scrubSideF_of Scrub.streamInit_code Scrub.frameOk_2592 _)

/-- `vg_aes_gcm_stream_aad`. -/
theorem streamAad [VG.Proof.Gcm.Arm.GhashLaw] : VerifiedScrubbed target Impl.AesGcm.Arm.Fn.streamAad (Spec.Gcm.streamAadContract abi 2592) 0 :=
  verifiedScrubbedF (api := Spec.Gcm.streamAadApi)
    { code := Impl.StackScratch.Arm.withStackScratch 2576 2 Impl.AesGcm.Arm.streamAad
      verified := (Verified.stack_le (by decide) streamAad_framed Scrub.streamAadSat :
        Verified Arm.target _ (Spec.Gcm.streamAadContract Arm.abi 2592)) }
    (Scrub.streamAadOut _) (scrubSideF_of Scrub.streamAad_code Scrub.frameOk_2592 _)

/-- `vg_aes_gcm_stream_encrypt`. -/
theorem streamEncrypt [VG.Proof.Gcm.Arm.GhashLaw] : VerifiedScrubbed target Impl.AesGcm.Arm.Fn.streamEncrypt (Spec.Gcm.streamEncryptContract abi 2608) 0 :=
  verifiedScrubbedF (api := Spec.Gcm.streamEncryptApi)
    { code := Impl.StackScratch.Arm.withStackScratch 2592 6 Impl.AesGcm.Arm.streamEncrypt
      verified := Proof.AesGcm.streamEncrypt_keyed (Verified.stack_le (by decide) streamEncrypt_framed
        Scrub.streamEncryptSat : Verified Arm.target _ (Proof.AesGcm.streamEncryptRoundsContract Arm.abi 2608)) }
    (Scrub.streamEncryptOut _) (scrubSideF_of Scrub.streamEncrypt_code Scrub.frameOk_2608 _)

/-- `vg_aes_gcm_stream_decrypt`. -/
theorem streamDecrypt [VG.Proof.Gcm.Arm.GhashLaw] : VerifiedScrubbed target Impl.AesGcm.Arm.Fn.streamDecrypt (Spec.Gcm.streamDecryptContract abi 2608) 0 :=
  verifiedScrubbedF (api := Spec.Gcm.streamDecryptApi)
    { code := Impl.StackScratch.Arm.withStackScratch 2592 6 Impl.AesGcm.Arm.streamDecrypt
      verified := Proof.AesGcm.streamDecrypt_keyed (Verified.stack_le (by decide) streamDecrypt_framed
        Scrub.streamDecryptSat : Verified Arm.target _ (Proof.AesGcm.streamDecryptRoundsContract Arm.abi 2608)) }
    (Scrub.streamDecryptOut _) (scrubSideF_of Scrub.streamDecrypt_code Scrub.frameOk_2608 _)

/-- `vg_aes_gcm_stream_finish`. -/
theorem streamFinish [VG.Proof.Gcm.Arm.GhashLaw] : VerifiedScrubbed target Impl.AesGcm.Arm.Fn.streamFinish (Spec.Gcm.streamFinishContract abi 2608) 0 :=
  verifiedScrubbedF (api := Spec.Gcm.streamFinishApi)
    { code := Impl.StackScratch.Arm.withStackScratch 2592 5 Impl.AesGcm.Arm.streamFinish
      verified := Proof.AesGcm.streamFinish_keyed (Verified.stack_le (by decide) streamFinish_framed
        Scrub.streamFinishSat : Verified Arm.target _ (Proof.AesGcm.streamFinishRoundsContract Arm.abi 2608)) }
    (Scrub.streamFinishOut _) (scrubSideF_of Scrub.streamFinish_code Scrub.frameOk_2608 _)

/-- `vg_aes_gcm_stream_verify`. -/
theorem streamVerify [VG.Proof.Gcm.Arm.GhashLaw] : VerifiedScrubbed target Impl.AesGcm.Arm.Fn.streamVerify (Spec.Gcm.streamVerifyContract abi 2608) 32 :=
  verifiedScrubbedF (api := Spec.Gcm.streamVerifyApi)
    { code := Impl.StackScratch.Arm.withStackScratch 2592 6 Impl.AesGcm.Arm.streamVerify
      verified := Proof.AesGcm.streamVerify_keyed (Verified.stack_le (by decide) streamVerify_framed
        Scrub.streamVerifySat : Verified Arm.target _ (Proof.AesGcm.streamVerifyRoundsContract Arm.abi 2608)) }
    (Scrub.streamVerifyOut _) (scrubSideF_of Scrub.streamVerify_code Scrub.frameOk_2608 _)

/-- `vg_aes_gcm_seal`. -/
theorem «seal» [VG.Proof.Gcm.Arm.GhashLaw] : VerifiedScrubbed target Impl.AesGcm.Arm.Fn.«seal» (Spec.Gcm.sealContract abi 2608) 0 :=
  verifiedScrubbedF (api := Spec.Gcm.sealApi)
    { code := Impl.StackScratch.Arm.withStackScratch 2592 5 Impl.AesGcm.Arm.«seal»
      verified := Proof.AesGcm.seal_keyed (Verified.stack_le (by decide) seal_framed
        Scrub.sealSat : Verified Arm.target _ (Proof.AesGcm.sealRoundsContract Arm.abi 2608)) }
    (Scrub.sealOut _) (scrubSideF_of Scrub.seal_code Scrub.frameOk_2608 _)

/-- `vg_aes_gcm_open`. -/
theorem «open» [VG.Proof.Gcm.Arm.GhashLaw] : VerifiedScrubbed target Impl.AesGcm.Arm.Fn.«open» (Spec.Gcm.openContract abi 2608) 32 :=
  verifiedScrubbedF (api := Spec.Gcm.openApi)
    { code := Impl.StackScratch.Arm.withStackScratch 2592 6 Impl.AesGcm.Arm.«open»
      verified := Proof.AesGcm.open_keyed (Verified.stack_le (by decide) open_framed
        Scrub.openSat : Verified Arm.target _ (Proof.AesGcm.openRoundsContract Arm.abi 2608)) }
    (Scrub.openOut _) (scrubSideF_of Scrub.open_code Scrub.frameOk_2608 _)

/-- `vg_aes_gcm_seal_gather`. -/
theorem sealGather [VG.Proof.Gcm.Arm.GhashLaw] : VerifiedScrubbed target Impl.AesGcm.Arm.Fn.sealGather (Spec.Gcm.sealGatherContract abi 2640) 0 :=
  verifiedScrubbedF (api := Spec.Gcm.sealGatherApi)
    { code := Impl.AesGcm.Arm.SealGather.sealGather Scrub.sealFnEntry.name Scrub.sealFnEntry.code
      verified := Proof.AesGcm.sealGather_keyed (Gather.sealGather_verified Scrub.sealFnEntry) }
    (Scrub.sealGatherOut _) (scrubSideF_of Scrub.sealGather_code Scrub.frameOk_2640 _)

/-- `vg_aes_gcm_open_to`. -/
theorem openTo [VG.Proof.Gcm.Arm.GhashLaw] : VerifiedScrubbed target Impl.AesGcm.Arm.Fn.openTo (Spec.Gcm.openToContract abi 2624) 32 :=
  verifiedScrubbedF (api := Spec.Gcm.openToApi)
    { code := Impl.StackScratch.Arm.withStackScratch 2608 8 Impl.AesGcm.Arm.openTo
      verified := Proof.AesGcm.openTo_keyed (Verified.stack_le (by decide) openTo_framed
        Scrub.openToSat : Verified Arm.target _ (Proof.AesGcm.openToRoundsContract Arm.abi 2624)) }
    (Scrub.openToOut _) (scrubSideF_of Scrub.openTo_code Scrub.frameOk_2624 _)

end VG.Proof.AesGcm.Arm.Fn
