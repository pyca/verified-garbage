module

public import VerifiedGarbage.Proof.Framework.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.AesGcm.Arm.Frame
public import VerifiedGarbage.Proof.AesGcm.Arm.Gather.Verified
public import VerifiedGarbage.Proof.AesGcm.Arm.OpenTo
public import VerifiedGarbage.Proof.AesGcm.RoundsTo
import VerifiedGarbage.Proof.AesGcm.Scratch
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Gcm.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Scrub
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
Each is registered followed by a wipe of that stack and by instructions that
set the registers a callee may change, but the result, and the flags to
constants (`Arm.Scrub.scrubRegF`).

That stack is a frame of the model (`Arm.Scrub.FrameOk`): where the number
of bytes a proof is stated with is not one (2568, 2584, 2600, 2620), the
function is registered with the next that is (2576, 2592, 2608, 2624;
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
    armStack (Impl.StackScratch.Arm.withRegScratch 2560 .r3 init) ≤ 2576 ∧
      noIcall (Impl.StackScratch.Arm.withRegScratch 2560 .r3 init) = true := by
  lit_decide

theorem streamInit_code :
    armStack (Impl.StackScratch.Arm.withStackScratch 2576 0 streamInit) ≤ 2592 ∧
      noIcall (Impl.StackScratch.Arm.withStackScratch 2576 0 streamInit) = true := by
  lit_decide

theorem streamAad_code :
    armStack (Impl.StackScratch.Arm.withStackScratch 2576 2 streamAad) ≤ 2592 ∧
      noIcall (Impl.StackScratch.Arm.withStackScratch 2576 2 streamAad) = true := by
  lit_decide

theorem streamEncrypt_code :
    armStack (Impl.StackScratch.Arm.withStackScratch 2592 6 streamEncrypt) ≤ 2608 ∧
      noIcall (Impl.StackScratch.Arm.withStackScratch 2592 6 streamEncrypt) = true := by
  lit_decide

theorem streamDecrypt_code :
    armStack (Impl.StackScratch.Arm.withStackScratch 2592 6 streamDecrypt) ≤ 2608 ∧
      noIcall (Impl.StackScratch.Arm.withStackScratch 2592 6 streamDecrypt) = true := by
  lit_decide

theorem streamFinish_code :
    armStack (Impl.StackScratch.Arm.withStackScratch 2592 5 streamFinish) ≤ 2608 ∧
      noIcall (Impl.StackScratch.Arm.withStackScratch 2592 5 streamFinish) = true := by
  lit_decide

theorem streamVerify_code :
    armStack (Impl.StackScratch.Arm.withStackScratch 2592 6 streamVerify) ≤ 2608 ∧
      noIcall (Impl.StackScratch.Arm.withStackScratch 2592 6 streamVerify) = true := by
  lit_decide

theorem seal_code :
    armStack (Impl.StackScratch.Arm.withStackScratch 2592 5 «seal») ≤ 2608 ∧
      noIcall (Impl.StackScratch.Arm.withStackScratch 2592 5 «seal») = true := by
  lit_decide

theorem open_code :
    armStack (Impl.StackScratch.Arm.withStackScratch 2592 6 «open») ≤ 2608 ∧
      noIcall (Impl.StackScratch.Arm.withStackScratch 2592 6 «open») = true := by
  lit_decide

theorem sealGather_code [VG.Proof.Gcm.Arm.GhashLaw] :
    armStack (Impl.AesGcm.Arm.SealGather.sealGather sealFnEntry.name sealFnEntry.code) ≤ 2640 ∧
      noIcall (Impl.AesGcm.Arm.SealGather.sealGather sealFnEntry.name sealFnEntry.code) = true := by
  simp only [sealFnEntry, Gather.sealFn]
  lit_decide

theorem openTo_code :
    armStack (Impl.StackScratch.Arm.withStackScratch 2608 8 openTo) ≤ 2624 ∧
      noIcall (Impl.StackScratch.Arm.withStackScratch 2608 8 openTo) = true := by
  lit_decide

/-! ## The registrations

Over the law of `vg_ghash` (`Gcm.Arm.GhashLaw`), which the registration file
gives, so that this module does not import its algebra. -/

variable [VG.Proof.Gcm.Arm.GhashLaw]

/-- `vg_aes_gcm_init`. -/
def initReg : Registration Spec.Gcm.initApi Arm.target :=
  scrubRegF {
      code := Impl.StackScratch.Arm.withRegScratch 2560 .r3 init
      verified := (Verified.stack_le (by decide) init_framed initSat :
        Verified Arm.target _ (Spec.Gcm.initContract Arm.abi 2576)) }
    init_code.1 init_code.2 frameOk_2576 (initOut _) rfl

/-- `vg_aes_gcm_stream_init`. -/
def streamInitReg : Registration Spec.Gcm.streamInitApi Arm.target :=
  scrubRegF {
      code := Impl.StackScratch.Arm.withStackScratch 2576 0 streamInit
      verified := (Verified.stack_le (by decide) streamInit_framed streamInitSat :
        Verified Arm.target _ (Spec.Gcm.streamInitContract Arm.abi 2592)) }
    streamInit_code.1 streamInit_code.2 frameOk_2592 (streamInitOut _) rfl

/-- `vg_aes_gcm_stream_aad`. -/
def streamAadReg : Registration Spec.Gcm.streamAadApi Arm.target :=
  scrubRegF {
      code := Impl.StackScratch.Arm.withStackScratch 2576 2 streamAad
      verified := (Verified.stack_le (by decide) streamAad_framed streamAadSat :
        Verified Arm.target _ (Spec.Gcm.streamAadContract Arm.abi 2592)) }
    streamAad_code.1 streamAad_code.2 frameOk_2592 (streamAadOut _) rfl

/-- `vg_aes_gcm_stream_encrypt`. -/
def streamEncryptReg : Registration Spec.Gcm.streamEncryptApi Arm.target :=
  scrubRegF {
      code := Impl.StackScratch.Arm.withStackScratch 2592 6 streamEncrypt
      verified := Proof.AesGcm.streamEncrypt_keyed (Verified.stack_le (by decide) streamEncrypt_framed
        streamEncryptSat : Verified Arm.target _ (Proof.AesGcm.streamEncryptRoundsContract Arm.abi 2608)) }
    streamEncrypt_code.1 streamEncrypt_code.2 frameOk_2608 (streamEncryptOut _) rfl

/-- `vg_aes_gcm_stream_decrypt`. -/
def streamDecryptReg : Registration Spec.Gcm.streamDecryptApi Arm.target :=
  scrubRegF {
      code := Impl.StackScratch.Arm.withStackScratch 2592 6 streamDecrypt
      verified := Proof.AesGcm.streamDecrypt_keyed (Verified.stack_le (by decide) streamDecrypt_framed
        streamDecryptSat : Verified Arm.target _ (Proof.AesGcm.streamDecryptRoundsContract Arm.abi 2608)) }
    streamDecrypt_code.1 streamDecrypt_code.2 frameOk_2608 (streamDecryptOut _) rfl

/-- `vg_aes_gcm_stream_finish`. -/
def streamFinishReg : Registration Spec.Gcm.streamFinishApi Arm.target :=
  scrubRegF {
      code := Impl.StackScratch.Arm.withStackScratch 2592 5 streamFinish
      verified := Proof.AesGcm.streamFinish_keyed (Verified.stack_le (by decide) streamFinish_framed
        streamFinishSat : Verified Arm.target _ (Proof.AesGcm.streamFinishRoundsContract Arm.abi 2608)) }
    streamFinish_code.1 streamFinish_code.2 frameOk_2608 (streamFinishOut _) rfl

/-- `vg_aes_gcm_stream_verify`. -/
def streamVerifyReg : Registration Spec.Gcm.streamVerifyApi Arm.target :=
  scrubRegF {
      code := Impl.StackScratch.Arm.withStackScratch 2592 6 streamVerify
      verified := Proof.AesGcm.streamVerify_keyed (Verified.stack_le (by decide) streamVerify_framed
        streamVerifySat : Verified Arm.target _ (Proof.AesGcm.streamVerifyRoundsContract Arm.abi 2608)) }
    streamVerify_code.1 streamVerify_code.2 frameOk_2608 (streamVerifyOut _) rfl

/-- `vg_aes_gcm_seal`. -/
def sealReg : Registration Spec.Gcm.sealApi Arm.target :=
  scrubRegF {
      code := Impl.StackScratch.Arm.withStackScratch 2592 5 «seal»
      verified := Proof.AesGcm.seal_keyed (Verified.stack_le (by decide) seal_framed
        sealSat : Verified Arm.target _ (Proof.AesGcm.sealRoundsContract Arm.abi 2608)) }
    seal_code.1 seal_code.2 frameOk_2608 (sealOut _) rfl

/-- `vg_aes_gcm_open`. -/
def openReg : Registration Spec.Gcm.openApi Arm.target :=
  scrubRegF {
      code := Impl.StackScratch.Arm.withStackScratch 2592 6 «open»
      verified := Proof.AesGcm.open_keyed (Verified.stack_le (by decide) open_framed
        openSat : Verified Arm.target _ (Proof.AesGcm.openRoundsContract Arm.abi 2608)) }
    open_code.1 open_code.2 frameOk_2608 (openOut _) rfl

/-- `vg_aes_gcm_seal_gather`. -/
def sealGatherReg : Registration Spec.Gcm.sealGatherApi Arm.target :=
  scrubRegF {
      code := Impl.AesGcm.Arm.SealGather.sealGather sealFnEntry.name sealFnEntry.code
      verified := Proof.AesGcm.sealGather_keyed (Gather.sealGather_verified sealFnEntry) }
    sealGather_code.1 sealGather_code.2 frameOk_2640 (sealGatherOut _) rfl

/-- `vg_aes_gcm_open_to`. -/
def openToReg : Registration Spec.Gcm.openToApi Arm.target :=
  scrubRegF {
      code := Impl.StackScratch.Arm.withStackScratch 2608 8 openTo
      verified := Proof.AesGcm.openTo_keyed (Verified.stack_le (by decide) openTo_framed
        openToSat : Verified Arm.target _ (Proof.AesGcm.openToRoundsContract Arm.abi 2624)) }
    openTo_code.1 openTo_code.2 frameOk_2624 (openToOut _) rfl

end VG.Proof.AesGcm.Arm.Scrub
