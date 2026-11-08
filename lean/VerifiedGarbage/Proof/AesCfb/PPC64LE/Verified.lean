module

public import VerifiedGarbage.Proof.AesCfb.Rounds
public import VerifiedGarbage.Impl.AesCfb.PPC64LE
public import VerifiedGarbage.Proof.AesCbc.PPC64LE.Call
public import VerifiedGarbage.Proof.AesCfb.Spec
public import VerifiedGarbage.Spec.Cfb.Contract
import VerifiedGarbage.Proof.AesCfb.PPC64LE.Body
import VerifiedGarbage.Proof.AesCbc.PPC64LE.Verified
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
public import VerifiedGarbage.Proof.AesCbc.PPC64LE.Group
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.AesCfb.Rounds
meta import VerifiedGarbage.Impl.AesCfb.PPC64LE
meta import VerifiedGarbage.Proof.AesCbc.PPC64LE.Call
meta import VerifiedGarbage.Proof.AesCfb.Spec
meta import VerifiedGarbage.Spec.Cfb.Contract
meta import VerifiedGarbage.Proof.AesCfb.PPC64LE.Body
meta import VerifiedGarbage.Proof.AesCbc.PPC64LE.Verified
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.AesCbc.PPC64LE.Group
meta import VerifiedGarbage.Proof.Framework.Offset

/-!
# AES-CFB128 on PPC64LE: `Verified`

Correctness and constant time, from the loop AES-CBC's proofs share, a state
satisfying the precondition, and the shared contracts of
`Spec/Cfb/Contract.lean` (with no stack: a call stores nothing in memory).
-/

@[expose] public section

namespace VG.Proof.AesCfb.PPC64LE

open VG VG.PPC64LE VG.Impl.AesCfb.PPC64LE
open VG.Proof.AesCbc (cts)
open VG.Proof.AesCbc.PPC64LE
open VG.Proof.AesCbc (xorMem xorMem_frame xorMem_bytes copyMem copyMem_frame copyMem_bytes aesWith_state)
open VG.Impl.AesCbc.PPC64LE (copy slot saveSlots fixSlots advance8 encCall)
open VG.Spec.Aes (bytesAt)

/-! ## Decryption, eight blocks at a time -/

/-- CFB128 decryption extends its output one block at a time. -/
theorem cfbDec_steps : Steps (cfbMode false) fun R w x c => Spec.Cbc.xor x (Spec.Cbc.aesWith R w c) := by
  intro R w iv xs x
  simp only [cfbMode_out, cfbMode_chain, cfb, cts, Bool.false_eq_true, ite_false, Proof.AesCfb.decrypt_snoc]

/-- The chaining value after block `i` is block `i`. -/
theorem cfbDec_chain (s₀ : State) {i : Nat} (hi : i < N s₀) :
    chainK (cfbMode false) s₀ (i + 1) = blkOf s₀ i := by
  simp only [chainK, cfbMode_chain, cts, Bool.false_eq_true, ite_false, take_succ_blkOf s₀ hi,
    Proof.AesCbc.next_snoc]

/-- The arguments of the block function for the eight slots. -/
theorem callArgs8_wp {s : State} {Φ : State → Prop}
    (k : ∀ s', s'.gpr .r3 = s.gpr .r14 → s'.gpr .r4 = s.gpr .r15 → s'.gpr .r5 = s.gpr .r19 →
      s'.gpr .r6 = BitVec.ofNat 64 8 → s'.gpr .r7 = s.gpr .r19 + BitVec.ofNat 64 128 →
      (∀ r, r ∉ argRegs5 → s'.gpr r = s.gpr r) → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → Φ s') :
    WP isa (.block callArgs8) s Φ := by
  unfold callArgs8 Impl.AesCbc.PPC64LE.mov
  refine wp_mr fun s₁ u₁ => wp_mr fun s₂ u₂ => wp_mr fun s₃ u₃ => wp_li (by decide) fun s₄ u₄ =>
    wp_addi (by decide) (by decide) fun s₅ u₅ => wp_nil ?_
  refine k s₅ ?_ ?_ ?_ ?_ ?_ (fun r hr => ?_) ?_ ?_ ?_
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.gpr]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr,
      u₁.other _ (by decide)]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide)]
  · rw [u₅.other _ (by decide), u₄.gpr]
  · rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide)]
  · simp only [argRegs5, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h3, h4, h5, h6, h7⟩ := hr
    rw [u₅.other _ h7, u₄.other _ h6, u₃.other _ h5, u₂.other _ h4, u₁.other _ h3]
  · rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  · rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]

/-- The arguments of a call on the eight slots, with the working space after
them. -/
theorem callPre8S {s₀ : State} (hp : UPre s₀) {s : State}
    (r3 : s.gpr .r3 = W s₀) (r4 : s.gpr .r4 = s₀.gpr .r4) (r5 : s.gpr .r5 = S s₀)
    (r6 : s.gpr .r6 = BitVec.ofNat 64 8) (r7 : s.gpr .r7 = S s₀ + BitVec.ofNat 64 128)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    CallPre8 s (W s₀) (S s₀) (S s₀ + BitVec.ofNat 64 128) (R s₀) where
  r3 := r3
  r4 := by rw [r4, r4_ofNat]
  r5 := r5
  r6 := r6
  r7 := r7
  rounds := hp.rounds
  wd := hp.sch_scr.sub_right (Region.sub_prefix (by decide))
  ws := hp.sch_scr.sub_right (UPre.scr_sub (by decide))
  ds := (Offset.disjoint_base _ (by decide) (by have := hp.scr_wrap; omega)).symm
  wrap := by have := hp.scr_wrap; omega
  reads := by
    rw [hrd, hwr, hp.rd, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨schR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨scrR s₀, by simp, 128, rfl, by simp⟩
  writes := by
    rw [hwr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨scrR s₀, by simp, 128, rfl, by simp⟩

/-- The code before the call of a group: the slots, and the call's arguments. -/
theorem decA8_wp {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k + 8 ≤ N s₀) {s : State}
    (h : LInv (cfbMode false) s₀ k s) :
    WP isa (.block (saveSlots 7 ++ callArgs8)) s fun s₂ =>
      CallPre8 s₂ (W s₀) (S s₀) (S s₀ + BitVec.ofNat 64 128) (R s₀) ∧ (∀ r ∈ preserved, s₂.gpr r = s.gpr r) ∧
      s₂.rd = s.rd ∧ s₂.wr = s.wr ∧ Frame [⟨S s₀, 144⟩] s.mem s₂.mem ∧
      ∀ j < 8, bytesAt s₂.mem (sl s₀ j) 16 = chainK (cfbMode false) s₀ (k + j) :=
  saveSlots_wp hp (m := 7) (by decide) (by omega) h fun s₁ g₁ rd₁ wr₁ f₁ e₀ e₁ =>
    callArgs8_wp fun s₂ r3₂ r4₂ r5₂ r6₂ r7₂ o₂ mem₂ rd₂ wr₂ => by
      refine ⟨callPre8S hp (by rw [r3₂, g₁ _ (by decide), h.r14]) (by rw [r4₂, g₁ _ (by decide), h.r15])
        (by rw [r5₂, g₁ _ (by decide), h.r19]) r6₂ (by rw [r7₂, g₁ _ (by decide), h.r19])
        (by rw [rd₂, rd₁, h.rd]) (by rw [wr₂, wr₁, h.wr]), fun r hr => ?_, by rw [rd₂, rd₁],
        by rw [wr₂, wr₁], by rw [mem₂]; exact f₁, fun j hj => ?_⟩
      · obtain ⟨h3, h4, h5, h6, h7, h9, -⟩ := preserved_ne hr
        rw [o₂ r (by simp [argRegs5, h3, h4, h5, h6, h7]), g₁ r h9]
      · rw [mem₂]
        rcases Nat.eq_zero_or_pos j with rfl | hj0
        · exact e₀
        · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
          rw [e₁ i (by omega), ← Nat.add_assoc, cfbDec_chain s₀ (by omega)]

theorem decGroup_ok : GroupOk (cfbMode false) decGroup := by
  intro s₀ hp k hk s h
  refine WP.seq (WP.mono (decA8_wp hp hk h) fun s₂ ⟨pre, g₂, rd₂, wr₂, f₂, e₂⟩ => ?_)
  refine WP.seq (WP.mono (blk_call8 Proof.Aes.PPC64LE.encryptBlocks_framed encryptBlocks_noFrames pre)
    fun s₃ c => ?_)
  have g₃ (r : Reg) (hr : r ∈ preserved) : s₃.gpr r = s.gpr r := by rw [c.saved r hr, g₂ r hr]
  have hR₃ : s₃.rd ++ s₃.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by rw [c.rd, c.wr, rd₂, wr₂, h.regs hp]
  have hW₃ : s₃.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [c.wr, wr₂, h.wrs hp]
  have big₂ : Frame (Big s₀) s₀.mem s₂.mem :=
    (UPre.big_of h.frame).trans (f₂.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨scrR s₀, by simp, Region.sub_prefix (by decide)⟩)
  have cS (j : Nat) (hj : j < 8) : (⟨blk s₀ (k + j), 16⟩ : Region).Disjoint ⟨S s₀, 128⟩ :=
    (hp.dBG (by omega)).sub_right (Region.sub_prefix (by decide))
  -- The blocks and the enciphered slots after the call.
  have blk₃ (j : Nat) (hj : j < 8) : bytesAt s₃.mem (blk s₀ (k + j)) 16 = blkOf s₀ (k + j) := by
    rw [bytesAt_frame c.frame (one_disj (cS j hj)) (by decide),
      bytesAt_frame f₂ (one_disj (hp.dBG (by omega))) (by decide), h.blockAt (by omega) (by omega)]
  have slot₃ (j : Nat) (hj : j < 8) : bytesAt s₃.mem (sl s₀ j) 16 =
      Spec.Cbc.aesWith (R s₀) (wK s₀) (chainK (cfbMode false) s₀ (k + j)) := by
    have := c.out j hj
    show bytesAt s₃.mem (S s₀ + BitVec.ofNat 64 (16 * j)) 16 = _
    rw [this, ← aesWith_state, UPre.sched_bytes hp big₂]
    exact congrArg _ (e₂ j hj)
  rw [List.append_assoc]
  refine copy_wp (P := Iv s₀) (Q := blk s₀ (k + 7)) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [g₃ _ (by decide), h.r16, ofNat_zero_add]) (by rw [g₃ _ (by decide), h.r16])
    (by rw [g₃ _ (by decide), h.r17, blk_add]) (by rw [g₃ _ (by decide), h.r17, blk_add8])
    (by rw [hR₃]; exact in_rw (by simp) (hp.cBlk0 (k := k + 7) (by omega)))
    (by rw [hR₃]; exact in_rw (by simp) (hp.cBlk8 (k := k + 7) (by omega)))
    (by rw [hW₃]; exact in_rw (by simp) cIv0) (by rw [hW₃]; exact in_rw (by simp) cIv8)
    fun s₄ g₄ mem₄ rd₄ wr₄ => ?_
  have g₄' (r : Reg) (hr : r ∈ preserved) : s₄.gpr r = s.gpr r := by
    rw [g₄ r (preserved_ne hr).2.2.2.2.2.1, g₃ r hr]
  rw [fixSlots]
  refine fixes_wp hp 8 (by decide) hk (by rw [g₄' _ (by decide), h.r17]) (by rw [g₄' _ (by decide), h.r19])
    (by rw [rd₄, wr₄, hR₃]) (by rw [wr₄, hW₃]) fun s₅ g₅ rd₅ wr₅ f₅ e₅ => ?_
  have g₅' (r : Reg) (hr : r ∈ preserved) : s₅.gpr r = s.gpr r := by
    obtain ⟨-, -, -, -, -, h9, h10⟩ := preserved_ne hr
    rw [g₅ r h9 h10, g₄' r hr]
  refine advance8_regs (s := s₅) hk (by rw [g₅' _ (by decide), h.r17]) (by rw [g₅' _ (by decide), h.r18])
    fun s₆ r17₆ r18₆ keep₆ mem₆ rd₆ wr₆ => ?_
  have g (r : Reg) (hr : r ∈ preserved) (h17 : r ≠ .r17) (h18 : r ≠ .r18) : s₆.gpr r = s.gpr r := by
    rw [keep₆ r h17 h18, g₅' r hr]
  refine group_step cfbDec_steps hp hk h ?_ ?_ ?_ r17₆ r18₆ ?_ (fun r hr hv => ?_) ?_ ?_ ?_ (fun j hj => ?_) ?_
  · rw [g .r14 (by decide) (by decide) (by decide), h.r14]
  · rw [g .r15 (by decide) (by decide) (by decide), h.r15]
  · rw [g .r16 (by decide) (by decide) (by decide), h.r16]
  · rw [g .r19 (by decide) (by decide) (by decide), h.r19]
  · exact g r hr (fun e => hv (by simp [e])) (fun e => hv (by simp [e]))
  · rw [rd₆, rd₅, rd₄, c.rd, rd₂]
  · rw [wr₆, wr₅, wr₄, c.wr, wr₂]
  · rw [mem₆]
    refine (f₂.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨⟨S s₀, 2064⟩, by simp, slR_sub s₀⟩).trans ?_
    refine (c.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨S s₀, 2064⟩, by simp, Region.sub_prefix (by decide)⟩).trans ?_
    refine (by rw [mem₄]; exact (copyMem_frame _ _ _).sub (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨ivR s₀, by simp, fun _ h => h⟩) :
      Frame [⟨blk s₀ k, 128⟩, ivR s₀, ⟨S s₀, 2064⟩] s₃.mem s₄.mem).trans ?_
    exact f₅.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
  · rw [mem₆, e₅ j hj, mem₄, copyMem_other _ (hp.blk_iv (by omega)), copyMem_other _ (hp.dIS (by omega)).symm,
      blk₃ j hj, slot₃ j hj]
  · rw [mem₆, bytesAt_frame f₅ (one_disj (hp.dIB hk)) (by decide), mem₄,
      copyMem_bytes _ (hp.blk_iv (by omega)).symm, blk₃ 7 (by decide), cfbDec_chain s₀ (by omega)]

theorem decGroupPre_taint : ∃ h, (taint.check (Taint.ofRegs vars)
    (.block (saveSlots 7 ++ callArgs8)) h).isSome = true := ⟨_, by taint_decide⟩

theorem decGroupPost_taint : ∃ h, (taint.check (Taint.ofRegs [.r16, .r17, .r18, .r19])
    (.block (copy .r16 0 .r17 (16 * 7) ++ fixSlots ++ advance8)) h).isSome = true := ⟨_, by taint_decide⟩

theorem decGroup_ct : GroupCt (cfbMode false) decGroup :=
  fun hp hp' hq k => group_ct (D := fun s₀ _ => S s₀) (Sc := fun s₀ => S s₀ + BitVec.ofNat 64 128)
    (fun hq _ => pub_S hq) (fun hq => by rw [pub_S hq]) Proof.Aes.PPC64LE.encryptBlocks_correct
    Proof.Aes.PPC64LE.encryptBlocks_framed Proof.Aes.PPC64LE.encryptBlocks_ct encryptBlocks_noFrames
    decGroupPre_taint decGroupPost_taint
    (@fun _ hp _ hk _ h => WP.mono (decA8_wp hp hk h) fun _ a => ⟨a.1, a.2.1⟩) hp hp' hq k

theorem encrypt_correct (s : State) (hs : (modePPC64LE (cfbMode true)).pre s) :
    ∃ t s', Exec isa encrypt s t s' ∧ abiPreserved s s' ∧ (modePPC64LE (cfbMode true)).post s s' := by
  obtain ⟨t, s', he, hg, hlr, hp⟩ := whole_wp encBody_ok hs
  exact ⟨t, s', he, ⟨hg, Exec.sp he, hlr⟩, hp⟩

theorem decrypt_correct (s : State) (hs : (modePPC64LE (cfbMode false)).pre s) :
    ∃ t s', Exec isa decrypt s t s' ∧ abiPreserved s s' ∧ (modePPC64LE (cfbMode false)).post s s' := by
  obtain ⟨t, s', he, hg, hlr, hp⟩ := batched_wp decGroup_ok decBody_ok hs
  exact ⟨t, s', he, ⟨hg, Exec.sp he, hlr⟩, hp⟩

theorem encrypt_verified : Verified PPC64LE.target encrypt (Proof.AesCfb.encryptRoundsContract PPC64LE.abi) :=
  Verified.of_correct encrypt_correct (whole_ct encBody_ok encBody_ct) (by
    sig_implies [Proof.AesCfb.encryptRoundsContract, Spec.Cfb.aesSig, Spec.Cbc.aesSig, modePPC64LE, cfbMode, cfb, cts,
      PPC64LE.abi, PPC64LE.argRegs] [sat] using sat)

theorem decrypt_ct : ConstantTime isa (modePPC64LE (cfbMode false)).pre (modePPC64LE (cfbMode false)).pub decrypt :=
  batched_ct decGroup_ok decGroup_ct decBody_ok decBody_ct

theorem decrypt_verified : Verified PPC64LE.target decrypt (Proof.AesCfb.decryptRoundsContract PPC64LE.abi) :=
  Verified.of_correct decrypt_correct decrypt_ct (by
    sig_implies [Proof.AesCfb.decryptRoundsContract, Spec.Cfb.aesSig, Spec.Cbc.aesSig, modePPC64LE, cfbMode, cfb, cts,
      PPC64LE.abi, PPC64LE.argRegs] [sat] using sat)

end VG.Proof.AesCfb.PPC64LE
