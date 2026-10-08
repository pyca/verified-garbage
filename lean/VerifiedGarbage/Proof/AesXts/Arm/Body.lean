import VerifiedGarbage.Proof.AesXts.Arm.Steps
import VerifiedGarbage.Proof.AesCbc.Arm.CT

/-!
# XTS-AES on ARMv7: one block, and constant time

`body_ok'`: one run of a block takes the loop invariant AES-CBC's proofs
share (`Proof/AesCbc/Arm/Loop.lean`) from `k` blocks to `k + 1`, for
`xtsMode enc`, with the block function called as AES-CBC calls it
(`vg_aes_encrypt_blocks` for encryption, `vg_aes_decrypt_blocks` for
decryption). The tweak is XORed into the data block (`preA_wp`), which is
enciphered in place, the tweak is XORed in again, and the tweak is
multiplied by `α` (`Steps.lean`). `body_ct'`: it is constant time, by the
shared framework, with the call on the data block.
-/

namespace VG.Proof.AesXts.Arm

open VG VG.Arm VG.Impl.AesXts.Arm
open VG.Impl.AesCbc.Arm (callArgs encFrame decFrame)
open VG.Impl.CmacAes.Arm (advance xor4)
open VG.Proof.CmacAes.Arm (W R Dp N S schR dataR scrR argsR belowR savedMem add0)
open VG.Proof.AesOcb.Arm (BlkFn BlkCall BlkPost blkFrame blk_call encF decF)
open VG.Proof.AesGcm.Arm (below)
open VG.Proof.AesCbc (aesWith_state aesInvWith_state xorIn4_bytes set_prefix bytesAt_of_statesAt Mode ciphOf)
open VG.Proof.AesCbc.Arm
open VG.Spec.Aes (bytesAt)

theorem preA_wp {M : Mode} {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀)
    {s : State} (h : LInv M s₀ k s) :
    WP isa (.block pre) s
      (PreA s₀ k s (Proof.Cmac.xor4Mem s.mem (blk s₀ k) (blk s₀ k) (State.addr (Iv s₀)))) := by
  have hdf := hp.data_fit
  have hiv := hp.iv_fit
  have qN := hp.dataN hk
  have hd := hp.dataA hk
  have rw₀ : s.rd ++ s.wr = [schR s₀, argsR s₀, ivR s₀, dataR s₀, scrR s₀] := by rw [h.rd, h.wr, hp.rd, hp.wr]; rfl
  have w₀ : s.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [h.wr, hp.wr]
  refine xorIn_wp (by decide) (by decide) (by decide) (by decide) (by rw [h.r6]; omega)
    (by rw [h.r7, qN]; omega) (by rw [h.r6, add0, rw₀]; exact covIv (by simp))
    (by rw [h.r7, add0, hd, w₀]; exact covBlk hk (by simp)) fun s₁ g₁ => ?_
  have m₁ : s₁.mem = Proof.Cmac.xor4Mem s.mem (blk s₀ k) (blk s₀ k) (State.addr (Iv s₀)) := by
    rw [g₁.mem, h.r7, h.r6, add0, add0, hd]
  refine WP.mono (callArgs_wp hp hk (h.regs.of g₁.gpr g₁.sp g₁.rd g₁.wr)) fun s₂ a => ?_
  exact ⟨a.pre, fun r h0 h1 h2 h3 h12 hlr => by rw [a.keep r h0 h1 h2 h3 h12 hlr, g₁.gpr r h12 hlr],
    by rw [a.sp, g₁.sp], by rw [a.mem, m₁], by rw [a.rd, g₁.rd], by rw [a.wr, g₁.wr]⟩

theorem post_eq : post = xor4 .r7 .r6 .r7 0 0 0 ++ (mulA ++ advance) := by
  simp only [post, List.append_assoc]

/-- One block in the direction `enc`, by the block function `F`, which
computes `ciphOf enc` on bytes. -/
theorem body_ok' (enc : Bool) (F : BlkFn)
    (hf : ∀ R w m p, (F.f R w (Spec.Aes.stateAt m p)).toList = ciphOf enc R w (bytesAt m p 16)) :
    BodyOk (AesXts.xtsMode enc) (.seq (.block pre) (.seq (blkFrame F) (.block post))) := by
  intro s₀ hp k hk s h
  have hd := hp.dataA hk
  have qN := hp.dataN hk
  have hdf := hp.data_fit
  have hiv := hp.iv_fit
  refine WP.seq (WP.mono (preA_wp hp hk h) fun s₁ a => ?_)
  refine WP.seq (WP.mono (blk_call F a.pre) fun s₂ c => ?_)
  have rg₂ := post_regs F h.regs a c
  have hb : below s₁.sp = belowR s₀ := by rw [a.sp, h.sp]; rfl
  -- Memory so far.
  have f₁ : Frame [⟨blk s₀ k, 16⟩] s.mem s₁.mem := by rw [a.mem]; exact Proof.Cmac.xor4Mem_frame _ _ _ _
  have f₂ : Frame [⟨blk s₀ k, 16⟩, ⟨State.addr (S s₀), 2048⟩, belowR s₀] s₁.mem s₂.mem := by
    have fr := c.frame; rw [hb, hd] at fr; exact fr
  have fs₂ : Frame [⟨blk s₀ k, 16⟩, ivR s₀, ⟨State.addr (S s₀), 2064⟩, belowR s₀] s.mem s₂.mem :=
    (f₁.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact stepIn (.inl rfl)).trans
      (f₂.sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact stepIn (.inl rfl)
        · exact stepIn (.inr (.inr (.inl (Region.sub_prefix (by decide)))))
        · exact stepIn (.inr (.inr (.inr rfl))))
  have big₁ : Frame (Big s₀) s₀.mem s₁.mem := bigOf hp hk h.frame (f₁.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact stepIn (.inl rfl))
  have w₂ : s₂.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [rg₂.wr, hp.wr]
  have rw₂ : s₂.rd ++ s₂.wr = [schR s₀, argsR s₀, ivR s₀, dataR s₀, scrR s₀] := by
    rw [rg₂.rd, rg₂.wr, hp.rd, hp.wr]; rfl
  rw [post_eq]
  refine xorIn_wp (by decide) (by decide) (by decide) (by decide) (by rw [rg₂.r6]; omega)
    (by rw [rg₂.r7, qN]; omega) (by rw [rg₂.r6, add0, rw₂]; exact covIv (by simp))
    (by rw [rg₂.r7, add0, hd, w₂]; exact covBlk hk (by simp)) fun s₃ g₃ => ?_
  have m₃ : s₃.mem = Proof.Cmac.xor4Mem s₂.mem (blk s₀ k) (blk s₀ k) (State.addr (Iv s₀)) := by
    rw [g₃.mem, rg₂.r7, rg₂.r6, add0, add0, hd]
  have f₃ : Frame [⟨blk s₀ k, 16⟩] s₂.mem s₃.mem := by rw [m₃]; exact Proof.Cmac.xor4Mem_frame _ _ _ _
  have rg₃ := rg₂.of g₃.gpr g₃.sp g₃.rd g₃.wr
  have w₃ : s₃.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [rg₃.wr, hp.wr]
  have rw₃ : s₃.rd ++ s₃.wr = [schR s₀, argsR s₀, ivR s₀, dataR s₀, scrR s₀] := by
    rw [rg₃.rd, rg₃.wr, hp.rd, hp.wr]; rfl
  obtain ⟨s₄, run₄, g₄, sp₄, mem₄, rd₄, wr₄⟩ := mulA_ok s₃ (Q := State.addr (Iv s₀)) (by rw [rg₃.r6])
    (by rw [rg₃.r6]; omega)
    (fun d n hdn => by rw [rw₃]; exact ⟨ivR s₀, by simp, Offset.contains_base _ hdn (by omega)⟩)
    (fun d n hdn => by rw [w₃]; exact ⟨ivR s₀, by simp, Offset.contains_base _ hdn (by omega)⟩)
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨s₄, run₄, ?_⟩
  have f₄ : Frame [ivR s₀] s₃.mem s₄.mem := by rw [mem₄]; exact alphaMem_frame _ _
  have fStep : Frame [⟨blk s₀ k, 16⟩, ivR s₀, ⟨State.addr (S s₀), 2064⟩, belowR s₀] s.mem s₄.mem :=
    (fs₂.trans (f₃.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact stepIn (.inl rfl))).trans
      (f₄.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact stepIn (.inr (.inl rfl)))
  have callIv : ∀ r ∈ [⟨blk s₀ k, 16⟩, ⟨State.addr (S s₀), 2048⟩, belowR s₀], (ivR s₀).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (hp.blk_iv hk).symm
    · exact hp.iv_scr.sub_right (Region.sub_prefix (by decide))
    · exact hp.b_iv.symm
  have hlt : ((blks s₀).take k).length = k := by simp [Spec.Cbc.blocksAt]; omega
  have ivIn : bytesAt s₂.mem (State.addr (Iv s₀)) 16 = chainK (AesXts.xtsMode enc) s₀ k := by
    rw [Proof.Cmac.bytesAt_frame f₂ callIv (by decide), a.mem,
      Proof.Cmac.bytesAt_frame (Proof.Cmac.xor4Mem_frame _ _ _ _) (one (hp.blk_iv hk).symm) (by decide), h.iv]
  have newBlk : bytesAt s₄.mem (blk s₀ k) 16 =
      Spec.Xts.block (ciphOf enc (R s₀) (wK s₀)) (Spec.Xts.next (iv0 s₀) k)
        ((blks s₀)[k]'(by simp [Spec.Cbc.blocksAt]; exact hk)) := by
    rw [Proof.Cmac.bytesAt_frame f₄ (one (hp.blk_iv hk)) (by decide), m₃, xorIn4_bytes _ (hp.blk_iv hk), ivIn,
      ← hd, bytesAt_of_statesAt c.out, hd, hf, UPre.sched_bytes hp big₁, a.mem, xorIn4_bytes _ (hp.blk_iv hk),
      h.block hk, h.iv]
    simp only [chainK, AesXts.xtsMode_chain, hlt]
    rfl
  have newIv : bytesAt s₄.mem (State.addr (Iv s₀)) 16 = Spec.Xts.mulAlpha (chainK (AesXts.xtsMode enc) s₀ k) := by
    rw [mem₄, alphaMem_bytes, m₃,
      Proof.Cmac.bytesAt_frame (Proof.Cmac.xor4Mem_frame _ _ _ _) (one (hp.blk_iv hk).symm) (by decide), ivIn]
  have hl : (outK (AesXts.xtsMode enc) s₀ k).length = k := by
    rw [outK, Mode.length_out]; simp [Spec.Cbc.blocksAt]; omega
  have outSucc :
      outK (AesXts.xtsMode enc) s₀ (k + 1) = outK (AesXts.xtsMode enc) s₀ k ++ [bytesAt s₄.mem (blk s₀ k) 16] := by
    rw [newBlk]
    simp only [outK, AesXts.xtsMode_out, take_succ_blks s₀ hk, AesXts.crypt_snoc, hlt]
  have k₄ (r : Reg) (h₁ : r ≠ .r0 ∧ r ≠ .r1 ∧ r ≠ .r2 ∧ r ≠ .r3 ∧ r ≠ .r12 ∧ r ≠ .lr) : s₄.gpr r = s₃.gpr r :=
    g₄ r h₁.1 h₁.2.1 h₁.2.2.1 h₁.2.2.2.1 h₁.2.2.2.2.1 h₁.2.2.2.2.2
  have rg₄ : Regs s₀ k s₄ := ⟨by rw [k₄ _ (by decide), rg₃.r4], by rw [k₄ _ (by decide), rg₃.r5],
    by rw [k₄ _ (by decide), rg₃.r6], by rw [k₄ _ (by decide), rg₃.r7], by rw [k₄ _ (by decide), rg₃.r10],
    by rw [sp₄, rg₃.sp], by rw [rd₄, rg₃.rd], by rw [wr₄, rg₃.wr]⟩
  refine advance_wp hp hk rg₄
    (by rw [k₄ _ (by decide), g₃.gpr _ (by decide) (by decide), kept a c (.inl rfl), h.r8])
    (by rw [k₄ _ (by decide), g₃.gpr _ (by decide) (by decide), kept a c (.inr rfl), h.r11])
    (h.frame.trans (stepFrame hk fStep)) ?_ ?_
  · rw [hp.blocksAt_step hk fStep, h.data, outSucc,
      set_prefix _ _ _ hl (by simp [Spec.Cbc.blocksAt]; exact hk)]
  · rw [newIv]
    simp only [chainK, AesXts.xtsMode_chain, take_succ_blks s₀ hk, List.length_append, List.length_singleton,
      hlt, AesXts.next_succ]

theorem encBody_ok : BodyOk (AesXts.xtsMode true) (.seq (.block pre) (.seq encFrame (.block post))) := by
  rw [encFrame_eq]
  exact body_ok' true encF fun _ _ _ _ => (aesWith_state _ _ _ _).symm

theorem decBody_ok : BodyOk (AesXts.xtsMode false) (.seq (.block pre) (.seq decFrame (.block post))) := by
  rw [decFrame_eq]
  exact body_ok' false decF fun _ _ _ _ => (aesInvWith_state _ _ _ _).symm

/-! ## Constant time -/

theorem pre_taint : ∃ h, (taint.check (Taint.ofRegs vars) (.block pre) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem post_taint : ∃ h, (taint.check (Taint.ofRegs postVars) (.block post) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem encBody_ct : BodyCt (AesXts.xtsMode true) (.seq (.block pre) (.seq encFrame (.block post))) :=
  fun hp hp' hq k => by
    rw [encFrame_eq]
    exact body_ct encF (fun hq k => pub_D32 hq k) pre_taint post_taint
      (@fun _ hp _ hk _ h => WP.mono (preA_wp hp hk h) fun _ a => Mid.of h a) hp hp' hq k

theorem decBody_ct : BodyCt (AesXts.xtsMode false) (.seq (.block pre) (.seq decFrame (.block post))) :=
  fun hp hp' hq k => by
    rw [decFrame_eq]
    exact body_ct decF (fun hq k => pub_D32 hq k) pre_taint post_taint
      (@fun _ hp _ hk _ h => WP.mono (preA_wp hp hk h) fun _ a => Mid.of h a) hp hp' hq k

end VG.Proof.AesXts.Arm
