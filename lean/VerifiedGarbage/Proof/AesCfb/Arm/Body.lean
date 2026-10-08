import VerifiedGarbage.Proof.AesCfb.Spec
import VerifiedGarbage.Proof.AesOfb.Arm.Body
import VerifiedGarbage.Impl.AesCfb.Arm

/-!
# AES-CFB128 on ARMv7: one block, and constant time

`encBody_ok` and `decBody_ok`: one run of `body` takes the loop invariant
AES-CBC's proofs share (`Proof/AesCbc/Arm/Loop.lean`) from `k` blocks to
`k + 1`, for `cfbMode`. The code before the call and the call are AES-OFB's
(`Proof/AesOfb/Arm/Body.lean`). `encBody_ct` and `decBody_ct`: they are
constant time, by the shared framework, with the call on the block at `iv`.
-/

namespace VG.Proof.AesCfb.Arm

open VG VG.Arm VG.Impl.AesCfb.Arm
open VG.Impl.CmacAes.Arm (advance xor4)
open VG.Impl.AesCbc.Arm (whole encFrame zero4)
open VG.Impl.AesOfb.Arm (ivArgs)
open VG.Proof.CmacAes.Arm (W R Dp N S schR dataR scrR argsR belowR savedMem add0)
open VG.Proof.AesOcb.Arm (BlkFn BlkCall BlkPost blkFrame blk_call encF)
open VG.Proof.AesGcm.Arm (below)
open VG.Proof.AesOfb.Arm (IvA ivA_wp keptIv mid_of)
open VG.Proof.AesCbc
open VG.Proof.AesCbc.Arm
open VG.Spec.Aes (bytesAt)

/-- What the code before the call, the call and the output block into the
data block leave, for either direction. -/
structure AfterXor (s₀ : State) (k : Nat) (s s₃ : State) : Prop where
  regs : Regs s₀ k s₃
  r8 : s₃.gpr .r8 = s.gpr .r8
  r11 : s₃.gpr .r11 = s.gpr .r11
  rw : s₃.rd ++ s₃.wr = [schR s₀, argsR s₀, ivR s₀, dataR s₀, scrR s₀]
  w : s₃.wr = [ivR s₀, dataR s₀, scrR s₀]
  frame : Frame [⟨blk s₀ k, 16⟩, ivR s₀, ⟨State.addr (S s₀), 2064⟩, belowR s₀] s.mem s₃.mem
  blk : bytesAt s₃.mem (blk s₀ k) 16 =
    Spec.Cbc.xor (bytesAt s.mem (blk s₀ k) 16) (bytesAt s₃.mem (State.addr (Iv s₀)) 16)
  iv : bytesAt s₃.mem (State.addr (Iv s₀)) 16 =
    Spec.Cbc.aesWith (R s₀) (wK s₀) (bytesAt s.mem (State.addr (Iv s₀)) 16)

theorem head_ok {M : Mode} {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s : State}
    (h : LInv M s₀ k s) (rest : List Instr) {Q : State → Prop}
    (hq : ∀ s₃, AfterXor s₀ k s s₃ → WP isa (.block rest) s₃ Q) :
    WP isa (body (xor4 .r7 .r6 .r7 0 0 0 ++ rest)) s Q := by
  have hd := hp.dataA hk
  have qN := hp.dataN hk
  have hdf := hp.data_fit
  have hiv := hp.iv_fit
  refine WP.seq (WP.mono (ivA_wp hp h) fun s₁ a => ?_)
  rw [encFrame_eq]
  refine WP.seq (WP.mono (blk_call encF a.pre) fun s₂ c => ?_)
  have hb : below s₁.sp = belowR s₀ := by rw [a.sp, h.sp]; rfl
  have rg₂ : Regs s₀ k s₂ :=
    ⟨by rw [keptIv a c (by simp [preserved]) (by decide), h.r4],
      by rw [keptIv a c (by simp [preserved]) (by decide), h.r5],
      by rw [keptIv a c (by simp [preserved]) (by decide), h.r6],
      by rw [keptIv a c (by simp [preserved]) (by decide), h.r7],
      by rw [keptIv a c (by simp [preserved]) (by decide), h.r10], by rw [c.sp, a.sp, h.sp],
      by rw [c.rd, a.rd, h.rd], by rw [c.wr, a.wr, h.wr]⟩
  have f₂ : Frame [ivR s₀, ⟨State.addr (S s₀), 2048⟩, belowR s₀] s.mem s₂.mem := by
    have fr := c.frame; rw [hb, a.mem] at fr; exact fr
  have w₂ : s₂.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [rg₂.wr, hp.wr]
  have rw₂ : s₂.rd ++ s₂.wr = [schR s₀, argsR s₀, ivR s₀, dataR s₀, scrR s₀] := by
    rw [rg₂.rd, rg₂.wr, hp.rd, hp.wr]; rfl
  refine xorIn_wp (by decide) (by decide) (by decide) (by decide) (by rw [rg₂.r6]; omega)
    (by rw [rg₂.r7, qN]; omega) (by rw [rg₂.r6, add0, rw₂]; exact covIv (by simp))
    (by rw [rg₂.r7, add0, hd, w₂]; exact covBlk hk (by simp)) fun s₃ g₃ => hq s₃ ?_
  have m₃ : s₃.mem = Proof.Cmac.xor4Mem s₂.mem (blk s₀ k) (blk s₀ k) (State.addr (Iv s₀)) := by
    rw [g₃.mem, rg₂.r7, rg₂.r6, add0, add0, hd]
  have f₃ : Frame [⟨blk s₀ k, 16⟩] s₂.mem s₃.mem := by rw [m₃]; exact Proof.Cmac.xor4Mem_frame _ _ _ _
  have big : Frame (Big s₀) s₀.mem s.mem := UPre.big_of h.frame
  have iv₃ : bytesAt s₃.mem (State.addr (Iv s₀)) 16 = bytesAt s₂.mem (State.addr (Iv s₀)) 16 :=
    Proof.Cmac.bytesAt_frame f₃ (one (hp.blk_iv hk).symm) (by decide)
  refine ⟨rg₂.of g₃.gpr g₃.sp g₃.rd g₃.wr,
    by rw [g₃.gpr _ (by decide) (by decide), keptIv a c (by simp [preserved]) (by decide)],
    by rw [g₃.gpr _ (by decide) (by decide), keptIv a c (by simp [preserved]) (by decide)],
    by rw [g₃.rd, g₃.wr, rw₂], by rw [g₃.wr, w₂],
    (f₂.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact stepIn (.inr (.inl rfl))
      · exact stepIn (.inr (.inr (.inl (Region.sub_prefix (by decide)))))
      · exact stepIn (.inr (.inr (.inr rfl)))).trans
      (f₃.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact stepIn (.inl rfl)), ?_, ?_⟩
  · rw [iv₃, m₃, xorIn4_bytes _ (hp.blk_iv hk),
      Proof.Cmac.bytesAt_frame f₂ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact hp.blk_iv hk
        · exact (hp.data_scr.sub_left (UPre.data_sub hk)).sub_right (Region.sub_prefix (by decide))
        · exact hp.b_data.symm.sub_left (UPre.data_sub hk)) (by decide)]
  · rw [iv₃, bytesAt_of_statesAt c.out, show encF.f = Spec.Aes.cipher from rfl, a.mem, UPre.sched_bytes hp big,
      ← aesWith_state]

/-- The invariant after a block, from what the block leaves. -/
theorem linv_succ {M : Mode} {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s s₃ s₄ : State}
    (h : LInv M s₀ k s) (x : AfterXor s₀ k s s₃) (g₄ : Moved s₃ s₄.mem s₄)
    (f₄ : Frame [ivR s₀] s₃.mem s₄.mem)
    (hout : outK M s₀ (k + 1) = outK M s₀ k ++ [bytesAt s₄.mem (blk s₀ k) 16])
    (hiv : bytesAt s₄.mem (State.addr (Iv s₀)) 16 = chainK M s₀ (k + 1)) :
    WP isa (.block advance) s₄ fun s' => LInv M s₀ (k + 1) s' ∧ s'.z = decide (N s₀ - (k + 1) = 0) := by
  have fStep : Frame [⟨blk s₀ k, 16⟩, ivR s₀, ⟨State.addr (S s₀), 2064⟩, belowR s₀] s.mem s₄.mem :=
    x.frame.trans (f₄.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact stepIn (.inr (.inl rfl)))
  have hl' : (outK M s₀ k).length = k := by
    rw [outK, Mode.length_out]; simp [Spec.Cbc.blocksAt]; omega
  refine advance_wp hp hk (x.regs.of g₄.gpr g₄.sp g₄.rd g₄.wr)
    (by rw [g₄.gpr _ (by decide) (by decide), x.r8, h.r8])
    (by rw [g₄.gpr _ (by decide) (by decide), x.r11, h.r11])
    (h.frame.trans (stepFrame hk fStep)) ?_ hiv
  rw [hp.blocksAt_step hk fStep, h.data, hout, set_prefix _ _ _ hl' (by simp [Spec.Cbc.blocksAt]; exact hk)]

theorem encPost_eq : encPost = xor4 .r7 .r6 .r7 0 0 0 ++ (zero4 .r6 0 ++ (xor4 .r6 .r7 .r6 0 0 0 ++ advance)) := by
  simp only [encPost, List.append_assoc]

theorem decPost_eq : decPost = xor4 .r7 .r6 .r7 0 0 0 ++ (xor4 .r6 .r7 .r6 0 0 0 ++ advance) := by
  simp only [decPost, List.append_assoc]

theorem encBody_ok : BodyOk (cfbMode true) (body encPost) := by
  intro s₀ hp k hk s h
  have hd := hp.dataA hk
  have qN := hp.dataN hk
  have hdf := hp.data_fit
  have hiv := hp.iv_fit
  rw [encPost_eq]
  refine head_ok hp hk h _ fun s₃ x => ?_
  refine copy_wp (by decide) (by decide) (by decide) (by decide) (by rw [x.regs.r7, qN]; omega)
    (by rw [x.regs.r6]; omega) (by rw [x.regs.r7, add0, hd, x.rw]; exact covBlk hk (by simp))
    (by rw [x.regs.r6, add0, x.w]; exact covIv (by simp)) fun s₄ g₄ => ?_
  have m₄ : s₄.mem = copy4Mem s₃.mem (State.addr (Iv s₀)) (blk s₀ k) := by
    rw [g₄.mem, x.regs.r6, x.regs.r7, add0, add0, hd]
  have f₄ : Frame [ivR s₀] s₃.mem s₄.mem := by rw [m₄]; exact copy4Mem_frame _ _ _
  have b₄ : bytesAt s₄.mem (blk s₀ k) 16 = bytesAt s₃.mem (blk s₀ k) 16 :=
    Proof.Cmac.bytesAt_frame f₄ (one (hp.blk_iv hk)) (by decide)
  have i₄ : bytesAt s₄.mem (State.addr (Iv s₀)) 16 = bytesAt s₄.mem (blk s₀ k) 16 := by
    rw [b₄, m₄, copy4Mem_bytes _ (hp.blk_iv hk).symm]
  have newBlk : bytesAt s₄.mem (blk s₀ k) 16 =
      Spec.Cbc.xor ((blks s₀)[k]'(by simp [Spec.Cbc.blocksAt]; exact hk))
        (Spec.Cbc.aesWith (R s₀) (wK s₀) (chainK (cfbMode true) s₀ k)) := by
    rw [b₄, x.blk, h.block hk, x.iv, h.iv]
  have outSucc :
      outK (cfbMode true) s₀ (k + 1) = outK (cfbMode true) s₀ k ++ [bytesAt s₄.mem (blk s₀ k) 16] := by
    rw [newBlk]
    simp only [outK, chainK, cfbMode_out, cfbMode_chain, cfb, cts, ite_true, take_succ_blks s₀ hk,
      encrypt_snoc]
  refine linv_succ hp hk h x ⟨g₄.gpr, rfl, g₄.rd, g₄.wr, g₄.sp⟩ f₄ outSucc ?_
  rw [i₄]
  simp only [chainK, cfbMode_chain, cts, ite_true, outSucc, next_snoc]

theorem decBody_ok : BodyOk (cfbMode false) (body decPost) := by
  intro s₀ hp k hk s h
  have hd := hp.dataA hk
  have qN := hp.dataN hk
  have hdf := hp.data_fit
  have hiv := hp.iv_fit
  rw [decPost_eq]
  refine head_ok hp hk h _ fun s₃ x => ?_
  refine xorIn_wp (by decide) (by decide) (by decide) (by decide) (by rw [x.regs.r7, qN]; omega)
    (by rw [x.regs.r6]; omega) (by rw [x.regs.r7, add0, hd, x.rw]; exact covBlk hk (by simp))
    (by rw [x.regs.r6, add0, x.w]; exact covIv (by simp)) fun s₄ g₄ => ?_
  have m₄ : s₄.mem = Proof.Cmac.xor4Mem s₃.mem (State.addr (Iv s₀)) (State.addr (Iv s₀)) (blk s₀ k) := by
    rw [g₄.mem, x.regs.r6, x.regs.r7, add0, add0, hd]
  have f₄ : Frame [ivR s₀] s₃.mem s₄.mem := by rw [m₄]; exact Proof.Cmac.xor4Mem_frame _ _ _ _
  have b₄ : bytesAt s₄.mem (blk s₀ k) 16 = bytesAt s₃.mem (blk s₀ k) 16 :=
    Proof.Cmac.bytesAt_frame f₄ (one (hp.blk_iv hk)) (by decide)
  have hb := h.block hk
  have i₄ : bytesAt s₄.mem (State.addr (Iv s₀)) 16 = (blks s₀)[k]'(by simp [Spec.Cbc.blocksAt]; exact hk) := by
    rw [m₄, xorIn4_bytes _ (hp.blk_iv hk).symm, x.blk, hb]
    exact xor_xor_cancel (by simp [Spec.Aes.bytesAt, ← hb])
  have newBlk : bytesAt s₄.mem (blk s₀ k) 16 =
      Spec.Cbc.xor ((blks s₀)[k]'(by simp [Spec.Cbc.blocksAt]; exact hk))
        (Spec.Cbc.aesWith (R s₀) (wK s₀) (chainK (cfbMode false) s₀ k)) := by
    rw [b₄, x.blk, hb, x.iv, h.iv]
  have outSucc :
      outK (cfbMode false) s₀ (k + 1) = outK (cfbMode false) s₀ k ++ [bytesAt s₄.mem (blk s₀ k) 16] := by
    rw [newBlk]
    simp only [outK, chainK, cfbMode_out, cfbMode_chain, cfb, cts, Bool.false_eq_true, ite_false,
      take_succ_blks s₀ hk, decrypt_snoc]
  refine linv_succ hp hk h x ⟨g₄.gpr, rfl, g₄.rd, g₄.wr, g₄.sp⟩ f₄ outSucc ?_
  rw [i₄]
  simp only [chainK, cfbMode_chain, cts, Bool.false_eq_true, ite_false, take_succ_blks s₀ hk, next_snoc]

/-! ## Constant time -/

theorem pre_taint : ∃ h, (taint.check (Taint.ofRegs vars) (.block ivArgs) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem encPost_taint : ∃ h, (taint.check (Taint.ofRegs postVars) (.block encPost) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem decPost_taint : ∃ h, (taint.check (Taint.ofRegs postVars) (.block decPost) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem encBody_ct : BodyCt (cfbMode true) (body encPost) := fun hp hp' hq k => by
  rw [body, encFrame_eq]
  exact VG.Proof.AesCbc.Arm.body_ct encF (D := fun s₀ _ => Iv s₀) (fun hq _ => pub_Iv hq) pre_taint
    encPost_taint (@fun _ hp _ _ _ h => WP.mono (ivA_wp hp h) fun _ a => mid_of h a) hp hp' hq k

theorem decBody_ct : BodyCt (cfbMode false) (body decPost) := fun hp hp' hq k => by
  rw [body, encFrame_eq]
  exact VG.Proof.AesCbc.Arm.body_ct encF (D := fun s₀ _ => Iv s₀) (fun hq _ => pub_Iv hq) pre_taint
    decPost_taint (@fun _ hp _ _ _ h => WP.mono (ivA_wp hp h) fun _ a => mid_of h a) hp hp' hq k

end VG.Proof.AesCfb.Arm
