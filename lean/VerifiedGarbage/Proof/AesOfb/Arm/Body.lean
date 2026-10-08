import VerifiedGarbage.Proof.AesOfb.Spec
import VerifiedGarbage.Proof.AesCbc.Arm.CT
import VerifiedGarbage.Impl.AesOfb.Arm

/-!
# AES-OFB on ARMv7: one block, and constant time

`body_ok`: one run of `body` takes the loop invariant AES-CBC's proofs
share (`Proof/AesCbc/Arm/Loop.lean`) from `k` blocks to `k + 1`, for
`ofbMode`. `body_ct`: it is constant time, by the shared framework, with the
call on the block at `iv`.
-/

namespace VG.Proof.AesOfb.Arm

open VG VG.Arm VG.Impl.AesOfb.Arm
open VG.Impl.CmacAes.Arm (advance xor4)
open VG.Impl.AesCbc.Arm (whole encFrame)
open VG.Proof.CmacAes.Arm (W R Dp N S schR dataR scrR argsR belowR savedMem add0)
open VG.Proof.AesOcb.Arm (BlkFn BlkCall BlkPost blkFrame blk_call encF)
open VG.Proof.AesGcm.Arm (below)
open VG.Proof.MdStream.Arm (Upd op2_imm op2_reg wp_mov)
open VG.Proof.AesCbc
open VG.Proof.AesCbc.Arm
open VG.Spec.Aes (bytesAt)

/-- The arguments of a call on the block at `iv`, with the working space at
the start of the scratch buffer. -/
theorem blkCallIv {s₀ : State} (hp : UPre s₀) {s : State}
    (r0 : s.gpr .r0 = W s₀) (r1 : s.gpr .r1 = s₀.gpr .r1) (r2 : s.gpr .r2 = Iv s₀) (r3 : s.gpr .r3 = 1)
    (r12 : s.gpr .r12 = S s₀) (sp : s.sp = s₀.sp) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    BlkCall s (W s₀) (Iv s₀) (S s₀) (R s₀) 1 := by
  have hb : below s.sp = belowR s₀ := by rw [sp]; rfl
  have hsc := hp.scr_fit
  refine ⟨r0, by rw [r1]; simp [R], r2, by rw [r3]; rfl, r12, hp.rounds, by rw [sp]; exact hp.sp8, hp.sch_fit,
    by have := hp.iv_fit; omega, by omega, hp.sch_iv, hp.sch_scr.sub_right (Region.sub_prefix (by decide)),
    hp.iv_scr.sub_right (Region.sub_prefix (by decide)), by rw [hb]; exact hp.b_sch, by rw [hb]; exact hp.b_iv,
    by rw [hb]; exact hp.b_scr.sub_right (Region.sub_prefix (by decide)), ?_, ?_⟩
  · rw [hrd, hwr, hp.rd, hp.wr]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨schR s₀, by simp, 0, by simp, by simp⟩
  · rw [hwr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨ivR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩

/-- What the code before the call leaves. -/
structure IvA (s₀ : State) (s s₁ : State) : Prop where
  pre : BlkCall s₁ (W s₀) (Iv s₀) (S s₀) (R s₀) 1
  keep : ∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → r ≠ .lr → s₁.gpr r = s.gpr r
  sp : s₁.sp = s.sp
  mem : s₁.mem = s.mem
  rd : s₁.rd = s.rd
  wr : s₁.wr = s.wr

theorem ivArgs_eq : ivArgs = [.mov .r0 (.reg .r4), .mov .r1 (.reg .r5), .mov .r2 (.reg .r6),
    .mov .r3 (.imm 1), .mov .r12 (.reg .r10)] := rfl

theorem ivA_wp {s₀ : State} (hp : UPre s₀) {k : Nat} {s : State} (h : LInv ofbMode s₀ k s) :
    WP isa (.block ivArgs) s (IvA s₀ s) := by
  rw [ivArgs_eq]
  refine wp_mov (op2_reg _ _) fun s₁ u₁ => wp_mov (op2_reg _ _) fun s₂ u₂ => wp_mov (op2_reg _ _) fun s₃ u₃ =>
    wp_mov (op2_imm (by decide)) fun s₄ u₄ => wp_mov (op2_reg _ _) fun s₅ u₅ => WP.block_nil ?_
  have keep : ∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → r ≠ .lr → s₅.gpr r = s.gpr r :=
    fun r h0 h1 h2 h3 h12 _ => by
      rw [u₅.other _ h12, u₄.other _ h3, u₃.other _ h2, u₂.other _ h1, u₁.other _ h0]
  have sp₅ : s₅.sp = s.sp := by rw [u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]
  have rd₅ : s₅.rd = s.rd := by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have wr₅ : s₅.wr = s.wr := by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  refine ⟨blkCallIv hp ?_ ?_ ?_ ?_ ?_ (by rw [sp₅, h.sp]) (by rw [rd₅, h.rd]) (by rw [wr₅, h.wr]), keep, sp₅,
    by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem], rd₅, wr₅⟩
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr,
      h.r4]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide),
      h.r5]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide),
      h.r6]
  · rw [u₅.other _ (by decide), u₄.gpr]
  · rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide),
      h.r10]

/-- A register the call and the code before it keep. -/
theorem keptIv {s₀ : State} {s s₁ s₂ : State} (a : IvA s₀ s s₁)
    (c : BlkPost encF s₁ (W s₀) (Iv s₀) (S s₀) (R s₀) 1 s₂) {r : Reg} (hr : r ∈ preserved) (hlr : r ≠ .lr) :
    s₂.gpr r = s.gpr r := by
  rw [c.saved r hr hlr]
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact absurd rfl hlr
    | exact a.keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem post_eq : post = xor4 .r7 .r6 .r7 0 0 0 ++ advance := rfl

theorem body_ok : BodyOk ofbMode body := by
  intro s₀ hp k hk s h
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
  -- Memory so far.
  have f₂ : Frame [ivR s₀, ⟨State.addr (S s₀), 2048⟩, belowR s₀] s.mem s₂.mem := by
    have fr := c.frame; rw [hb, a.mem] at fr; exact fr
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
  have fStep : Frame [⟨blk s₀ k, 16⟩, ivR s₀, ⟨State.addr (S s₀), 2064⟩, belowR s₀] s.mem s₃.mem :=
    (f₂.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact stepIn (.inr (.inl rfl))
      · exact stepIn (.inr (.inr (.inl (Region.sub_prefix (by decide)))))
      · exact stepIn (.inr (.inr (.inr rfl)))).trans
      (f₃.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact stepIn (.inl rfl))
  have big : Frame (Big s₀) s₀.mem s.mem := UPre.big_of h.frame
  have hblk := h.block hk
  have newIv : bytesAt s₃.mem (State.addr (Iv s₀)) 16 =
      Spec.Cbc.aesWith (R s₀) (wK s₀) (chainK ofbMode s₀ k) := by
    rw [m₃, Proof.Cmac.bytesAt_frame (Proof.Cmac.xor4Mem_frame _ _ _ _) (one (hp.blk_iv hk).symm) (by decide),
      bytesAt_of_statesAt c.out, show encF.f = Spec.Aes.cipher from rfl, a.mem, UPre.sched_bytes hp big,
      ← aesWith_state, h.iv]
  have newBlk : bytesAt s₃.mem (blk s₀ k) 16 =
      Spec.Cbc.xor ((blks s₀)[k]'(by simp [Spec.Cbc.blocksAt]; exact hk))
        (bytesAt s₃.mem (State.addr (Iv s₀)) 16) := by
    rw [m₃, xorIn4_bytes _ (hp.blk_iv hk), ← hblk,
      Proof.Cmac.bytesAt_frame f₂ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact hp.blk_iv hk
        · exact (hp.data_scr.sub_left (UPre.data_sub hk)).sub_right (Region.sub_prefix (by decide))
        · exact hp.b_data.symm.sub_left (UPre.data_sub hk)) (by decide),
      Proof.Cmac.bytesAt_frame (Proof.Cmac.xor4Mem_frame _ _ _ _) (one (hp.blk_iv hk).symm) (by decide)]
  have hl : ((blks s₀).take k).length = k := by simp [Spec.Cbc.blocksAt]; omega
  have outSucc : outK ofbMode s₀ (k + 1) = outK ofbMode s₀ k ++ [bytesAt s₃.mem (blk s₀ k) 16] := by
    rw [newBlk, newIv]
    simp only [outK, chainK, ofbMode_out, ofbMode_chain, take_succ_blks s₀ hk, crypt_snoc, hl]
  have hl' : (outK ofbMode s₀ k).length = k := by rw [outK, Mode.length_out, hl]
  refine advance_wp hp hk (rg₂.of g₃.gpr g₃.sp g₃.rd g₃.wr)
    (by rw [g₃.gpr _ (by decide) (by decide), keptIv a c (by simp [preserved]) (by decide), h.r8])
    (by rw [g₃.gpr _ (by decide) (by decide), keptIv a c (by simp [preserved]) (by decide), h.r11])
    (h.frame.trans (stepFrame hk fStep)) ?_ ?_
  · rw [hp.blocksAt_step hk fStep, h.data, outSucc,
      set_prefix _ _ _ hl' (by simp [Spec.Cbc.blocksAt]; exact hk)]
  · rw [newIv]
    simp only [chainK, ofbMode_chain, take_succ_blks s₀ hk, List.length_append, List.length_singleton, hl,
      next_succ]

/-! ## Constant time -/

theorem pre_taint : ∃ h, (taint.check (Taint.ofRegs vars) (.block ivArgs) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem post_taint : ∃ h, (taint.check (Taint.ofRegs postVars) (.block post) h).isSome = true :=
  ⟨_, by taint_decide⟩

/-- What the code before the call leaves, as `Mid`. -/
theorem mid_of {s₀ : State} {k : Nat} {s s₁ : State} (h : LInv ofbMode s₀ k s) (a : IvA s₀ s s₁) :
    Mid s₀ k (Iv s₀) s₁ :=
  ⟨a.pre, ⟨by rw [a.keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.r6],
    by rw [a.keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.r7],
    by rw [a.keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.r8],
    by rw [a.keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.r10],
    by rw [a.sp, h.sp]⟩⟩

theorem body_ct : BodyCt ofbMode body := fun hp hp' hq k => by
  rw [body, encFrame_eq]
  exact VG.Proof.AesCbc.Arm.body_ct encF (D := fun s₀ _ => Iv s₀) (fun hq _ => pub_Iv hq) pre_taint post_taint
    (@fun _ hp _ _ _ h => WP.mono (ivA_wp hp h) fun _ a => mid_of h a) hp hp' hq k

end VG.Proof.AesOfb.Arm
