import VerifiedGarbage.Proof.AesCtr.Arm.Steps
import VerifiedGarbage.Proof.AesCbc.Arm.CT

/-!
# AES-CTR on ARMv7: one block, and constant time

`body_ok`: one run of `body` takes the loop invariant AES-CBC's proofs share
(`Proof/AesCbc/Arm/Loop.lean`) from `k` blocks to `k + 1`, for `ctrMode`.
The counter block is copied to the scratch buffer and enciphered there
(`pre_wp`), as AES-CBC calls the block function, the output block is XORed
into the data block, and the counter block is incremented (`Steps.lean`).
`body_ct`: it is constant time, by the shared framework, with the call on
the copy.
-/

namespace VG.Proof.AesCtr.Arm

open VG VG.Arm VG.Impl.AesCtr.Arm
open VG.Impl.AesCbc.Arm (cOff encFrame zero4)
open VG.Impl.CmacAes.Arm (xor4 mov advance)
open VG.Proof.CmacAes.Arm (W R Dp N S schR dataR scrR argsR belowR savedMem add0)
open VG.Proof.AesOcb.Arm (BlkCall BlkPost blk_call encF)
open VG.Proof.AesGcm.Arm (below)
open VG.Proof.MdStream.Arm (Upd op2_imm op2_reg wp_mov wp_add)
open VG.Proof.AesCbc (copy4Mem copy4Mem_frame copy4Mem_bytes xorIn4_bytes aesWith_state set_prefix
  bytesAt_of_statesAt Mode)
open VG.Proof.AesCbc.Arm
open VG.Spec.Aes (bytesAt)

/-- The copy of the counter block, as a 32-bit address. -/
abbrev Sv32 (s₀ : State) : BitVec 32 := S s₀ + BitVec.ofNat 32 2048

section
variable {s₀ : State} (hp : UPre s₀)
include hp

theorem UPre.sv : State.addr (Sv32 s₀) = Sv s₀ := hp.scrA (by decide)

/-- The arguments of a call on the copy of the counter block, with the
working space at the start of the scratch buffer. -/
theorem UPre.blkCallSv {s : State}
    (r0 : s.gpr .r0 = W s₀) (r1 : s.gpr .r1 = s₀.gpr .r1) (r2 : s.gpr .r2 = Sv32 s₀) (r3 : s.gpr .r3 = 1)
    (r12 : s.gpr .r12 = S s₀) (sp : s.sp = s₀.sp) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    BlkCall s (W s₀) (Sv32 s₀) (S s₀) (R s₀) 1 := by
  have hb : below s.sp = belowR s₀ := by rw [sp]; rfl
  have hd := UPre.sv hp
  have hsc := hp.scr_fit
  have qN : (Sv32 s₀).toNat = (S s₀).toNat + 2048 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 2048) (by decide),
      Nat.mod_eq_of_lt (by omega)]
  refine ⟨r0, by rw [r1]; simp [R], r2, by rw [r3]; rfl, r12, hp.rounds, by rw [sp]; exact hp.sp8, hp.sch_fit,
    by rw [qN]; omega, by omega, ?_, hp.sch_scr.sub_right (Region.sub_prefix (by decide)), ?_,
    by rw [hb]; exact hp.b_sch, ?_, by rw [hb]; exact hp.b_scr.sub_right (Region.sub_prefix (by decide)), ?_, ?_⟩
  · rw [hd]; exact hp.sch_scr.sub_right (UPre.scr_sub (by decide))
  · rw [hd]; exact hp.sv_scr
  · rw [hb, hd]; exact hp.b_scr.sub_right (UPre.scr_sub (by decide))
  · rw [hrd, hwr, hp.rd, hp.wr]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨schR s₀, by simp, 0, by simp, by simp⟩
  · rw [hwr, hp.wr, hd]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨scrR s₀, by simp, 2048, rfl, by simp⟩
    · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩

end

/-! ## The code before the call -/

/-- What the code before the call leaves. -/
structure PreA (s₀ : State) (s s₁ : State) : Prop where
  pre : BlkCall s₁ (W s₀) (Sv32 s₀) (S s₀) (R s₀) 1
  keep : ∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → r ≠ .lr → s₁.gpr r = s.gpr r
  sp : s₁.sp = s.sp
  mem : s₁.mem = copy4Mem s.mem (Sv s₀) (State.addr (Iv s₀))
  rd : s₁.rd = s.rd
  wr : s₁.wr = s.wr

theorem pre_eq : pre = zero4 .r10 2048 ++ (xor4 .r10 .r6 .r10 2048 0 2048 ++
    ([.mov .r0 (.reg .r4), .mov .r1 (.reg .r5), .dp .add .r2 .r10 (.imm 2048), .mov .r3 (.imm 1),
      .mov .r12 (.reg .r10)] : List Instr)) := rfl

theorem pre_wp {s₀ : State} (hp : UPre s₀) {k : Nat} {s : State} (h : LInv AesCtr.ctrMode s₀ k s) :
    WP isa (.block pre) s (PreA s₀ s) := by
  have hsc := hp.scr_fit
  have hiv := hp.iv_fit
  have rw₀ : s.rd ++ s.wr = [schR s₀, argsR s₀, ivR s₀, dataR s₀, scrR s₀] := by
    rw [h.rd, h.wr, hp.rd, hp.wr]; rfl
  have w₀ : s.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [h.wr, hp.wr]
  rw [pre_eq]
  refine copy_wp (by decide) (by decide) (by decide) (by decide) (by rw [h.r6]; omega)
    (by rw [h.r10]; omega) (by rw [h.r6, add0, rw₀]; exact covIv (by simp))
    (by rw [h.r10, w₀]; exact covSv (by simp)) fun s₁ g₁ => ?_
  have m₁ : s₁.mem = copy4Mem s.mem (Sv s₀) (State.addr (Iv s₀)) := by rw [g₁.mem, h.r10, h.r6, add0]
  refine wp_mov (op2_reg _ _) fun s₂ u₂ => wp_mov (op2_reg _ _) fun s₃ u₃ =>
    wp_add (op2_imm (by decide)) fun s₄ u₄ => wp_mov (op2_imm (by decide)) fun s₅ u₅ =>
    wp_mov (op2_reg _ _) fun s₆ u₆ => WP.block_nil ?_
  have keep : ∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → r ≠ .lr → s₆.gpr r = s.gpr r :=
    fun r h0 h1 h2 h3 h12 hlr => by
      rw [u₆.other _ h12, u₅.other _ h3, u₄.other _ h2, u₃.other _ h1, u₂.other _ h0, g₁.gpr _ h12 hlr]
  have sp₆ : s₆.sp = s.sp := by rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, g₁.sp]
  have rd₆ : s₆.rd = s.rd := by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, g₁.rd]
  have wr₆ : s₆.wr = s.wr := by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, g₁.wr]
  have g10 : s₁.gpr .r10 = S s₀ := by rw [g₁.gpr _ (by decide) (by decide), h.r10]
  refine ⟨UPre.blkCallSv hp ?_ ?_ ?_ ?_ ?_ (by rw [sp₆, h.sp]) (by rw [rd₆, h.rd]) (by rw [wr₆, h.wr]), keep,
    sp₆, by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, m₁], rd₆, wr₆⟩
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr,
      g₁.gpr _ (by decide) (by decide), h.r4]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
      u₂.other _ (by decide), g₁.gpr _ (by decide) (by decide), h.r5]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide),
      g10]; rfl
  · rw [u₆.other _ (by decide), u₅.gpr]
  · rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), g10]

/-! ## One block -/

/-- What the call leaves, about the registers. -/
theorem post_regs {s₀ : State} {k : Nat} {s s₁ s₂ : State} (h : Regs s₀ k s) (a : PreA s₀ s s₁)
    (c : BlkPost encF s₁ (W s₀) (Sv32 s₀) (S s₀) (R s₀) 1 s₂) :
    Regs s₀ k s₂ ∧ s₂.gpr .r8 = s.gpr .r8 ∧ s₂.gpr .r11 = s.gpr .r11 := by
  have g : ∀ r ∈ preserved, r ≠ .lr → s₂.gpr r = s.gpr r := fun r hr hlr => by
    rw [c.saved r hr hlr]
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact absurd rfl hlr
      | exact a.keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  exact ⟨⟨by rw [g .r4 (by simp [preserved]) (by decide), h.r4], by rw [g .r5 (by simp [preserved]) (by decide), h.r5],
    by rw [g .r6 (by simp [preserved]) (by decide), h.r6], by rw [g .r7 (by simp [preserved]) (by decide), h.r7],
    by rw [g .r10 (by simp [preserved]) (by decide), h.r10], by rw [c.sp, a.sp, h.sp], by rw [c.rd, a.rd, h.rd],
    by rw [c.wr, a.wr, h.wr]⟩, g .r8 (by simp [preserved]) (by decide), g .r11 (by simp [preserved]) (by decide)⟩

theorem post_eq : post = xor4 .r7 .r10 .r7 0 cOff 0 ++ (incr ++ advance) := by
  simp only [post, List.append_assoc]

theorem body_ok : BodyOk AesCtr.ctrMode body := by
  intro s₀ hp k hk s h
  have hd := hp.dataA hk
  have qN := hp.dataN hk
  have hdf := hp.data_fit
  have hiv := hp.iv_fit
  have hsc := hp.scr_fit
  refine WP.seq (WP.mono (pre_wp hp h) fun s₁ a => ?_)
  rw [encFrame_eq]
  refine WP.seq (WP.mono (blk_call encF a.pre) fun s₂ c => ?_)
  obtain ⟨rg₂, r8₂, r11₂⟩ := post_regs h.regs a c
  have hb : below s₁.sp = belowR s₀ := by rw [a.sp, h.sp]; rfl
  have svSub : Region.Sub ⟨Sv s₀, 16⟩ ⟨State.addr (S s₀), 2064⟩ := Offset.sub_base _ (by decide)
  -- Memory so far.
  have f₁ : Frame [⟨Sv s₀, 16⟩] s.mem s₁.mem := by rw [a.mem]; exact copy4Mem_frame _ _ _
  have f₂ : Frame [⟨Sv s₀, 16⟩, ⟨State.addr (S s₀), 2048⟩, belowR s₀] s₁.mem s₂.mem := by
    have fr := c.frame; rw [hb, UPre.sv hp] at fr; exact fr
  have fs₂ : Frame [⟨blk s₀ k, 16⟩, ivR s₀, ⟨State.addr (S s₀), 2064⟩, belowR s₀] s.mem s₂.mem :=
    (f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact stepIn (.inr (.inr (.inl svSub)))).trans
      (f₂.sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact stepIn (.inr (.inr (.inl svSub)))
        · exact stepIn (.inr (.inr (.inl (Region.sub_prefix (by decide)))))
        · exact stepIn (.inr (.inr (.inr rfl))))
  have big₁ : Frame (Big s₀) s₀.mem s₁.mem := bigOf hp hk h.frame (f₁.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact stepIn (.inr (.inr (.inl svSub))))
  have w₂ : s₂.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [rg₂.wr, hp.wr]
  have rw₂ : s₂.rd ++ s₂.wr = [schR s₀, argsR s₀, ivR s₀, dataR s₀, scrR s₀] := by
    rw [rg₂.rd, rg₂.wr, hp.rd, hp.wr]; rfl
  rw [post_eq]
  refine xorIn_wp (by decide) (by decide) (by decide) (by decide) (by rw [rg₂.r10]; unfold cOff; omega)
    (by rw [rg₂.r7, qN]; omega) (by rw [rg₂.r10, rw₂]; exact covSv (by simp))
    (by rw [rg₂.r7, add0, hd, w₂]; exact covBlk hk (by simp)) fun s₃ g₃ => ?_
  have m₃ : s₃.mem = Proof.Cmac.xor4Mem s₂.mem (blk s₀ k) (blk s₀ k) (Sv s₀) := by
    rw [g₃.mem, rg₂.r7, rg₂.r10, add0, hd]; rfl
  have f₃ : Frame [⟨blk s₀ k, 16⟩] s₂.mem s₃.mem := by rw [m₃]; exact Proof.Cmac.xor4Mem_frame _ _ _ _
  have rg₃ := rg₂.of g₃.gpr g₃.sp g₃.rd g₃.wr
  have w₃ : s₃.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [rg₃.wr, hp.wr]
  have rw₃ : s₃.rd ++ s₃.wr = [schR s₀, argsR s₀, ivR s₀, dataR s₀, scrR s₀] := by
    rw [rg₃.rd, rg₃.wr, hp.rd, hp.wr]; rfl
  obtain ⟨s₄, run₄, g₄, sp₄, mem₄, rd₄, wr₄⟩ := incr_ok s₃ (Q := State.addr (Iv s₀)) (by rw [rg₃.r6])
    (by rw [rg₃.r6]; omega)
    (fun d n hdn => by rw [rw₃]; exact ⟨ivR s₀, by simp, Offset.contains_base _ hdn (by omega)⟩)
    (fun d n hdn => by rw [w₃]; exact ⟨ivR s₀, by simp, Offset.contains_base _ hdn (by omega)⟩)
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨s₄, run₄, ?_⟩
  have f₄ : Frame [ivR s₀] s₃.mem s₄.mem := by rw [mem₄]; exact incMem_frame _ _
  have fStep : Frame [⟨blk s₀ k, 16⟩, ivR s₀, ⟨State.addr (S s₀), 2064⟩, belowR s₀] s.mem s₄.mem :=
    (fs₂.trans (f₃.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact stepIn (.inl rfl))).trans
      (f₄.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact stepIn (.inr (.inl rfl)))
  have callIv : ∀ r ∈ [⟨Sv s₀, 16⟩, ⟨State.addr (S s₀), 2048⟩, belowR s₀], (ivR s₀).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.iv_sv
    · exact hp.iv_scr.sub_right (Region.sub_prefix (by decide))
    · exact hp.b_iv.symm
  have callBlk : ∀ r ∈ [⟨Sv s₀, 16⟩, ⟨State.addr (S s₀), 2048⟩, belowR s₀],
      (⟨blk s₀ k, 16⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.blk_sv hk
    · exact (hp.data_scr.sub_left (UPre.data_sub hk)).sub_right (Region.sub_prefix (by decide))
    · exact (hp.b_data.sub_right (UPre.data_sub hk)).symm
  have ivIn : bytesAt s₃.mem (State.addr (Iv s₀)) 16 = chainK AesCtr.ctrMode s₀ k := by
    rw [m₃, Proof.Cmac.bytesAt_frame (Proof.Cmac.xor4Mem_frame _ _ _ _) (one (hp.blk_iv hk).symm) (by decide),
      Proof.Cmac.bytesAt_frame f₂ callIv (by decide), a.mem,
      Proof.Cmac.bytesAt_frame (copy4Mem_frame _ _ _) (one hp.iv_sv) (by decide), h.iv]
  have blkIn : bytesAt s₂.mem (blk s₀ k) 16 = (blks s₀)[k]'(by simp [Spec.Cbc.blocksAt]; exact hk) := by
    rw [Proof.Cmac.bytesAt_frame f₂ callBlk (by decide), a.mem,
      Proof.Cmac.bytesAt_frame (copy4Mem_frame _ _ _) (one (hp.blk_sv hk)) (by decide), h.block hk]
  have outBlk : bytesAt s₂.mem (Sv s₀) 16 = Spec.Cbc.aesWith (R s₀) (wK s₀) (chainK AesCtr.ctrMode s₀ k) := by
    have o := bytesAt_of_statesAt c.out
    rw [UPre.sv hp] at o
    rw [o, show encF.f = Spec.Aes.cipher from rfl, UPre.sched_bytes hp big₁, ← aesWith_state, a.mem,
      copy4Mem_bytes _ hp.iv_sv.symm, h.iv]
  have newBlk : bytesAt s₄.mem (blk s₀ k) 16 =
      Spec.Cbc.xor ((blks s₀)[k]'(by simp [Spec.Cbc.blocksAt]; exact hk))
        (Spec.Cbc.aesWith (R s₀) (wK s₀) (chainK AesCtr.ctrMode s₀ k)) := by
    rw [Proof.Cmac.bytesAt_frame f₄ (one (hp.blk_iv hk)) (by decide), m₃, xorIn4_bytes _ (hp.blk_sv hk), blkIn,
      outBlk]
  have newIv : bytesAt s₄.mem (State.addr (Iv s₀)) 16 = Spec.Ctr.inc (chainK AesCtr.ctrMode s₀ k) := by
    rw [mem₄, incMem_bytes, ivIn]
  have hl : (outK AesCtr.ctrMode s₀ k).length = k := by
    rw [outK, Mode.length_out]; simp [Spec.Cbc.blocksAt]; omega
  have hlt : ((blks s₀).take k).length = k := by simp [Spec.Cbc.blocksAt]; omega
  have outSucc :
      outK AesCtr.ctrMode s₀ (k + 1) = outK AesCtr.ctrMode s₀ k ++ [bytesAt s₄.mem (blk s₀ k) 16] := by
    rw [newBlk]
    simp only [outK, chainK, AesCtr.ctrMode_out, AesCtr.ctrMode_chain, take_succ_blks s₀ hk, AesCtr.crypt_snoc]
  have k₄ (r : Reg) (h₁ : r ≠ .r0 ∧ r ≠ .r1 ∧ r ≠ .r2 ∧ r ≠ .r3 ∧ r ≠ .r12) : s₄.gpr r = s₃.gpr r :=
    g₄ r h₁.1 h₁.2.1 h₁.2.2.1 h₁.2.2.2.1 h₁.2.2.2.2
  have rg₄ : Regs s₀ k s₄ := ⟨by rw [k₄ _ (by decide), rg₃.r4], by rw [k₄ _ (by decide), rg₃.r5],
    by rw [k₄ _ (by decide), rg₃.r6], by rw [k₄ _ (by decide), rg₃.r7], by rw [k₄ _ (by decide), rg₃.r10],
    by rw [sp₄, rg₃.sp], by rw [rd₄, rg₃.rd], by rw [wr₄, rg₃.wr]⟩
  refine advance_wp hp hk rg₄
    (by rw [g₄ _ (by decide) (by decide) (by decide) (by decide) (by decide), g₃.gpr _ (by decide) (by decide),
      r8₂, h.r8])
    (by rw [g₄ _ (by decide) (by decide) (by decide) (by decide) (by decide), g₃.gpr _ (by decide) (by decide),
      r11₂, h.r11])
    (h.frame.trans (stepFrame hk fStep)) ?_ ?_
  · rw [hp.blocksAt_step hk fStep, h.data, outSucc,
      set_prefix _ _ _ hl (by simp [Spec.Cbc.blocksAt]; exact hk)]
  · rw [newIv]
    simp only [chainK, AesCtr.ctrMode_chain, take_succ_blks s₀ hk, List.length_append, List.length_singleton,
      hlt, AesCtr.next_succ]

/-! ## Constant time -/

theorem pre_taint : ∃ h, (taint.check (Taint.ofRegs vars) (.block pre) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem post_taint : ∃ h, (taint.check (Taint.ofRegs postVars) (.block post) h).isSome = true :=
  ⟨_, by taint_decide⟩

/-- What the code before the call leaves, as `Mid`. -/
theorem mid_of {s₀ : State} {k : Nat} {s s₁ : State} (h : LInv AesCtr.ctrMode s₀ k s) (a : PreA s₀ s s₁) :
    Mid s₀ k (Sv32 s₀) s₁ :=
  ⟨a.pre, ⟨by rw [a.keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.r6],
    by rw [a.keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.r7],
    by rw [a.keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.r8],
    by rw [a.keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.r10],
    by rw [a.sp, h.sp]⟩⟩

theorem body_ct : BodyCt AesCtr.ctrMode body := fun hp hp' hq k => by
  rw [body, encFrame_eq]
  exact VG.Proof.AesCbc.Arm.body_ct encF (D := fun s₀ _ => Sv32 s₀) (fun hq _ => by rw [Sv32, Sv32, pub_S hq])
    pre_taint post_taint (@fun _ hp _ _ _ h => WP.mono (pre_wp hp h) fun _ a => mid_of h a) hp hp' hq k

end VG.Proof.AesCtr.Arm
