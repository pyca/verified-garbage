import VerifiedGarbage.Proof.AesCtr.AArch64.Steps
import VerifiedGarbage.Proof.AesCbc.AArch64.CT

/-!
# AES-CTR on AArch64: one block, and constant time

`body_ok`: one run of `body` takes the loop invariant AES-CBC's proofs share
(`Proof/AesCbc/AArch64/Loop.lean`) from `k` blocks to `k + 1`, for
`ctrMode`, for any implementation of the block functions (`BlocksImpl`).
The counter block is copied to the scratch buffer and enciphered there
(`preA_wp`), the output block is XORed into the data block, and the counter
block is incremented (`Steps.lean`). `body_ct`: it is constant time, by the
shared framework, with the call on the copy.
-/

namespace VG.Proof.AesCtr.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesCtr.AArch64
open VG.Impl.AesCbc.AArch64 (cOff copy advance whole)
open VG.Proof.AesCbc (copyMem copyMem_frame copyMem_bytes xorMem xorMem_frame xorMem_bytes aesWith_state
  set_prefix Mode)
open VG.Proof.AesCbc.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.AArch64 (BlocksImpl)

section
variable {s₀ : State} (hp : UPre s₀)
include hp

theorem UPre.sv_wrap' : (Sv s₀).toNat + 16 ≤ 2 ^ 64 := by
  have := hp.scr_wrap
  rw [Sv, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 2048) (by decide),
    Nat.mod_eq_of_lt (by omega)]
  omega

/-- The arguments of a call on the copy of the counter block, with the
working space at the start of the scratch buffer. -/
theorem UPre.callPreSv {s : State}
    (x0 : s.gpr .x0 = W s₀) (x1 : s.gpr .x1 = s₀.gpr .x1) (x2 : s.gpr .x2 = Sv s₀)
    (x3 : s.gpr .x3 = 1) (x4 : s.gpr .x4 = S s₀) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    CallPre s (W s₀) (Sv s₀) (S s₀) (R s₀) where
  x0 := x0
  x1 := by rw [x1, x1_ofNat]
  x2 := x2
  x3 := x3
  x4 := x4
  rounds := hp.rounds
  wd := hp.sch_scr.sub_right (UPre.scr_sub (by decide))
  ws := hp.sch_scr.sub_right (Region.sub_prefix (by decide))
  ds := hp.sv_scr
  wrap := UPre.sv_wrap' hp
  reads := by
    rw [hrd, hwr, hp.rd, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨schR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨scrR s₀, by simp, 2048, rfl, by simp⟩
    · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩
  writes := by
    rw [hwr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨scrR s₀, by simp, 2048, rfl, by simp⟩
    · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩

end

/-- What the code before the call leaves. -/
structure PreA (s₀ : State) (s s₁ : State) : Prop where
  pre : CallPre s₁ (W s₀) (Sv s₀) (S s₀) (R s₀)
  saved : ∀ r ∈ preserved, s₁.gpr r = s.gpr r
  sp : s₁.sp = s.sp
  mem : s₁.mem = copyMem s.mem (Sv s₀) (Iv s₀)
  rd : s₁.rd = s.rd
  wr : s₁.wr = s.wr

theorem preA_wp {s₀ : State} (hp : UPre s₀) {k : Nat} {s : State} (h : LInv AesCtr.ctrMode s₀ k s) :
    WP isa (.block pre) s (PreA s₀ s) := by
  have hR := h.regs hp
  have hW := h.wrs hp
  obtain ⟨s₁, run₁, g₁, sp₁, mem₁, rd₁, wr₁⟩ :=
    copy_ok s (dst := .x24) (src := .x21) (d := cOff) (e := 0) (P := Sv s₀) (Q := Iv s₀)
      (by rw [h.x24]; rfl) (by rw [h.x24]; exact sv8 _)
      (by rw [h.x21]; simp) (by rw [h.x21])
      (by rw [hR]; exact in_rw (by simp) cIv0) (by rw [hR]; exact in_rw (by simp) cIv8)
      (by rw [hW]; exact in_rw (by simp) cSv0) (by rw [hW]; exact in_rw (by simp) cSv8)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨s₂, run₂, x0₂, x1₂, x2₂, x3₂, x4₂, cs₂, sp₂, mem₂, rd₂, wr₂⟩ := args_ok s₁
  rw [pre_eq, WP.block_append_iff]
  refine WP.of_runBlock ⟨s₁, run₁, WP.of_runBlock ⟨s₂, run₂, ?_⟩⟩
  have keep (r : Reg) (hr : r ∈ preserved) : s₂.gpr r = s.gpr r := by
    rw [cs₂ r hr, g₁ r (preserved_ne hr).1]
  exact ⟨UPre.callPreSv hp (by rw [x0₂, g₁ _ (by decide), h.x19]) (by rw [x1₂, g₁ _ (by decide), h.x20])
    (by rw [x2₂, g₁ _ (by decide), h.x24]) x3₂ (by rw [x4₂, g₁ _ (by decide), h.x24])
    (by rw [rd₂, rd₁, h.rd]) (by rw [wr₂, wr₁, h.wr]), keep, by rw [sp₂, sp₁], by rw [mem₂, mem₁],
    by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩

theorem preserved_ne' {r : Reg} (hr : r ∈ preserved) : r ≠ .x11 ∧ r ≠ .x12 := by
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem body_ok (v : BlocksImpl) : BodyOk AesCtr.ctrMode (body v.enc) := by
  intro s₀ hp k hk s h
  refine WP.seq (WP.mono (preA_wp hp h) fun s₁ a => ?_)
  refine WP.seq (WP.mono (blk_call v.encOk v.encNoFrames a.pre) fun s₂ c => ?_)
  have g₂ (r : Reg) (hr : r ∈ preserved) (h30 : r ≠ .x30) : s₂.gpr r = s.gpr r := by
    rw [c.saved r hr h30, a.saved r hr]
  have hW₂ : s₂.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [c.wr, a.wr, h.wrs hp]
  have hR₂ : s₂.rd ++ s₂.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by
    rw [c.rd, c.wr, a.rd, a.wr, h.regs hp]
  obtain ⟨s₃, run₃, g₃, sp₃, mem₃, rd₃, wr₃⟩ :=
    xorOut_ok s₂ (P := blk s₀ k) (Q := Sv s₀) (by rw [g₂ .x22 (by simp [preserved]) (by decide), h.x22])
      (by rw [g₂ .x24 (by simp [preserved]) (by decide), h.x24])
      (by rw [g₂ .x24 (by simp [preserved]) (by decide), h.x24]; exact sv8 _)
      (by rw [hR₂]; exact in_rw (by simp) (hp.cBlk0 hk)) (by rw [hR₂]; exact in_rw (by simp) (hp.cBlk8 hk))
      (by rw [hR₂]; exact in_rw (by simp) cSv0) (by rw [hR₂]; exact in_rw (by simp) cSv8)
      (by rw [hW₂]; exact in_rw (by simp) (hp.cBlk0 hk)) (by rw [hW₂]; exact in_rw (by simp) (hp.cBlk8 hk))
  have g₃' (r : Reg) (hr : r ∈ preserved) (h30 : r ≠ .x30) : s₃.gpr r = s.gpr r := by
    rw [g₃ r (preserved_ne hr).1 (preserved_ne hr).2, g₂ r hr h30]
  have hR₃ : s₃.rd ++ s₃.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by rw [rd₃, wr₃, hR₂]
  have hW₃ : s₃.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [wr₃, hW₂]
  obtain ⟨s₄, run₄, g₄, sp₄, mem₄, rd₄, wr₄⟩ :=
    incr_ok s₃ (Q := Iv s₀) (by rw [g₃' .x21 (by simp [preserved]) (by decide), h.x21])
      (by rw [hR₃]; exact in_rw (by simp) cIv0) (by rw [hR₃]; exact in_rw (by simp) cIv8)
      (by rw [hW₃]; exact in_rw (by simp) cIv0) (by rw [hW₃]; exact in_rw (by simp) cIv8)
  obtain ⟨s₅, run₅, x22₅, x23₅, keep₅, sp₅, mem₅, rd₅, wr₅⟩ := advance_regs (s := s₄) hk
    (by rw [g₄ _ (by decide) (by decide) (by decide) (by decide), g₃' .x22 (by simp [preserved]) (by decide), h.x22])
    (by rw [g₄ _ (by decide) (by decide) (by decide) (by decide), g₃' .x23 (by simp [preserved]) (by decide), h.x23])
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨s₄, run₄, WP.of_runBlock ⟨s₅, run₅, ?_⟩⟩
  have g (r : Reg) (hr : r ∈ preserved) (h30 : r ≠ .x30) (h22 : r ≠ .x22) (h23 : r ≠ .x23) :
      s₅.gpr r = s.gpr r := by
    rw [keep₅ r h22 h23, g₄ r (preserved_ne hr).1 (preserved_ne hr).2 (preserved_ne' hr).1 (preserved_ne' hr).2,
      g₃' r hr h30]
  -- Memory.
  have svSub : Region.Sub ⟨Sv s₀, 16⟩ ⟨S s₀, 2064⟩ := Offset.sub_base _ (by decide)
  have f₁ : Frame [⟨Sv s₀, 16⟩] s.mem s₁.mem := by rw [a.mem]; exact copyMem_frame _ _ _
  have f₃ : Frame [⟨blk s₀ k, 16⟩] s₂.mem s₃.mem := by rw [mem₃]; exact xorMem_frame _ _ _
  have f₄ : Frame [ivR s₀] s₃.mem s₄.mem := by rw [mem₄]; exact incMem_frame _ _
  have fStep : Frame [⟨blk s₀ k, 16⟩, ivR s₀, ⟨S s₀, 2064⟩] s.mem s₅.mem := by
    rw [mem₅]
    refine (f₁.sub fun r hr => ?_).trans ((c.frame.sub fun r hr => ?_).trans
      ((f₃.sub fun r hr => ?_).trans (f₄.sub fun r hr => ?_)))
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨⟨S s₀, 2064⟩, by simp, svSub⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨S s₀, 2064⟩, by simp, svSub⟩
      · exact ⟨⟨S s₀, 2064⟩, by simp, Region.sub_prefix (by decide)⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
  have big₁ : Frame (Big s₀) s₀.mem s₁.mem :=
    (UPre.big_of h.frame).trans (f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, by simp, UPre.scr_sub (by decide)⟩)
  have one (r : Region) (P : Addr) (hd : (⟨P, 16⟩ : Region).Disjoint r) :
      ∀ r' ∈ [r], (⟨P, 16⟩ : Region).Disjoint r' := fun r' hr' => by
    simp only [List.mem_singleton] at hr'; subst hr'; exact hd
  have callIv : ∀ r ∈ [⟨Sv s₀, 16⟩, ⟨S s₀, 2048⟩], (ivR s₀).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.iv_sv
    · exact hp.iv_scr.sub_right (Region.sub_prefix (by decide))
  have callBlk : ∀ r ∈ [⟨Sv s₀, 16⟩, ⟨S s₀, 2048⟩], (⟨blk s₀ k, 16⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.blk_sv hk
    · exact (hp.data_scr.sub_left (UPre.data_sub hk)).sub_right (Region.sub_prefix (by decide))
  have ivIn : bytesAt s₃.mem (Iv s₀) 16 = chainK AesCtr.ctrMode s₀ k := by
    rw [mem₃, Proof.Cmac.bytesAt_frame (xorMem_frame _ _ _) (one _ _ (hp.blk_iv hk).symm) (by decide),
      Proof.Cmac.bytesAt_frame c.frame callIv (by decide), a.mem,
      Proof.Cmac.bytesAt_frame (copyMem_frame _ _ _) (one _ _ hp.iv_sv) (by decide), h.iv]
  have blkIn : bytesAt s₂.mem (blk s₀ k) 16 = (blks s₀)[k]'(by simp [Spec.Cbc.blocksAt]; exact hk) := by
    rw [Proof.Cmac.bytesAt_frame c.frame callBlk (by decide), a.mem,
      Proof.Cmac.bytesAt_frame (copyMem_frame _ _ _) (one _ _ (hp.blk_sv hk)) (by decide), h.block hk]
  have outBlk : bytesAt s₂.mem (Sv s₀) 16 = Spec.Cbc.aesWith (R s₀) (wK s₀) (chainK AesCtr.ctrMode s₀ k) := by
    rw [c.out, UPre.sched_bytes hp big₁, ← aesWith_state, a.mem, copyMem_bytes _ hp.iv_sv.symm, h.iv]
  have newBlk : bytesAt s₅.mem (blk s₀ k) 16 =
      Spec.Cbc.xor ((blks s₀)[k]'(by simp [Spec.Cbc.blocksAt]; exact hk))
        (Spec.Cbc.aesWith (R s₀) (wK s₀) (chainK AesCtr.ctrMode s₀ k)) := by
    rw [mem₅, mem₄, Proof.Cmac.bytesAt_frame (incMem_frame _ _) (one _ _ (hp.blk_iv hk)) (by decide), mem₃,
      xorMem_bytes _ (hp.blk_sv hk), blkIn, outBlk]
  have newIv : bytesAt s₅.mem (Iv s₀) 16 = Spec.Ctr.inc (chainK AesCtr.ctrMode s₀ k) := by
    rw [mem₅, mem₄, incMem_bytes, ivIn]
  have hl : (outK AesCtr.ctrMode s₀ k).length = k := by
    rw [outK, Mode.length_out]; simp [Spec.Cbc.blocksAt]; omega
  have hlt : ((blks s₀).take k).length = k := by simp [Spec.Cbc.blocksAt]; omega
  have outSucc :
      outK AesCtr.ctrMode s₀ (k + 1) = outK AesCtr.ctrMode s₀ k ++ [bytesAt s₅.mem (blk s₀ k) 16] := by
    rw [newBlk]
    simp only [outK, chainK, AesCtr.ctrMode_out, AesCtr.ctrMode_chain, take_succ_blks s₀ hk, AesCtr.crypt_snoc]
  obtain ⟨x19', x20', x21', x24', other'⟩ := h.next g
  refine ⟨x19', x20', x21', x22₅, x23₅, x24', other', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [sp₅, sp₄, sp₃, c.sp, a.sp, h.sp]
  · rw [rd₅, rd₄, rd₃, c.rd, a.rd, h.rd]
  · rw [wr₅, wr₄, wr₃, c.wr, a.wr, h.wr]
  · exact h.frame.trans (stepFrame hk fStep)
  · rw [hp.blocksAt_step hk fStep, h.data, outSucc,
      set_prefix _ _ _ hl (by simp [Spec.Cbc.blocksAt]; exact hk)]
  · rw [newIv]
    simp only [chainK, AesCtr.ctrMode_chain, take_succ_blks s₀ hk, List.length_append, List.length_singleton,
      hlt, AesCtr.next_succ]

/-! ## Constant time -/

theorem pre_taint : ∃ h, (taint.check (Taint.ofRegs [.x19, .x20, .x21, .x22, .x23, .x24])
    (.block pre) h).isSome = true := ⟨_, by taint_decide⟩

theorem post_taint : ∃ h, (taint.check (Taint.ofRegs [.x21, .x22, .x23, .x24])
    (.block (xorOut ++ incr ++ advance)) h).isSome = true := ⟨_, by taint_decide⟩

theorem body_ct (v : BlocksImpl) : BodyCt AesCtr.ctrMode (body v.enc) :=
  fun hp hp' hq k => VG.Proof.AesCbc.AArch64.body_ct (D := fun s₀ _ => Sv s₀)
    (fun hq _ => by rw [Sv, Sv, pub_S hq])
    v.encOk v.encCt v.encNoFrames pre_taint post_taint
    (@fun _ hp _ _ _ h => WP.mono (preA_wp hp h) fun _ a => Mid.of h a.pre a.saved a.sp) hp hp' hq k

end VG.Proof.AesCtr.AArch64
