import VerifiedGarbage.Proof.AesCtr.X86_64.Steps
import VerifiedGarbage.Proof.AesCbc.X86_64.CT

/-!
# AES-CTR on x86-64: one block, and constant time

`body_ok`: one run of `body` takes the loop invariant AES-CBC's proofs share
(`Proof/AesCbc/X86_64/Loop.lean`) from `k` blocks to `k + 1`, for
`ctrMode`, for any implementation of the block functions (`BlocksImpl`).
The counter block is copied to the scratch buffer and enciphered there
(`preA_wp`, `call_ok`), the output block is XORed into the data block, and
the counter block is incremented (`Steps.lean`). `body_ct`: it is constant
time, by the shared framework, with the call on the copy.
-/

namespace VG.Proof.AesCtr.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesCtr.X86_64
open VG.Impl.AesCbc.X86_64 (whole copy advance at_ cOff)
open VG.Proof.AesCbc (copyMem copyMem_frame copyMem_bytes xorMem xorMem_frame xorMem_bytes aesWith_state
  set_prefix Mode)
open VG.Proof.AesCbc.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86_64 (BlocksImpl)

section
variable {s₀ : State} (hp : UPre s₀)
include hp

theorem UPre.sv_wrap : (Sv s₀).toNat + 16 ≤ 2 ^ 64 := by
  have := hp.scr_wrap
  rw [Sv, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 2048) (by decide),
    Nat.mod_eq_of_lt (by omega)]
  omega

/-- The arguments of a call on the copy of the counter block, with the
working space at the start of the scratch buffer. -/
theorem UPre.callPreSv {s : State}
    (rdi : s.gpr .rdi = W s₀) (rsi : s.gpr .rsi = s₀.gpr .rsi) (rdx : s.gpr .rdx = Sv s₀)
    (rcx : s.gpr .rcx = 1) (r8 : s.gpr .r8 = S s₀) (rsp : s.gpr .rsp = s₀.gpr .rsp)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    CallPre s (W s₀) (Sv s₀) (S s₀) (R s₀) where
  rdi := rdi
  rsi := by rw [rsi, rsi_ofNat]
  rdx := rdx
  rcx := rcx
  r8 := r8
  rounds := hp.rounds
  wd := hp.sch_scr.sub_right (UPre.scr_sub (by decide))
  ws := hp.sch_scr.sub_right (Region.sub_prefix (by decide))
  ds := hp.sv_scr
  stkW := by rw [rsp]; exact hp.stk_sch
  stkD := by rw [rsp]; exact hp.stk_scr.sub_right (UPre.scr_sub (by decide))
  stkS := by rw [rsp]; exact hp.stk_scr.sub_right (Region.sub_prefix (by decide))
  wrap := UPre.sv_wrap hp
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
  saved : ∀ r ∈ calleeSaved, s₁.gpr r = s.gpr r
  mem : s₁.mem = copyMem s.mem (Sv s₀) (Iv s₀)
  rd : s₁.rd = s.rd
  wr : s₁.wr = s.wr

theorem preA_wp {s₀ : State} (hp : UPre s₀) {k : Nat} {s : State} (h : LInv AesCtr.ctrMode s₀ k s) :
    WP isa (.block pre) s (PreA s₀ s) := by
  have hR := h.regs hp
  have hW := h.wrs hp
  obtain ⟨s₁, run₁, g₁, mem₁, rd₁, wr₁⟩ :=
    copy_ok s (dst := .r15) (src := .r12) (d := cOff) (e := 0) (P := Sv s₀) (Q := Iv s₀)
      (by rw [h.r15]; rfl) (by rw [h.r15]; exact sv8 _)
      (by rw [h.r12]; simp) (by rw [h.r12])
      (by rw [hR]; exact in_rw (by simp) cIv0) (by rw [hR]; exact in_rw (by simp) cIv8)
      (by rw [hW]; exact in_rw (by simp) cSv0) (by rw [hW]; exact in_rw (by simp) cSv8)
      (by decide) (by decide)
  obtain ⟨s₂, run₂, rdi₂, rsi₂, rdx₂, rcx₂, r8₂, cs₂, mem₂, rd₂, wr₂⟩ := args_ok s₁
  have keep (r : Reg) (hr : r ∈ calleeSaved) : s₂.gpr r = s.gpr r := by
    rw [cs₂ r hr, g₁ r (calleeSaved_ne_rax hr)]
  rw [pre_eq, WP.block_append_iff]
  refine WP.of_runBlock ⟨s₁, run₁, WP.of_runBlock ⟨s₂, run₂, ?_⟩⟩
  exact ⟨UPre.callPreSv hp (by rw [rdi₂, g₁ _ (by decide), h.rbx]) (by rw [rsi₂, g₁ _ (by decide), h.rbp])
      (by rw [rdx₂, g₁ _ (by decide), h.r15]) rcx₂ (by rw [r8₂, g₁ _ (by decide), h.r15])
      (by rw [keep .rsp (by simp [calleeSaved]), h.rsp]) (by rw [rd₂, rd₁, h.rd]) (by rw [wr₂, wr₁, h.wr]),
    keep, by rw [mem₂, mem₁], by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩

theorem body_ok (v : BlocksImpl) : BodyOk AesCtr.ctrMode (body v.enc) := by
  intro s₀ hp k hk s h
  refine WP.seq (WP.mono (preA_wp hp h) fun s₁ a => ?_)
  have rsp₁ : s₁.gpr .rsp = s₀.gpr .rsp := by rw [a.saved .rsp (by simp [calleeSaved]), h.rsp]
  refine WP.seq (WP.mono (blk_call v.encOk v.encNosp v.encDepth a.pre) fun s₂ c => ?_)
  have g₂ (r : Reg) (hr : r ∈ calleeSaved) : s₂.gpr r = s.gpr r := by rw [c.saved r hr, a.saved r hr]
  have hW₂ : s₂.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [c.wr, a.wr, h.wrs hp]
  have hR₂ : s₂.rd ++ s₂.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by
    rw [c.rd, c.wr, a.rd, a.wr, h.regs hp]
  obtain ⟨s₃, run₃, g₃, mem₃, rd₃, wr₃⟩ :=
    xorOut_ok s₂ (P := blk s₀ k) (Q := Sv s₀) (by rw [g₂ .r13 (by simp [calleeSaved]), h.r13])
      (by rw [g₂ .r15 (by simp [calleeSaved]), h.r15]) (by rw [g₂ .r15 (by simp [calleeSaved]), h.r15]; exact sv8 _)
      (by rw [hR₂]; exact in_rw (by simp) (hp.cBlk0 hk)) (by rw [hR₂]; exact in_rw (by simp) (hp.cBlk8 hk))
      (by rw [hR₂]; exact in_rw (by simp) cSv0) (by rw [hR₂]; exact in_rw (by simp) cSv8)
      (by rw [hW₂]; exact in_rw (by simp) (hp.cBlk0 hk)) (by rw [hW₂]; exact in_rw (by simp) (hp.cBlk8 hk))
  have g₃' (r : Reg) (hr : r ∈ calleeSaved) : s₃.gpr r = s.gpr r := by
    rw [g₃ r (calleeSaved_ne_rax hr), g₂ r hr]
  have hR₃ : s₃.rd ++ s₃.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by rw [rd₃, wr₃, hR₂]
  have hW₃ : s₃.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [wr₃, hW₂]
  obtain ⟨s₄, run₄, g₄, mem₄, rd₄, wr₄⟩ :=
    incr_ok s₃ (Q := Iv s₀) (by rw [g₃' .r12 (by simp [calleeSaved]), h.r12])
      (by rw [hR₃]; exact in_rw (by simp) cIv0) (by rw [hR₃]; exact in_rw (by simp) cIv8)
      (by rw [hW₃]; exact in_rw (by simp) cIv0) (by rw [hW₃]; exact in_rw (by simp) cIv8)
  have ne (r : Reg) (hr : r ∈ calleeSaved) : r ≠ .rcx := by
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  obtain ⟨s₅, run₅, r13₅, r14₅, zf₅, keep₅, mem₅, rd₅, wr₅⟩ := advance_regs (s := s₄) hk
    (by rw [g₄ _ (by decide) (by decide), g₃' .r13 (by simp [calleeSaved]), h.r13])
    (by rw [g₄ _ (by decide) (by decide), g₃' .r14 (by simp [calleeSaved]), h.r14])
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨s₄, run₄, WP.of_runBlock ⟨s₅, run₅, ?_⟩⟩
  have g (r : Reg) (hr : r ∈ calleeSaved) (h13 : r ≠ .r13) (h14 : r ≠ .r14) : s₅.gpr r = s.gpr r := by
    rw [keep₅ r h13 h14, g₄ r (calleeSaved_ne_rax hr) (ne r hr), g₃' r hr]
  -- Memory.
  have svSub : Region.Sub ⟨Sv s₀, 16⟩ ⟨S s₀, 2064⟩ := Offset.sub_base _ (by decide)
  have f₁ : Frame [⟨Sv s₀, 16⟩] s.mem s₁.mem := by rw [a.mem]; exact copyMem_frame _ _ _
  have f₃ : Frame [⟨blk s₀ k, 16⟩] s₂.mem s₃.mem := by rw [mem₃]; exact xorMem_frame _ _ _
  have f₄ : Frame [ivR s₀] s₃.mem s₄.mem := by rw [mem₄]; exact incMem_frame _ _
  have fStep : Frame [⟨blk s₀ k, 16⟩, ivR s₀, ⟨S s₀, 2064⟩, stkR s₀] s.mem s₅.mem := by
    rw [mem₅]
    refine (f₁.sub fun r hr => ?_).trans ((c.frame.sub fun r hr => ?_).trans
      ((f₃.sub fun r hr => ?_).trans (f₄.sub fun r hr => ?_)))
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨⟨S s₀, 2064⟩, by simp, svSub⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨⟨S s₀, 2064⟩, by simp, svSub⟩
      · exact ⟨⟨S s₀, 2064⟩, by simp, Region.sub_prefix (by decide)⟩
      · exact ⟨stkR s₀, by simp, by rw [rsp₁]; exact fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
  have big₁ : Frame (Big s₀) s₀.mem s₁.mem :=
    (UPre.big_of h.frame).trans (f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, by simp, UPre.scr_sub (by decide)⟩)
  have one (r : Region) (P : Addr) (hd : (⟨P, 16⟩ : Region).Disjoint r) :
      ∀ r' ∈ [r], (⟨P, 16⟩ : Region).Disjoint r' := fun r' hr' => by
    simp only [List.mem_singleton] at hr'; subst hr'; exact hd
  have callIv : ∀ r ∈ [⟨Sv s₀, 16⟩, ⟨S s₀, 2048⟩, below (s₁.gpr .rsp) 8], (ivR s₀).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.iv_sv
    · exact hp.iv_scr.sub_right (Region.sub_prefix (by decide))
    · rw [rsp₁]; exact hp.stk_iv.symm
  have callBlk : ∀ r ∈ [⟨Sv s₀, 16⟩, ⟨S s₀, 2048⟩, below (s₁.gpr .rsp) 8],
      (⟨blk s₀ k, 16⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.blk_sv hk
    · exact (hp.data_scr.sub_left (UPre.data_sub hk)).sub_right (Region.sub_prefix (by decide))
    · rw [rsp₁]; exact (hp.stk_data.sub_right (UPre.data_sub hk)).symm
  -- The counter block on entry to the block, and the data block before the XOR.
  have ivIn : bytesAt s₃.mem (Iv s₀) 16 = chainK AesCtr.ctrMode s₀ k := by
    rw [mem₃, bytesAt_frame (xorMem_frame _ _ _) (one _ _ (hp.blk_iv hk).symm) (by decide),
      bytesAt_frame c.frame callIv (by decide), a.mem,
      bytesAt_frame (copyMem_frame _ _ _) (one _ _ hp.iv_sv) (by decide), h.iv]
  have blkIn : bytesAt s₂.mem (blk s₀ k) 16 = (blks s₀)[k]'(by simp [Spec.Cbc.blocksAt]; exact hk) := by
    rw [bytesAt_frame c.frame callBlk (by decide), a.mem,
      bytesAt_frame (copyMem_frame _ _ _) (one _ _ (hp.blk_sv hk)) (by decide), h.block hk]
  have outBlk : bytesAt s₂.mem (Sv s₀) 16 = Spec.Cbc.aesWith (R s₀) (wK s₀) (chainK AesCtr.ctrMode s₀ k) := by
    rw [c.out, UPre.sched_bytes hp big₁, ← aesWith_state, a.mem, copyMem_bytes _ hp.iv_sv.symm, h.iv]
  have newBlk : bytesAt s₅.mem (blk s₀ k) 16 =
      Spec.Cbc.xor ((blks s₀)[k]'(by simp [Spec.Cbc.blocksAt]; exact hk))
        (Spec.Cbc.aesWith (R s₀) (wK s₀) (chainK AesCtr.ctrMode s₀ k)) := by
    rw [mem₅, mem₄, bytesAt_frame (incMem_frame _ _) (one _ _ (hp.blk_iv hk)) (by decide), mem₃,
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
  refine ⟨⟨?_, ?_, ?_, r13₅, r14₅, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, zf₅⟩
  · rw [g .rbx (by simp [calleeSaved]) (by decide) (by decide), h.rbx]
  · rw [g .rbp (by simp [calleeSaved]) (by decide) (by decide), h.rbp]
  · rw [g .r12 (by simp [calleeSaved]) (by decide) (by decide), h.r12]
  · rw [g .r15 (by simp [calleeSaved]) (by decide) (by decide), h.r15]
  · rw [g .rsp (by simp [calleeSaved]) (by decide) (by decide), h.rsp]
  · rw [rd₅, rd₄, rd₃, c.rd, a.rd, h.rd]
  · rw [wr₅, wr₄, wr₃, c.wr, a.wr, h.wr]
  · exact h.frame.trans (stepFrame hk fStep)
  · rw [hp.blocksAt_step hk fStep, h.data, outSucc,
      set_prefix _ _ _ hl (by simp [Spec.Cbc.blocksAt]; exact hk)]
  · rw [newIv]
    simp only [chainK, AesCtr.ctrMode_chain, take_succ_blks s₀ hk, List.length_append, List.length_singleton,
      hlt, AesCtr.next_succ]

/-! ## Constant time -/

theorem pre_taint : ∃ h, (taint.check (Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp])
    (.block pre) h).isSome = true := ⟨_, by taint_decide⟩

theorem post_taint : ∃ h, (taint.check (Taint.ofRegs [.r12, .r13, .r14, .r15])
    (.block (xorOut ++ incr ++ advance)) h).isSome = true := ⟨_, by taint_decide⟩

theorem body_ct (v : BlocksImpl) : BodyCt AesCtr.ctrMode (body v.enc) :=
  fun hp hp' hq k => VG.Proof.AesCbc.X86_64.body_ct (D := fun s₀ _ => Sv s₀)
    (fun hq _ => by rw [Sv, Sv, pub_S hq])
    v.encOk v.encCt v.encNosp v.encDepth pre_taint post_taint
    (@fun _ hp _ _ _ h => WP.mono (preA_wp hp h) fun _ a => Mid.of h a.pre a.saved) hp hp' hq k

end VG.Proof.AesCtr.X86_64
