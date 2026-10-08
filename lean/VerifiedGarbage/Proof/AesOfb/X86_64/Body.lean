import VerifiedGarbage.Proof.AesOfb.Spec
import VerifiedGarbage.Proof.AesCbc.X86_64.CT
import VerifiedGarbage.Impl.AesOfb.X86_64

/-!
# AES-OFB on x86-64: one block, and constant time

`body_ok`: one run of `body` takes the loop invariant AES-CBC's proofs
share (`Proof/AesCbc/X86_64/Loop.lean`) from `k` blocks to `k + 1`, for
`ofbMode`, for any implementation of the block functions (`BlocksImpl`).
`body_ct`: it is constant time, by the shared framework, with the call on
the block at `iv`.
-/

namespace VG.Proof.AesOfb.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesOfb.X86_64
open VG.Impl.AesCbc.X86_64 (whole xorInto advance)
open VG.Proof.AesCbc
open VG.Proof.AesCbc.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86_64 (BlocksImpl)

theorem ivArgs_ok (s : State) :
    ∃ s', runBlock isa ivArgs s = some s' ∧
      s'.gpr .rdi = s.gpr .rbx ∧ s'.gpr .rsi = s.gpr .rbp ∧ s'.gpr .rdx = s.gpr .r12 ∧
      s'.gpr .rcx = 1 ∧ s'.gpr .r8 = s.gpr .r15 ∧ (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [ivArgs, runBlock_cons, runStep_some, exec, readSrc, Option.map_some]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
  · simp [gpr_setReg, State.setReg32]
  · simp [gpr_setReg, State.setReg32]
  · simp [gpr_setReg, State.setReg32]
  · simp [gpr_setReg, State.setReg32]
  · simp [gpr_setReg, State.setReg32]
  · intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg, State.setReg32]

/-- The arguments of a call on the block at `iv`, with the working space at
the start of the scratch buffer. -/
theorem callPreIv {s₀ : State} (hp : UPre s₀) {s : State}
    (rdi : s.gpr .rdi = W s₀) (rsi : s.gpr .rsi = s₀.gpr .rsi) (rdx : s.gpr .rdx = Iv s₀)
    (rcx : s.gpr .rcx = 1) (r8 : s.gpr .r8 = S s₀) (rsp : s.gpr .rsp = s₀.gpr .rsp)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    CallPre s (W s₀) (Iv s₀) (S s₀) (R s₀) where
  rdi := rdi
  rsi := by rw [rsi, rsi_ofNat]
  rdx := rdx
  rcx := rcx
  r8 := r8
  rounds := hp.rounds
  wd := hp.sch_iv
  ws := hp.sch_scr.sub_right (Region.sub_prefix (by decide))
  ds := hp.iv_scr.sub_right (Region.sub_prefix (by decide))
  stkW := by rw [rsp]; exact hp.stk_sch
  stkD := by rw [rsp]; exact hp.stk_iv
  stkS := by rw [rsp]; exact hp.stk_scr.sub_right (Region.sub_prefix (by decide))
  wrap := hp.iv_wrap
  reads := by
    rw [hrd, hwr, hp.rd, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨schR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨ivR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩
  writes := by
    rw [hwr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨ivR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩

/-- What the code before the call leaves. -/
structure IvA (s₀ : State) (s s₁ : State) : Prop where
  pre : CallPre s₁ (W s₀) (Iv s₀) (S s₀) (R s₀)
  saved : ∀ r ∈ calleeSaved, s₁.gpr r = s.gpr r
  mem : s₁.mem = s.mem
  rd : s₁.rd = s.rd
  wr : s₁.wr = s.wr

theorem ivA_wp {M : Mode} {s₀ : State} (hp : UPre s₀) {k : Nat} {s : State} (h : LInv M s₀ k s) :
    WP isa (.block ivArgs) s (IvA s₀ s) := by
  obtain ⟨s₁, run₁, rdi₁, rsi₁, rdx₁, rcx₁, r8₁, cs₁, mem₁, rd₁, wr₁⟩ := ivArgs_ok s
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  exact ⟨callPreIv hp (by rw [rdi₁, h.rbx]) (by rw [rsi₁, h.rbp]) (by rw [rdx₁, h.r12]) rcx₁
    (by rw [r8₁, h.r15]) (by rw [cs₁ .rsp (by simp [calleeSaved]), h.rsp]) (by rw [rd₁, h.rd])
    (by rw [wr₁, h.wr]), cs₁, mem₁, rd₁, wr₁⟩

theorem body_ok (v : BlocksImpl) : BodyOk ofbMode (body v.enc) := by
  intro s₀ hp k hk s h
  refine WP.seq (WP.mono (ivA_wp hp h) fun s₁ a => ?_)
  have rsp₁ : s₁.gpr .rsp = s₀.gpr .rsp := by rw [a.saved .rsp (by simp [calleeSaved]), h.rsp]
  refine WP.seq (WP.mono (blk_call v.encOk v.encNosp v.encDepth a.pre) fun s₂ c => ?_)
  have g₂ (r : Reg) (hr : r ∈ calleeSaved) : s₂.gpr r = s.gpr r := by rw [c.saved r hr, a.saved r hr]
  have hW₂ : s₂.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [c.wr, a.wr, h.wrs hp]
  have hR₂ : s₂.rd ++ s₂.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by
    rw [c.rd, c.wr, a.rd, a.wr, h.regs hp]
  obtain ⟨s₃, run₃, g₃, mem₃, rd₃, wr₃⟩ :=
    xorInto_ok s₂ (P := blk s₀ k) (Q := Iv s₀) (by rw [g₂ .r13 (by simp [calleeSaved]), h.r13])
      (by rw [g₂ .r12 (by simp [calleeSaved]), h.r12])
      (by rw [hR₂]; exact in_rw (by simp) (hp.cBlk0 hk)) (by rw [hR₂]; exact in_rw (by simp) (hp.cBlk8 hk))
      (by rw [hR₂]; exact in_rw (by simp) cIv0) (by rw [hR₂]; exact in_rw (by simp) cIv8)
      (by rw [hW₂]; exact in_rw (by simp) (hp.cBlk0 hk)) (by rw [hW₂]; exact in_rw (by simp) (hp.cBlk8 hk))
  obtain ⟨s₄, run₄, r13₄, r14₄, zf₄, keep₄, mem₄, rd₄, wr₄⟩ := advance_regs (s := s₃) hk
    (by rw [g₃ _ (by decide), g₂ .r13 (by simp [calleeSaved]), h.r13])
    (by rw [g₃ _ (by decide), g₂ .r14 (by simp [calleeSaved]), h.r14])
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨s₃, run₃, WP.of_runBlock ⟨s₄, run₄, ?_⟩⟩
  have g (r : Reg) (hr : r ∈ calleeSaved) (h13 : r ≠ .r13) (h14 : r ≠ .r14) : s₄.gpr r = s.gpr r := by
    rw [keep₄ r h13 h14, g₃ r (calleeSaved_ne_rax hr), g₂ r hr]
  -- Memory.
  have f₂ : Frame [ivR s₀, ⟨S s₀, 2048⟩, stkR s₀] s.mem s₂.mem := by
    have fr := c.frame; rw [rsp₁, a.mem] at fr; exact fr
  have f₃ : Frame [⟨blk s₀ k, 16⟩] s₂.mem s₃.mem := by rw [mem₃]; exact xorMem_frame _ _ _
  have fStep : Frame [⟨blk s₀ k, 16⟩, ivR s₀, ⟨S s₀, 2064⟩, stkR s₀] s.mem s₄.mem := by
    rw [mem₄]
    refine (f₂.sub fun r hr => ?_).trans (f₃.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨⟨S s₀, 2064⟩, by simp, Region.sub_prefix (by decide)⟩
      · exact ⟨stkR s₀, by simp, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
  have big : Frame (Big s₀) s₀.mem s.mem := UPre.big_of h.frame
  -- The new output block, and the data block.
  have hblk := h.block hk
  have newIv : bytesAt s₄.mem (Iv s₀) 16 =
      Spec.Cbc.aesWith (R s₀) (wK s₀) (chainK ofbMode s₀ k) := by
    rw [mem₄, mem₃, bytesAt_frame (xorMem_frame s₂.mem (blk s₀ k) (Iv s₀)) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (hp.blk_iv hk).symm) (by decide),
      c.out, a.mem, UPre.sched_bytes hp big, ← aesWith_state, h.iv]
  have newBlk : bytesAt s₄.mem (blk s₀ k) 16 =
      Spec.Cbc.xor ((blks s₀)[k]'(by simp [Spec.Cbc.blocksAt]; exact hk)) (bytesAt s₄.mem (Iv s₀) 16) := by
    rw [mem₄, mem₃, xorMem_bytes _ (hp.blk_iv hk), ← hblk,
      bytesAt_frame f₂ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact hp.blk_iv hk
        · exact (hp.data_scr.sub_left (UPre.data_sub hk)).sub_right (Region.sub_prefix (by decide))
        · exact (hp.stk_data.sub_right (UPre.data_sub hk)).symm) (by decide),
      bytesAt_frame (xorMem_frame s₂.mem (blk s₀ k) (Iv s₀)) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (hp.blk_iv hk).symm) (by decide)]
  have hl : ((blks s₀).take k).length = k := by simp [Spec.Cbc.blocksAt]; omega
  have outSucc : outK ofbMode s₀ (k + 1) = outK ofbMode s₀ k ++ [bytesAt s₄.mem (blk s₀ k) 16] := by
    rw [newBlk, newIv]
    simp only [outK, chainK, ofbMode_out, ofbMode_chain, take_succ_blks s₀ hk, crypt_snoc, hl]
  have hl' : (outK ofbMode s₀ k).length = k := by rw [outK, Mode.length_out, hl]
  refine ⟨⟨?_, ?_, ?_, r13₄, r14₄, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, zf₄⟩
  · rw [g .rbx (by simp [calleeSaved]) (by decide) (by decide), h.rbx]
  · rw [g .rbp (by simp [calleeSaved]) (by decide) (by decide), h.rbp]
  · rw [g .r12 (by simp [calleeSaved]) (by decide) (by decide), h.r12]
  · rw [g .r15 (by simp [calleeSaved]) (by decide) (by decide), h.r15]
  · rw [g .rsp (by simp [calleeSaved]) (by decide) (by decide), h.rsp]
  · rw [rd₄, rd₃, c.rd, a.rd, h.rd]
  · rw [wr₄, wr₃, c.wr, a.wr, h.wr]
  · exact h.frame.trans (stepFrame hk fStep)
  · rw [hp.blocksAt_step hk fStep, h.data, outSucc,
      set_prefix _ _ _ hl' (by simp [Spec.Cbc.blocksAt]; exact hk)]
  · rw [newIv]
    simp only [chainK, ofbMode_chain, take_succ_blks s₀ hk, List.length_append, List.length_singleton, hl,
      next_succ]

/-! ## Constant time -/

theorem pre_taint : ∃ h, (taint.check (Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp])
    (.block ivArgs) h).isSome = true := ⟨_, by taint_decide⟩

theorem post_taint : ∃ h, (taint.check (Taint.ofRegs [.r12, .r13, .r14, .r15])
    (.block (xorInto .r13 .r12 ++ advance)) h).isSome = true := ⟨_, by taint_decide⟩

theorem body_ct (v : BlocksImpl) : BodyCt ofbMode (body v.enc) :=
  fun hp hp' hq k => VG.Proof.AesCbc.X86_64.body_ct (D := fun s₀ _ => Iv s₀) (fun hq _ => pub_Iv hq)
    v.encOk v.encCt v.encNosp v.encDepth pre_taint post_taint
    (@fun _ hp _ _ _ h => WP.mono (ivA_wp hp h) fun _ a => Mid.of h a.pre a.saved) hp hp' hq k

end VG.Proof.AesOfb.X86_64
