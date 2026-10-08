import VerifiedGarbage.Proof.AesOfb.Spec
import VerifiedGarbage.Proof.AesCbc.AArch64.CT
import VerifiedGarbage.Impl.AesOfb.AArch64

/-!
# AES-OFB on AArch64: one block, and constant time

`body_ok`: one run of `body` takes the loop invariant AES-CBC's proofs
share (`Proof/AesCbc/AArch64/Loop.lean`) from `k` blocks to `k + 1`, for
`ofbMode`, for any implementation of the block functions (`BlocksImpl`).
`body_ct`: it is constant time, by the shared framework, with the call on
the block at `iv`.
-/

namespace VG.Proof.AesOfb.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesOfb.AArch64
open VG.Impl.AesCbc.AArch64 (whole xorInto advance)
open VG.Proof.AesCbc
open VG.Proof.AesCbc.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.AArch64 (BlocksImpl)

theorem ivArgs_ok (s : State) :
    ∃ s', runBlock isa ivArgs s = some s' ∧
      s'.gpr .x0 = s.gpr .x19 ∧ s'.gpr .x1 = s.gpr .x20 ∧ s'.gpr .x2 = s.gpr .x21 ∧
      s'.gpr .x3 = 1 ∧ s'.gpr .x4 = s.gpr .x24 ∧ (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by crun [ivArgs], ?_⟩
  refine ⟨by simp [gpr_write], by simp [gpr_write], by simp [gpr_write], ?_, by simp [gpr_write],
    fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  · simp [gpr_write]
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_write]

/-- The arguments of a call on the block at `iv`, with the working space at
the start of the scratch buffer. -/
theorem callPreIv {s₀ : State} (hp : UPre s₀) {s : State}
    (x0 : s.gpr .x0 = W s₀) (x1 : s.gpr .x1 = s₀.gpr .x1) (x2 : s.gpr .x2 = Iv s₀)
    (x3 : s.gpr .x3 = 1) (x4 : s.gpr .x4 = S s₀) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    CallPre s (W s₀) (Iv s₀) (S s₀) (R s₀) where
  x0 := x0
  x1 := by rw [x1, x1_ofNat]
  x2 := x2
  x3 := x3
  x4 := x4
  rounds := hp.rounds
  wd := hp.sch_iv
  ws := hp.sch_scr.sub_right (Region.sub_prefix (by decide))
  ds := hp.iv_scr.sub_right (Region.sub_prefix (by decide))
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
  saved : ∀ r ∈ preserved, s₁.gpr r = s.gpr r
  sp : s₁.sp = s.sp
  mem : s₁.mem = s.mem
  rd : s₁.rd = s.rd
  wr : s₁.wr = s.wr

theorem ivA_wp {M : Mode} {s₀ : State} (hp : UPre s₀) {k : Nat} {s : State} (h : LInv M s₀ k s) :
    WP isa (.block ivArgs) s (IvA s₀ s) := by
  obtain ⟨s₁, run₁, x0₁, x1₁, x2₁, x3₁, x4₁, cs₁, sp₁, mem₁, rd₁, wr₁⟩ := ivArgs_ok s
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  exact ⟨callPreIv hp (by rw [x0₁, h.x19]) (by rw [x1₁, h.x20]) (by rw [x2₁, h.x21]) x3₁
    (by rw [x4₁, h.x24]) (by rw [rd₁, h.rd]) (by rw [wr₁, h.wr]), cs₁, sp₁, mem₁, rd₁, wr₁⟩

theorem body_ok (v : BlocksImpl) : BodyOk ofbMode (body v.enc) := by
  intro s₀ hp k hk s h
  refine WP.seq (WP.mono (ivA_wp hp h) fun s₁ a => ?_)
  refine WP.seq (WP.mono (blk_call v.encOk v.encNoFrames a.pre) fun s₂ c => ?_)
  have g₂ (r : Reg) (hr : r ∈ preserved) (h30 : r ≠ .x30) : s₂.gpr r = s.gpr r := by
    rw [c.saved r hr h30, a.saved r hr]
  have hW₂ : s₂.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [c.wr, a.wr, h.wrs hp]
  have hR₂ : s₂.rd ++ s₂.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by
    rw [c.rd, c.wr, a.rd, a.wr, h.regs hp]
  obtain ⟨s₃, run₃, g₃, sp₃, mem₃, rd₃, wr₃⟩ :=
    xorInto_ok s₂ (P := blk s₀ k) (Q := Iv s₀) (by rw [g₂ .x22 (by simp [preserved]) (by decide), h.x22])
      (by rw [g₂ .x21 (by simp [preserved]) (by decide), h.x21])
      (by rw [hR₂]; exact in_rw (by simp) (hp.cBlk0 hk)) (by rw [hR₂]; exact in_rw (by simp) (hp.cBlk8 hk))
      (by rw [hR₂]; exact in_rw (by simp) cIv0) (by rw [hR₂]; exact in_rw (by simp) cIv8)
      (by rw [hW₂]; exact in_rw (by simp) (hp.cBlk0 hk)) (by rw [hW₂]; exact in_rw (by simp) (hp.cBlk8 hk))
  obtain ⟨s₄, run₄, x22₄, x23₄, keep₄, sp₄, mem₄, rd₄, wr₄⟩ := advance_regs (s := s₃) hk
    (by rw [g₃ _ (by decide) (by decide), g₂ .x22 (by simp [preserved]) (by decide), h.x22])
    (by rw [g₃ _ (by decide) (by decide), g₂ .x23 (by simp [preserved]) (by decide), h.x23])
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨s₃, run₃, WP.of_runBlock ⟨s₄, run₄, ?_⟩⟩
  have g (r : Reg) (hr : r ∈ preserved) (h30 : r ≠ .x30) (h22 : r ≠ .x22) (h23 : r ≠ .x23) :
      s₄.gpr r = s.gpr r := by
    rw [keep₄ r h22 h23, g₃ r (preserved_ne hr).1 (preserved_ne hr).2, g₂ r hr h30]
  -- Memory.
  have f₂ : Frame [ivR s₀, ⟨S s₀, 2048⟩] s.mem s₂.mem := by
    have fr := c.frame; rw [a.mem] at fr; exact fr
  have f₃ : Frame [⟨blk s₀ k, 16⟩] s₂.mem s₃.mem := by rw [mem₃]; exact xorMem_frame _ _ _
  have fStep : Frame [⟨blk s₀ k, 16⟩, ivR s₀, ⟨S s₀, 2064⟩] s.mem s₄.mem := by
    rw [mem₄]
    refine (f₂.sub fun r hr => ?_).trans (f₃.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨⟨S s₀, 2064⟩, by simp, Region.sub_prefix (by decide)⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
  have big : Frame (Big s₀) s₀.mem s.mem := UPre.big_of h.frame
  have one (r : Region) (P : Addr) (hd : (⟨P, 16⟩ : Region).Disjoint r) :
      ∀ r' ∈ [r], (⟨P, 16⟩ : Region).Disjoint r' := fun r' hr' => by
    simp only [List.mem_singleton] at hr'; subst hr'; exact hd
  -- The new output block, and the data block.
  have hblk := h.block hk
  have newIv : bytesAt s₄.mem (Iv s₀) 16 =
      Spec.Cbc.aesWith (R s₀) (wK s₀) (chainK ofbMode s₀ k) := by
    rw [mem₄, mem₃, Proof.Cmac.bytesAt_frame (xorMem_frame s₂.mem (blk s₀ k) (Iv s₀))
        (one _ _ (hp.blk_iv hk).symm) (by decide),
      c.out, a.mem, UPre.sched_bytes hp big, ← aesWith_state, h.iv]
  have newBlk : bytesAt s₄.mem (blk s₀ k) 16 =
      Spec.Cbc.xor ((blks s₀)[k]'(by simp [Spec.Cbc.blocksAt]; exact hk)) (bytesAt s₄.mem (Iv s₀) 16) := by
    rw [mem₄, mem₃, xorMem_bytes _ (hp.blk_iv hk), ← hblk,
      Proof.Cmac.bytesAt_frame f₂ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hp.blk_iv hk
        · exact (hp.data_scr.sub_left (UPre.data_sub hk)).sub_right (Region.sub_prefix (by decide))) (by decide),
      Proof.Cmac.bytesAt_frame (xorMem_frame s₂.mem (blk s₀ k) (Iv s₀)) (one _ _ (hp.blk_iv hk).symm)
        (by decide)]
  have hl : ((blks s₀).take k).length = k := by simp [Spec.Cbc.blocksAt]; omega
  have outSucc : outK ofbMode s₀ (k + 1) = outK ofbMode s₀ k ++ [bytesAt s₄.mem (blk s₀ k) 16] := by
    rw [newBlk, newIv]
    simp only [outK, chainK, ofbMode_out, ofbMode_chain, take_succ_blks s₀ hk, crypt_snoc, hl]
  have hl' : (outK ofbMode s₀ k).length = k := by rw [outK, Mode.length_out, hl]
  obtain ⟨x19', x20', x21', x24', other'⟩ := h.next g
  refine ⟨x19', x20', x21', x22₄, x23₄, x24', other', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [sp₄, sp₃, c.sp, a.sp, h.sp]
  · rw [rd₄, rd₃, c.rd, a.rd, h.rd]
  · rw [wr₄, wr₃, c.wr, a.wr, h.wr]
  · exact h.frame.trans (stepFrame hk fStep)
  · rw [hp.blocksAt_step hk fStep, h.data, outSucc,
      set_prefix _ _ _ hl' (by simp [Spec.Cbc.blocksAt]; exact hk)]
  · rw [newIv]
    simp only [chainK, ofbMode_chain, take_succ_blks s₀ hk, List.length_append, List.length_singleton, hl,
      next_succ]

/-! ## Constant time -/

theorem pre_taint : ∃ h, (taint.check (Taint.ofRegs [.x19, .x20, .x21, .x22, .x23, .x24])
    (.block ivArgs) h).isSome = true := ⟨_, by taint_decide⟩

theorem post_taint : ∃ h, (taint.check (Taint.ofRegs [.x21, .x22, .x23, .x24])
    (.block (xorInto ++ advance)) h).isSome = true := ⟨_, by taint_decide⟩

theorem body_ct (v : BlocksImpl) : BodyCt ofbMode (body v.enc) :=
  fun hp hp' hq k => VG.Proof.AesCbc.AArch64.body_ct (D := fun s₀ _ => Iv s₀) (fun hq _ => pub_Iv hq)
    v.encOk v.encCt v.encNoFrames pre_taint post_taint
    (@fun _ hp _ _ _ h => WP.mono (ivA_wp hp h) fun _ a => Mid.of h a.pre a.saved a.sp) hp hp' hq k

end VG.Proof.AesOfb.AArch64
