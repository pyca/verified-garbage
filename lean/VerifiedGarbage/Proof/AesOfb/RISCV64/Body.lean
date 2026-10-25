module

public import VerifiedGarbage.Proof.AesOfb.Spec
public import VerifiedGarbage.Proof.AesCbc.RISCV64.CT
public import VerifiedGarbage.Impl.AesOfb.RISCV64
import VerifiedGarbage.Proof.AesCbc.RISCV64.Body
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.AesOfb.Spec
meta import VerifiedGarbage.Proof.AesCbc.RISCV64.CT
meta import VerifiedGarbage.Impl.AesOfb.RISCV64
meta import VerifiedGarbage.Proof.AesCbc.RISCV64.Body
meta import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Aes.RISCV64.BlocksVerified
meta import VerifiedGarbage.Proof.Aes.RISCV64.BlocksVerified

/-!
# AES-OFB on RISC-V: one block, and constant time

As on PPC64LE (`Proof/AesOfb/PPC64LE/Body.lean`): `body_ok`, one run of
`body` takes the loop invariant AES-CBC's proofs share
(`Proof/AesCbc/RISCV64/Loop.lean`) from `k` blocks to `k + 1`, for
`ofbMode`; `body_ct`, it is constant time, by the shared framework, with the
call on the block at `iv`.
-/

@[expose] public section

namespace VG.Proof.AesOfb.RISCV64

open VG VG.RISCV64 VG.Impl.AesOfb.RISCV64
open VG.Impl.AesCbc.RISCV64 (whole xorInto advance encCall mov)
open VG.Proof.AesCbc
open VG.Proof.AesCbc.RISCV64
open VG.Spec.Aes (bytesAt)

/-- The arguments of a call on the block at `iv`, with the working space at
the start of the scratch buffer. -/
theorem callPreIv {s₀ : State} (hp : UPre s₀) {s : State}
    (a0 : s.gpr .a0 = W s₀) (a1 : s.gpr .a1 = s₀.gpr .a1) (a2 : s.gpr .a2 = Iv s₀)
    (a3 : s.gpr .a3 = BitVec.ofNat 64 1) (a4 : s.gpr .a4 = S s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    CallPre s (W s₀) (Iv s₀) (S s₀) (R s₀) where
  a0 := a0
  a1 := by rw [a1, a1_ofNat]
  a2 := a2
  a3 := a3
  a4 := a4
  rounds := hp.rounds
  wd := hp.sch_iv
  ws := hp.sch_scr.sub_right wsR_sub
  ds := hp.iv_scr.sub_right wsR_sub
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

theorem ivA_wp {M : Mode} {s₀ : State} (hp : UPre s₀) {k : Nat} {s : State} (h : LInv M s₀ k s) :
    WP isa (.block ivArgs) s (Pre s₀ (Iv s₀) s.mem s) := by
  unfold ivArgs mov
  refine Steps.wp_mv fun s₁ u₁ => Steps.wp_mv fun s₂ u₂ => Steps.wp_mv fun s₃ u₃ =>
    Steps.wp_li (imm := 1) (by decide) fun s₄ u₄ => Steps.wp_mv fun s₅ u₅ => WP.block_nil ?_
  have keep (r : Reg) (hr : r ∈ preserved) : s₅.gpr r = s.gpr r := by
    have h' := (preserved_ne hr).1
    simp only [argRegs5, List.mem_cons, List.not_mem_nil, or_false, not_or] at h'
    obtain ⟨h0, h1, h2, h3, h4⟩ := h'
    rw [u₅.other _ h4, u₄.other _ h3, u₃.other _ h2, u₂.other _ h1, u₁.other _ h0]
  refine ⟨callPreIv hp ?_ ?_ ?_ ?_ ?_ ?_ ?_, keep, ?_, ?_, ?_, ?_⟩
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.gpr, h.s1]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr,
      u₁.other _ (by decide), h.s2]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), h.s3]
  · rw [u₅.other _ (by decide), u₄.gpr]
  · rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), h.s6]
  · rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd]
  · rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr]
  · rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  · rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]

theorem body_ok : BodyOk ofbMode body := by
  intro s₀ hp k hk s h
  refine WP.seq (WP.mono (ivA_wp hp h) fun s₁ a => ?_)
  refine WP.seq (WP.mono (blk_call Proof.Aes.RISCV64.encryptBlocks_correct encryptBlocks_noFrames a.pre)
    fun s₂ c => ?_)
  have g₂ (r : Reg) (hr : r ∈ preserved) : s₂.gpr r = s.gpr r := by rw [c.saved r hr, a.saved r hr]
  have hW₂ : s₂.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [c.wr, a.wr, h.wrs hp]
  have hR₂ : s₂.rd ++ s₂.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by
    rw [c.rd, c.wr, a.rd, a.wr, h.regs hp]
  refine xorInto_wp (P := blk s₀ k) (Q := Iv s₀) (by decide) (by decide) (by decide) (by decide)
    (by rw [g₂ .s4 (by decide), h.s4]) (by rw [g₂ .s3 (by decide), h.s3])
    ⟨ivR s₀, by rw [hR₂]; simp, fun _ h => h⟩ ⟨dataR s₀, by rw [hW₂]; simp, UPre.data_sub hk⟩
    (hp.blk_iv hk) fun s₃ g₃ x₃ f₃ rd₃ wr₃ sp₃ => advance_regs (s := s₃) hk
      (by rw [g₃ _ (by decide) (by decide), g₂ .s4 (by decide), h.s4])
      (by rw [g₃ _ (by decide) (by decide), g₂ .s5 (by decide), h.s5])
      fun s₄ s4₄ s5₄ keep₄ mem₄ rd₄ wr₄ sp₄ => ?_
  have g (r : Reg) (hr : r ∈ preserved) (h4 : r ≠ .s4) (h5 : r ≠ .s5) : s₄.gpr r = s.gpr r := by
    rw [keep₄ r h4 h5, g₃ r (preserved_ne hr).2.2.1 (preserved_ne hr).2.2.2, g₂ r hr]
  -- Memory.
  have f₂ : Frame [ivR s₀, ⟨S s₀, 2048⟩] s.mem s₂.mem := by
    have fr := c.frame; rw [a.mem] at fr; exact fr
  have fStep : Frame [⟨blk s₀ k, 16⟩, ivR s₀, wsR s₀, cR s₀] s.mem s₄.mem := by
    rw [mem₄]
    refine (f₂.mono fun r hr => ?_).trans (f₃.mono (by simp))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp
  have big : Frame (Big s₀) s₀.mem s.mem := UPre.big_of h.frame
  -- The new output block, and the data block.
  have hblk := h.block hk
  have newIv : bytesAt s₄.mem (Iv s₀) 16 =
      Spec.Cbc.aesWith (R s₀) (wK s₀) (chainK ofbMode s₀ k) := by
    rw [mem₄, bytesAt_frame f₃ (one (hp.blk_iv hk).symm) (by decide), c.out, a.mem,
      UPre.sched_bytes hp big, ← aesWith_state, h.iv]
  have newBlk : bytesAt s₄.mem (blk s₀ k) 16 =
      Spec.Cbc.xor ((blks s₀)[k]'(by simp [Spec.Cbc.blocksAt]; exact hk)) (bytesAt s₄.mem (Iv s₀) 16) := by
    rw [mem₄, x₃, ← hblk,
      bytesAt_frame f₂ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hp.blk_iv hk
        · exact (hp.data_scr.sub_left (UPre.data_sub hk)).sub_right wsR_sub)
        (by decide),
      bytesAt_frame f₃ (one (hp.blk_iv hk).symm) (by decide)]
  have hl : ((blks s₀).take k).length = k := by simp [Spec.Cbc.blocksAt]; omega
  have outSucc : outK ofbMode s₀ (k + 1) = outK ofbMode s₀ k ++ [bytesAt s₄.mem (blk s₀ k) 16] := by
    rw [newBlk, newIv]
    simp only [outK, chainK, ofbMode_out, ofbMode_chain, take_succ_blks s₀ hk, AesOfb.crypt_snoc, hl]
  have hl' : (outK ofbMode s₀ k).length = k := by rw [outK, Mode.length_out, hl]
  refine ⟨?_, ?_, ?_, s4₄, s5₄, ?_, fun r hr hv => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [g .s1 (by decide) (by decide) (by decide), h.s1]
  · rw [g .s2 (by decide) (by decide) (by decide), h.s2]
  · rw [g .s3 (by decide) (by decide) (by decide), h.s3]
  · rw [g .s6 (by decide) (by decide) (by decide), h.s6]
  · rw [g r hr (fun e => hv (by simp [e])) (fun e => hv (by simp [e])), h.keep r hr hv]
  · rw [rd₄, rd₃, c.rd, a.rd, h.rd]
  · rw [wr₄, wr₃, c.wr, a.wr, h.wr]
  · rw [sp₄, sp₃, c.sp, a.sp, h.sp]
  · exact h.frame.trans (stepFrame hk fStep)
  · rw [hp.blocksAt_step hk fStep, h.data, outSucc,
      set_prefix _ _ _ hl' (by simp [Spec.Cbc.blocksAt]; exact hk)]
  · rw [newIv]
    simp only [chainK, ofbMode_chain, take_succ_blks s₀ hk, List.length_append, List.length_singleton, hl,
      AesOfb.next_succ]

/-! ## Constant time -/

theorem pre_taint : ∃ h, (taint.check (Taint.ofRegs vars) (.block ivArgs) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem post_taint : ∃ h, (taint.check (Taint.ofRegs [.s3, .s4, .s5, .s6])
    (.block (xorInto .s4 .s3 ++ advance)) h).isSome = true := ⟨_, by taint_decide⟩

theorem body_ct : BodyCt ofbMode body :=
  fun hp hp' hq k => VG.Proof.AesCbc.RISCV64.body_ct (D := fun s₀ _ => Iv s₀)
    (fun hq _ => pub_Iv hq) Proof.Aes.RISCV64.encryptBlocks_correct Proof.Aes.RISCV64.encryptBlocks_ct
    encryptBlocks_noFrames pre_taint post_taint (@fun _ hp _ _ _ h => WP.mono (ivA_wp hp h) fun _ a => ⟨_, a⟩)
    hp hp' hq k

end VG.Proof.AesOfb.RISCV64
