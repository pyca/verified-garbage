module

public import VerifiedGarbage.Proof.AesOfb.Spec
public import VerifiedGarbage.Proof.AesCbc.PPC64LE.CT
public import VerifiedGarbage.Impl.AesOfb.PPC64LE
import VerifiedGarbage.Proof.AesCbc.PPC64LE.Body
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.AesOfb.Spec
meta import VerifiedGarbage.Proof.AesCbc.PPC64LE.CT
meta import VerifiedGarbage.Impl.AesOfb.PPC64LE
meta import VerifiedGarbage.Proof.AesCbc.PPC64LE.Body
meta import VerifiedGarbage.Proof.Framework.Offset

/-!
# AES-OFB on PPC64LE: one block, and constant time

As on x86-64 (`Proof/AesOfb/X86_64/Body.lean`): `body_ok`, one run of
`body` takes the loop invariant AES-CBC's proofs share
(`Proof/AesCbc/PPC64LE/Loop.lean`) from `k` blocks to `k + 1`, for
`ofbMode`; `body_ct`, it is constant time, by the shared framework, with the
call on the block at `iv`.
-/

@[expose] public section

namespace VG.Proof.AesOfb.PPC64LE

open VG VG.PPC64LE VG.Impl.AesOfb.PPC64LE
open VG.Impl.AesCbc.PPC64LE (whole xorInto advance encCall mov)
open VG.Proof.AesCbc
open VG.Proof.AesCbc.PPC64LE
open VG.Spec.Aes (bytesAt)

/-- The arguments of a call on the block at `iv`, with the working space at
the start of the scratch buffer. -/
theorem callPreIv {s₀ : State} (hp : UPre s₀) {s : State}
    (r3 : s.gpr .r3 = W s₀) (r4 : s.gpr .r4 = s₀.gpr .r4) (r5 : s.gpr .r5 = Iv s₀)
    (r6 : s.gpr .r6 = BitVec.ofNat 64 1) (r7 : s.gpr .r7 = S s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    CallPre s (W s₀) (Iv s₀) (S s₀) (R s₀) where
  r3 := r3
  r4 := by rw [r4, r4_ofNat]
  r5 := r5
  r6 := r6
  r7 := r7
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

theorem ivA_wp {M : Mode} {s₀ : State} (hp : UPre s₀) {k : Nat} {s : State} (h : LInv M s₀ k s) :
    WP isa (.block ivArgs) s (Pre s₀ (Iv s₀) s.mem s) := by
  unfold ivArgs mov
  refine wp_mr fun s₁ u₁ => wp_mr fun s₂ u₂ => wp_mr fun s₃ u₃ => wp_li (by decide) fun s₄ u₄ =>
    wp_mr fun s₅ u₅ => wp_nil ?_
  have keep (r : Reg) (hr : r ∈ preserved) : s₅.gpr r = s.gpr r := by
    obtain ⟨h3, h4, h5, h6, h7, -⟩ := preserved_ne hr
    rw [u₅.other _ h7, u₄.other _ h6, u₃.other _ h5, u₂.other _ h4, u₁.other _ h3]
  refine ⟨callPreIv hp ?_ ?_ ?_ ?_ ?_ ?_ ?_, keep, ?_, ?_, ?_⟩
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.gpr, h.r14]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr,
      u₁.other _ (by decide), h.r15]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), h.r16]
  · rw [u₅.other _ (by decide), u₄.gpr]
  · rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), h.r19]
  · rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd]
  · rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr]
  · rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  · rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]

theorem body_ok : BodyOk ofbMode body := by
  intro s₀ hp k hk s h
  refine WP.seq (WP.mono (ivA_wp hp h) fun s₁ a => ?_)
  refine WP.seq (WP.mono (blk_call Proof.Aes.PPC64LE.encryptBlocks_correct encryptBlocks_noFrames a.pre)
    fun s₂ c => ?_)
  have g₂ (r : Reg) (hr : r ∈ preserved) : s₂.gpr r = s.gpr r := by rw [c.saved r hr, a.saved r hr]
  have hW₂ : s₂.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [c.wr, a.wr, h.wrs hp]
  have hR₂ : s₂.rd ++ s₂.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by
    rw [c.rd, c.wr, a.rd, a.wr, h.regs hp]
  refine xorInto_wp (P := blk s₀ k) (Q := Iv s₀) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [g₂ .r17 (by decide), h.r17]) (by rw [g₂ .r16 (by decide), h.r16])
    (by rw [hR₂]; exact in_rw (by simp) (hp.cBlk0 hk)) (by rw [hR₂]; exact in_rw (by simp) (hp.cBlk8 hk))
    (by rw [hR₂]; exact in_rw (by simp) cIv0) (by rw [hR₂]; exact in_rw (by simp) cIv8)
    (by rw [hW₂]; exact in_rw (by simp) (hp.cBlk0 hk)) (by rw [hW₂]; exact in_rw (by simp) (hp.cBlk8 hk))
    fun s₃ g₃ mem₃ rd₃ wr₃ => advance_regs (s := s₃) hk
      (by rw [g₃ _ (by decide) (by decide), g₂ .r17 (by decide), h.r17])
      (by rw [g₃ _ (by decide) (by decide), g₂ .r18 (by decide), h.r18])
      fun s₄ r17₄ r18₄ keep₄ mem₄ rd₄ wr₄ => ?_
  have g (r : Reg) (hr : r ∈ preserved) (h17 : r ≠ .r17) (h18 : r ≠ .r18) : s₄.gpr r = s.gpr r := by
    obtain ⟨-, -, -, -, -, h9, h10⟩ := preserved_ne hr
    rw [keep₄ r h17 h18, g₃ r h9 h10, g₂ r hr]
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
        rcases hr with rfl | rfl
        · exact hp.blk_iv hk
        · exact (hp.data_scr.sub_left (UPre.data_sub hk)).sub_right (Region.sub_prefix (by decide)))
        (by decide),
      bytesAt_frame (xorMem_frame s₂.mem (blk s₀ k) (Iv s₀)) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (hp.blk_iv hk).symm) (by decide)]
  have hl : ((blks s₀).take k).length = k := by simp [Spec.Cbc.blocksAt]; omega
  have outSucc : outK ofbMode s₀ (k + 1) = outK ofbMode s₀ k ++ [bytesAt s₄.mem (blk s₀ k) 16] := by
    rw [newBlk, newIv]
    simp only [outK, chainK, ofbMode_out, ofbMode_chain, take_succ_blks s₀ hk, AesOfb.crypt_snoc, hl]
  have hl' : (outK ofbMode s₀ k).length = k := by rw [outK, Mode.length_out, hl]
  refine ⟨?_, ?_, ?_, r17₄, r18₄, ?_, fun r hr hv => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [g .r14 (by decide) (by decide) (by decide), h.r14]
  · rw [g .r15 (by decide) (by decide) (by decide), h.r15]
  · rw [g .r16 (by decide) (by decide) (by decide), h.r16]
  · rw [g .r19 (by decide) (by decide) (by decide), h.r19]
  · rw [g r hr (fun e => hv (by simp [e])) (fun e => hv (by simp [e])), h.keep r hr hv]
  · rw [rd₄, rd₃, c.rd, a.rd, h.rd]
  · rw [wr₄, wr₃, c.wr, a.wr, h.wr]
  · exact h.frame.trans (stepFrame hk fStep)
  · rw [hp.blocksAt_step hk fStep, h.data, outSucc,
      set_prefix _ _ _ hl' (by simp [Spec.Cbc.blocksAt]; exact hk)]
  · rw [newIv]
    simp only [chainK, ofbMode_chain, take_succ_blks s₀ hk, List.length_append, List.length_singleton, hl,
      AesOfb.next_succ]

/-! ## Constant time -/

theorem pre_taint : ∃ h, (taint.check (Taint.ofRegs vars) (.block ivArgs) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem post_taint : ∃ h, (taint.check (Taint.ofRegs [.r16, .r17, .r18, .r19])
    (.block (xorInto .r17 .r16 ++ advance)) h).isSome = true := ⟨_, by taint_decide⟩

theorem body_ct : BodyCt ofbMode body :=
  fun hp hp' hq k => VG.Proof.AesCbc.PPC64LE.body_ct (m := fun _ _ s => s.mem) (D := fun s₀ _ => Iv s₀)
    (fun hq _ => pub_Iv hq) Proof.Aes.PPC64LE.encryptBlocks_correct Proof.Aes.PPC64LE.encryptBlocks_ct
    encryptBlocks_noFrames pre_taint post_taint (@fun _ hp _ _ _ h => ivA_wp hp h) hp hp' hq k

end VG.Proof.AesOfb.PPC64LE
