module

public import VerifiedGarbage.Proof.AesXts.RISCV64.Steps
public import VerifiedGarbage.Proof.AesXts.Spec
public import VerifiedGarbage.Proof.AesCbc.RISCV64.CT
import VerifiedGarbage.Proof.AesCbc.RISCV64.Body
import VerifiedGarbage.Proof.AesCbc.RISCV64.Lit
import VerifiedGarbage.Proof.Aes.RISCV64.BlocksVerified
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.AesXts.RISCV64.Steps
meta import VerifiedGarbage.Proof.AesXts.Spec
meta import VerifiedGarbage.Proof.AesCbc.RISCV64.CT
meta import VerifiedGarbage.Proof.AesCbc.RISCV64.Body
meta import VerifiedGarbage.Proof.Aes.RISCV64.BlocksVerified
public import VerifiedGarbage.Impl.AesXts.RISCV64
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.Aes

/-!
# XTS-AES on RISC-V: one block

As on PPC64LE (`Proof/AesXts/PPC64LE/Body.lean`): `body_ok`, one block takes
AES-CBC's loop invariant (`Proof/AesCbc/RISCV64/Loop.lean`) from `k` to
`k + 1` blocks, for `xtsMode enc`, by the block function in that direction:
the tweak XORed into the block, the call, the tweak XORed in again, and the
tweak times `α` (`mulA_wp`). `encBody_ct`, `decBody_ct`: it is constant
time, by AES-CBC's `body_ct`, whose code before the call is the same as
encryption's (`encA_wp`).
-/

@[expose] public section

namespace VG.Proof.AesXts.RISCV64

open VG VG.RISCV64 VG.Impl.AesXts.RISCV64
open VG.Impl.AesCbc.RISCV64 (xorInto callArgs advance encCall decCall)
open VG.Proof.AesCbc (aesWith_state aesInvWith_state set_prefix Mode ciphOf)
open VG.Proof.AesCbc.RISCV64
open VG.Spec.Aes (bytesAt)

theorem preserved_mul : ∀ r ∈ preserved, r ∉ mulRegs := by decide

/-- One block in the direction `enc`, by the block function `f`, which
computes `ciphOf enc` on bytes. -/
theorem body_ok (enc : Bool) {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {name : String}
    {c : Prog isa}
    (ok : ∀ s, (Proof.Aes.blocksRISCV64 f).pre s →
      ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksRISCV64 f).post s s')
    (nf : c.noFrames = true)
    (hf : ∀ R w m p, (f R w (Spec.Aes.stateAt m p)).toList = ciphOf enc R w (bytesAt m p 16)) :
    BodyOk (AesXts.xtsMode enc) (.seq (.block pre) (.seq (.call name c) (.block post))) := by
  intro s₀ hp k hk s h
  refine WP.seq (xorInto_wp (P := blk s₀ k) (Q := Iv s₀) (by decide) (by decide) (by decide) (by decide)
    h.s4 h.s3 (h.rIv hp) (h.wBlk hp hk) (hp.blk_iv hk) fun s₁ g₁ x₁ f₁ rd₁ wr₁ sp₁ =>
      WP.mono (callArgs_pre hp hk h (fun r hr => g₁ r (preserved_ne hr).2.2.1 (preserved_ne hr).2.2.2)
        rfl rd₁ wr₁ sp₁) fun s₂ a => ?_)
  refine WP.seq (WP.mono (blk_call (name := name) ok nf a.pre) fun s₃ c => ?_)
  have g₃ (r : Reg) (hr : r ∈ preserved) : s₃.gpr r = s.gpr r := by rw [c.saved r hr, a.saved r hr]
  have hW₃ : s₃.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [c.wr, a.wr, h.wrs hp]
  have hR₃ : s₃.rd ++ s₃.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by
    rw [c.rd, c.wr, a.rd, a.wr, h.regs hp]
  rw [post, List.append_assoc]
  refine xorInto_wp (P := blk s₀ k) (Q := Iv s₀) (by decide) (by decide) (by decide) (by decide)
    (by rw [g₃ .s4 (by decide), h.s4]) (by rw [g₃ .s3 (by decide), h.s3])
    ⟨ivR s₀, by rw [hR₃]; simp, fun _ h => h⟩ ⟨dataR s₀, by rw [hW₃]; simp, UPre.data_sub hk⟩
    (hp.blk_iv hk) fun s₄ g₄ x₄ f₄ rd₄ wr₄ sp₄ => ?_
  have g₄' (r : Reg) (hr : r ∈ preserved) : s₄.gpr r = s.gpr r := by
    rw [g₄ r (preserved_ne hr).2.2.1 (preserved_ne hr).2.2.2, g₃ r hr]
  refine mulA_wp (Q := Iv s₀) (by rw [g₄' .s3 (by decide), h.s3])
    (in_words (by rw [rd₄, wr₄, hR₃]; simp)) (in_words (by rw [wr₄, hW₃]; simp))
    fun s₅ g₅ b₅ f₅ rd₅ wr₅ sp₅ => ?_
  refine advance_regs (s := s₅) hk (by rw [g₅ _ (by decide), g₄' .s4 (by decide), h.s4])
    (by rw [g₅ _ (by decide), g₄' .s5 (by decide), h.s5]) fun s₆ s4₆ s5₆ keep₆ mem₆ rd₆ wr₆ sp₆ => ?_
  have g (r : Reg) (hr : r ∈ preserved) (h4 : r ≠ .s4) (h5 : r ≠ .s5) : s₆.gpr r = s.gpr r := by
    rw [keep₆ r h4 h5, g₅ r (preserved_mul r hr), g₄' r hr]
  -- Memory.
  have fc : Frame [⟨blk s₀ k, 16⟩, ⟨S s₀, 2048⟩] s₁.mem s₃.mem := by
    have := c.frame; rwa [a.mem] at this
  have fStep : Frame [⟨blk s₀ k, 16⟩, ivR s₀, wsR s₀, cR s₀] s.mem s₆.mem := by
    rw [mem₆]
    exact (f₁.mono (by simp)).trans ((callFrame fc).trans ((f₄.mono (by simp)).trans (f₅.mono (by simp))))
  have big₂ : Frame (Big s₀) s₀.mem s₂.mem := by
    rw [a.mem]
    exact (UPre.big_of h.frame).trans (f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨dataR s₀, by simp, UPre.data_sub hk⟩)
  have hlt : ((blks s₀).take k).length = k := by simp [Spec.Cbc.blocksAt]; omega
  -- The tweak on entry to the block, the new block, and the new tweak.
  have ivIn : bytesAt s₃.mem (Iv s₀) 16 = chainK (AesXts.xtsMode enc) s₀ k := by
    rw [bytesAt_frame fc (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact (hp.blk_iv hk).symm
        · exact hp.iv_scr.sub_right wsR_sub) (by decide),
      bytesAt_frame f₁ (one (hp.blk_iv hk).symm) (by decide), h.iv]
  have newBlk : bytesAt s₆.mem (blk s₀ k) 16 =
      Spec.Xts.block (ciphOf enc (R s₀) (wK s₀)) (Spec.Xts.next (iv0 s₀) k)
        ((blks s₀)[k]'(by simp [Spec.Cbc.blocksAt]; exact hk)) := by
    rw [mem₆, bytesAt_frame f₅ (one (hp.blk_iv hk)) (by decide), x₄, ivIn, c.out, hf, UPre.sched_bytes hp big₂,
      a.mem, x₁, h.block hk, h.iv]
    simp only [chainK, AesXts.xtsMode_chain, hlt]
    rfl
  have newIv : bytesAt s₆.mem (Iv s₀) 16 = Spec.Xts.mulAlpha (chainK (AesXts.xtsMode enc) s₀ k) := by
    rw [mem₆, b₅, bytesAt_frame f₄ (one (hp.blk_iv hk).symm) (by decide), ivIn]
  have hl : (outK (AesXts.xtsMode enc) s₀ k).length = k := by
    rw [outK, Mode.length_out]; simp [Spec.Cbc.blocksAt]; omega
  have outSucc :
      outK (AesXts.xtsMode enc) s₀ (k + 1) = outK (AesXts.xtsMode enc) s₀ k ++ [bytesAt s₆.mem (blk s₀ k) 16] := by
    rw [newBlk]
    simp only [outK, AesXts.xtsMode_out, take_succ_blks s₀ hk, AesXts.crypt_snoc, hlt]
  refine ⟨?_, ?_, ?_, s4₆, s5₆, ?_, fun r hr hv => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [g .s1 (by decide) (by decide) (by decide), h.s1]
  · rw [g .s2 (by decide) (by decide) (by decide), h.s2]
  · rw [g .s3 (by decide) (by decide) (by decide), h.s3]
  · rw [g .s6 (by decide) (by decide) (by decide), h.s6]
  · rw [g r hr (fun e => hv (by simp [e])) (fun e => hv (by simp [e])), h.keep r hr hv]
  · rw [rd₆, rd₅, rd₄, c.rd, a.rd, h.rd]
  · rw [wr₆, wr₅, wr₄, c.wr, a.wr, h.wr]
  · rw [sp₆, sp₅, sp₄, c.sp, a.sp, h.sp]
  · exact h.frame.trans (stepFrame hk fStep)
  · rw [hp.blocksAt_step hk fStep, h.data, outSucc,
      set_prefix _ _ _ hl (by simp [Spec.Cbc.blocksAt]; exact hk)]
  · rw [newIv]
    simp only [chainK, AesXts.xtsMode_chain, take_succ_blks s₀ hk, List.length_append, List.length_singleton,
      hlt, AesXts.next_succ]

theorem encBody_ok : BodyOk (AesXts.xtsMode true) encBody :=
  body_ok true Proof.Aes.RISCV64.encryptBlocks_correct encryptBlocks_noFrames
    fun _ _ _ _ => (aesWith_state _ _ _ _).symm

theorem decBody_ok : BodyOk (AesXts.xtsMode false) decBody :=
  body_ok false Proof.Aes.RISCV64.decryptBlocks_correct decryptBlocks_noFrames
    fun _ _ _ _ => (aesInvWith_state _ _ _ _).symm

/-! ## Constant time -/

theorem post_taint : ∃ h, (taint.check (Taint.ofRegs [.s3, .s4, .s5, .s6]) (.block post) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem encBody_ct : BodyCt (AesXts.xtsMode true) encBody :=
  fun hp hp' hq k => body_ct (fun hq k => pub_blk hq k)
    Proof.Aes.RISCV64.encryptBlocks_correct Proof.Aes.RISCV64.encryptBlocks_ct encryptBlocks_noFrames
    encPre_taint post_taint (@fun _ hp _ hk _ h => encA_wp hp hk h) hp hp' hq k

theorem decBody_ct : BodyCt (AesXts.xtsMode false) decBody :=
  fun hp hp' hq k => body_ct (fun hq k => pub_blk hq k)
    Proof.Aes.RISCV64.decryptBlocks_correct Proof.Aes.RISCV64.decryptBlocks_ct decryptBlocks_noFrames
    encPre_taint post_taint (@fun _ hp _ hk _ h => encA_wp hp hk h) hp hp' hq k

end VG.Proof.AesXts.RISCV64
