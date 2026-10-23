module

import VerifiedGarbage.Proof.AesXts.PPC64LE.Steps
public import VerifiedGarbage.Proof.AesXts.Spec
public import VerifiedGarbage.Proof.AesCbc.PPC64LE.CT
meta import VerifiedGarbage.Proof.AesXts.PPC64LE.Steps
meta import VerifiedGarbage.Proof.AesXts.Spec
meta import VerifiedGarbage.Proof.AesCbc.PPC64LE.CT
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.AesXts.PPC64LE
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.Aes

/-!
# XTS-AES on PPC64LE: one block

`body_ok`: one block takes AES-CBC's loop invariant (`Proof/AesCbc/PPC64LE/Loop.lean`)
from `k` to `k + 1` blocks, for `xtsMode enc`, by the block function in that
direction: the tweak XORed into the block (`preA_wp`), the call, the tweak
XORed in again, and the tweak times `α` (`mulA_wp`). `body_ct`: it is
constant time, by AES-CBC's `body_ct`.
-/

@[expose] public section

namespace VG.Proof.AesXts.PPC64LE

open VG VG.PPC64LE VG.Impl.AesXts.PPC64LE
open VG.Impl.AesCbc.PPC64LE (xorInto callArgs advance encCall decCall)
open VG.Proof.AesCbc (xorMem xorMem_frame xorMem_bytes aesWith_state aesInvWith_state set_prefix Mode ciphOf)
open VG.Proof.AesCbc.PPC64LE
open VG.Spec.Aes (bytesAt)

theorem one {r : Region} {P : Addr} (hd : (⟨P, 16⟩ : Region).Disjoint r) :
    ∀ r' ∈ [r], (⟨P, 16⟩ : Region).Disjoint r' := fun r' hr' => by
  simp only [List.mem_singleton] at hr'; subst hr'; exact hd

theorem preserved_ne' {r : Reg} (hr : r ∈ preserved) : r ≠ .r9 ∧ r ≠ .r10 ∧ r ≠ .r11 ∧ r ≠ .r12 := by
  revert hr; cases r <;> decide

/-- The tweak XORed into block `k`, and the arguments of the call. -/
theorem preA_wp {M : Mode} {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀)
    {s : State} (h : LInv M s₀ k s) :
    WP isa (.block pre) s (Pre s₀ (blk s₀ k) (xorMem s.mem (blk s₀ k) (Iv s₀)) s) := by
  have hR := h.regs hp
  have hW := h.wrs hp
  refine xorInto_wp (P := blk s₀ k) (Q := Iv s₀) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) h.r17 h.r16
    (by rw [hR]; exact in_rw (by simp) (hp.cBlk0 hk)) (by rw [hR]; exact in_rw (by simp) (hp.cBlk8 hk))
    (by rw [hR]; exact in_rw (by simp) cIv0) (by rw [hR]; exact in_rw (by simp) cIv8)
    (by rw [hW]; exact in_rw (by simp) (hp.cBlk0 hk)) (by rw [hW]; exact in_rw (by simp) (hp.cBlk8 hk))
    fun s₁ g₁ mem₁ rd₁ wr₁ => callArgs_pre hp hk h (fun r hr => by
      obtain ⟨-, -, -, -, -, h9, h10⟩ := preserved_ne hr
      exact g₁ r h9 h10) mem₁ rd₁ wr₁

/-- One block in the direction `enc`, by the block function `f`, which
computes `ciphOf enc` on bytes. -/
theorem body_ok (enc : Bool) {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {name : String}
    {c : Prog isa}
    (ok : ∀ s, (Proof.Aes.blocksPPC64LE f).pre s →
      ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksPPC64LE f).post s s')
    (nf : c.noFrames = true)
    (hf : ∀ R w m p, (f R w (Spec.Aes.stateAt m p)).toList = ciphOf enc R w (bytesAt m p 16)) :
    BodyOk (AesXts.xtsMode enc) (.seq (.block pre) (.seq (.call name c) (.block post))) := by
  intro s₀ hp k hk s h
  refine WP.seq (WP.mono (preA_wp hp hk h) fun s₁ a => ?_)
  refine WP.seq (WP.mono (blk_call (name := name) ok nf a.pre) fun s₂ c => ?_)
  have g₂ (r : Reg) (hr : r ∈ preserved) : s₂.gpr r = s.gpr r := by rw [c.saved r hr, a.saved r hr]
  have hW₂ : s₂.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [c.wr, a.wr, h.wrs hp]
  have hR₂ : s₂.rd ++ s₂.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by
    rw [c.rd, c.wr, a.rd, a.wr, h.regs hp]
  rw [post, List.append_assoc]
  refine xorInto_wp (P := blk s₀ k) (Q := Iv s₀) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [g₂ .r17 (by decide), h.r17]) (by rw [g₂ .r16 (by decide), h.r16])
    (by rw [hR₂]; exact in_rw (by simp) (hp.cBlk0 hk)) (by rw [hR₂]; exact in_rw (by simp) (hp.cBlk8 hk))
    (by rw [hR₂]; exact in_rw (by simp) cIv0) (by rw [hR₂]; exact in_rw (by simp) cIv8)
    (by rw [hW₂]; exact in_rw (by simp) (hp.cBlk0 hk)) (by rw [hW₂]; exact in_rw (by simp) (hp.cBlk8 hk))
    fun s₃ g₃ mem₃ rd₃ wr₃ => ?_
  have g₃' (r : Reg) (hr : r ∈ preserved) : s₃.gpr r = s.gpr r := by
    obtain ⟨-, -, -, -, -, h9, h10⟩ := preserved_ne hr
    rw [g₃ r h9 h10, g₂ r hr]
  have hR₃ : s₃.rd ++ s₃.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by rw [rd₃, wr₃, hR₂]
  have hW₃ : s₃.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [wr₃, hW₂]
  refine mulA_wp (Q := Iv s₀) (by rw [g₃' .r16 (by decide), h.r16])
    (by rw [hR₃]; exact in_rw (by simp) cIv0) (by rw [hR₃]; exact in_rw (by simp) cIv8)
    (by rw [hW₃]; exact in_rw (by simp) cIv0) (by rw [hW₃]; exact in_rw (by simp) cIv8)
    fun s₄ g₄ mem₄ rd₄ wr₄ => advance_regs (s := s₄) hk
      (by rw [g₄ _ (by decide) (by decide) (by decide) (by decide), g₃' .r17 (by decide), h.r17])
      (by rw [g₄ _ (by decide) (by decide) (by decide) (by decide), g₃' .r18 (by decide), h.r18])
      fun s₅ r17₅ r18₅ keep₅ mem₅ rd₅ wr₅ => ?_
  have g (r : Reg) (hr : r ∈ preserved) (h17 : r ≠ .r17) (h18 : r ≠ .r18) : s₅.gpr r = s.gpr r := by
    obtain ⟨h9, h10, h11, h12⟩ := preserved_ne' hr
    rw [keep₅ r h17 h18, g₄ r h9 h10 h11 h12, g₃' r hr]
  -- Memory.
  have f₁ : Frame [⟨blk s₀ k, 16⟩] s.mem s₁.mem := by rw [a.mem]; exact xorMem_frame _ _ _
  have f₃ : Frame [⟨blk s₀ k, 16⟩] s₂.mem s₃.mem := by rw [mem₃]; exact xorMem_frame _ _ _
  have f₄ : Frame [ivR s₀] s₃.mem s₄.mem := by rw [mem₄]; exact alphaMem_frame _ _
  have fStep : Frame [⟨blk s₀ k, 16⟩, ivR s₀, ⟨S s₀, 2064⟩] s.mem s₅.mem := by
    rw [mem₅]
    refine (f₁.sub fun r hr => ?_).trans ((c.frame.sub fun r hr => ?_).trans
      ((f₃.sub fun r hr => ?_).trans (f₄.sub fun r hr => ?_)))
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨⟨S s₀, 2064⟩, by simp, Region.sub_prefix (by decide)⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
  have big₁ : Frame (Big s₀) s₀.mem s₁.mem :=
    (UPre.big_of h.frame).trans ((stepFrame hk (f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩)).sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨ivR s₀, by simp, fun _ h => h⟩
      · exact ⟨dataR s₀, by simp, fun _ h => h⟩
      · exact ⟨scrR s₀, by simp, Region.sub_prefix (by decide)⟩)
  have callIv : ∀ r ∈ [⟨blk s₀ k, 16⟩, ⟨S s₀, 2048⟩], (ivR s₀).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (hp.blk_iv hk).symm
    · exact hp.iv_scr.sub_right (Region.sub_prefix (by decide))
  have hlt : ((blks s₀).take k).length = k := by simp [Spec.Cbc.blocksAt]; omega
  -- The tweak on entry to the block, the new block, and the new tweak.
  have ivIn : bytesAt s₂.mem (Iv s₀) 16 = chainK (AesXts.xtsMode enc) s₀ k := by
    rw [bytesAt_frame c.frame callIv (by decide), a.mem,
      bytesAt_frame (xorMem_frame _ _ _) (one (hp.blk_iv hk).symm) (by decide), h.iv]
  have newBlk : bytesAt s₅.mem (blk s₀ k) 16 =
      Spec.Xts.block (ciphOf enc (R s₀) (wK s₀)) (Spec.Xts.next (iv0 s₀) k)
        ((blks s₀)[k]'(by simp [Spec.Cbc.blocksAt]; exact hk)) := by
    rw [mem₅, mem₄, bytesAt_frame (alphaMem_frame _ _) (one (hp.blk_iv hk)) (by decide), mem₃,
      xorMem_bytes _ (hp.blk_iv hk), ivIn, c.out, hf, UPre.sched_bytes hp big₁, a.mem,
      xorMem_bytes _ (hp.blk_iv hk), h.block hk, h.iv]
    simp only [chainK, AesXts.xtsMode_chain, hlt]
    rfl
  have newIv : bytesAt s₅.mem (Iv s₀) 16 = Spec.Xts.mulAlpha (chainK (AesXts.xtsMode enc) s₀ k) := by
    rw [mem₅, mem₄, alphaMem_bytes, mem₃,
      bytesAt_frame (xorMem_frame _ _ _) (one (hp.blk_iv hk).symm) (by decide), ivIn]
  have hl : (outK (AesXts.xtsMode enc) s₀ k).length = k := by
    rw [outK, Mode.length_out]; simp [Spec.Cbc.blocksAt]; omega
  have outSucc :
      outK (AesXts.xtsMode enc) s₀ (k + 1) = outK (AesXts.xtsMode enc) s₀ k ++ [bytesAt s₅.mem (blk s₀ k) 16] := by
    rw [newBlk]
    simp only [outK, AesXts.xtsMode_out, take_succ_blks s₀ hk, AesXts.crypt_snoc, hlt]
  refine ⟨?_, ?_, ?_, r17₅, r18₅, ?_, fun r hr hv => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [g .r14 (by decide) (by decide) (by decide), h.r14]
  · rw [g .r15 (by decide) (by decide) (by decide), h.r15]
  · rw [g .r16 (by decide) (by decide) (by decide), h.r16]
  · rw [g .r19 (by decide) (by decide) (by decide), h.r19]
  · rw [g r hr (fun e => hv (by simp [e])) (fun e => hv (by simp [e])), h.keep r hr hv]
  · rw [rd₅, rd₄, rd₃, c.rd, a.rd, h.rd]
  · rw [wr₅, wr₄, wr₃, c.wr, a.wr, h.wr]
  · exact h.frame.trans (stepFrame hk fStep)
  · rw [hp.blocksAt_step hk fStep, h.data, outSucc,
      set_prefix _ _ _ hl (by simp [Spec.Cbc.blocksAt]; exact hk)]
  · rw [newIv]
    simp only [chainK, AesXts.xtsMode_chain, take_succ_blks s₀ hk, List.length_append, List.length_singleton,
      hlt, AesXts.next_succ]

theorem encBody_ok : BodyOk (AesXts.xtsMode true) encBody :=
  body_ok true Proof.Aes.PPC64LE.encryptBlocks_correct encryptBlocks_noFrames
    fun _ _ _ _ => (aesWith_state _ _ _ _).symm

theorem decBody_ok : BodyOk (AesXts.xtsMode false) decBody :=
  body_ok false Proof.Aes.PPC64LE.decryptBlocks_correct decryptBlocks_noFrames
    fun _ _ _ _ => (aesInvWith_state _ _ _ _).symm

/-! ## Constant time -/

theorem pre_taint : ∃ h, (taint.check (Taint.ofRegs vars) (.block pre) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem post_taint : ∃ h, (taint.check (Taint.ofRegs [.r16, .r17, .r18, .r19]) (.block post) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem encBody_ct : BodyCt (AesXts.xtsMode true) encBody :=
  fun hp hp' hq k => body_ct (m := fun s₀ k s => xorMem s.mem (blk s₀ k) (Iv s₀)) (fun hq k => pub_blk hq k)
    Proof.Aes.PPC64LE.encryptBlocks_correct Proof.Aes.PPC64LE.encryptBlocks_ct encryptBlocks_noFrames
    pre_taint post_taint (@fun _ hp _ hk _ h => preA_wp hp hk h) hp hp' hq k

theorem decBody_ct : BodyCt (AesXts.xtsMode false) decBody :=
  fun hp hp' hq k => body_ct (m := fun s₀ k s => xorMem s.mem (blk s₀ k) (Iv s₀)) (fun hq k => pub_blk hq k)
    Proof.Aes.PPC64LE.decryptBlocks_correct Proof.Aes.PPC64LE.decryptBlocks_ct decryptBlocks_noFrames
    pre_taint post_taint (@fun _ hp _ hk _ h => preA_wp hp hk h) hp hp' hq k

end VG.Proof.AesXts.PPC64LE
