import VerifiedGarbage.Proof.AesXts.AArch64.Steps
import VerifiedGarbage.Proof.AesCbc.AArch64.CT

/-!
# XTS-AES on AArch64: one block, and constant time

`body_ok'`: one run of `body` takes the loop invariant AES-CBC's proofs
share (`Proof/AesCbc/AArch64/Loop.lean`) from `k` blocks to `k + 1`, for
`xtsMode enc`, for any implementation of the block functions
(`BlocksImpl`), with `vg_aes_encrypt_blocks` for encryption and
`vg_aes_decrypt_blocks` for decryption. The tweak is XORed into the data
block (`preA_wp`), which is enciphered in place, the tweak is XORed in
again, and the tweak is multiplied by `α` (`Steps.lean`). `encBody_ct` and
`decBody_ct`: they are constant time, by the shared framework, with the call
on the data block.
-/

namespace VG.Proof.AesXts.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesXts.AArch64
open VG.Impl.AesCbc.AArch64 (xorInto callArgs advance whole)
open VG.Proof.AesCbc (xorMem xorMem_frame xorMem_bytes aesWith_state aesInvWith_state set_prefix Mode ciphOf)
open VG.Proof.AesCbc.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.AArch64 (BlocksImpl)

/-- What the code before the call leaves. -/
structure PreA (s₀ : State) (k : Nat) (s s₁ : State) : Prop where
  pre : CallPre s₁ (W s₀) (blk s₀ k) (S s₀) (R s₀)
  saved : ∀ r ∈ preserved, s₁.gpr r = s.gpr r
  sp : s₁.sp = s.sp
  mem : s₁.mem = xorMem s.mem (blk s₀ k) (Iv s₀)
  rd : s₁.rd = s.rd
  wr : s₁.wr = s.wr

theorem preA_wp {M : Mode} {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀)
    {s : State} (h : LInv M s₀ k s) :
    WP isa (.block (xorInto ++ callArgs)) s (PreA s₀ k s) := by
  have hR := h.regs hp
  have hW := h.wrs hp
  obtain ⟨s₁, run₁, g₁, sp₁, mem₁, rd₁, wr₁⟩ :=
    xorInto_ok s (P := blk s₀ k) (Q := Iv s₀) h.x22 h.x21
      (by rw [hR]; exact in_rw (by simp) (hp.cBlk0 hk)) (by rw [hR]; exact in_rw (by simp) (hp.cBlk8 hk))
      (by rw [hR]; exact in_rw (by simp) cIv0) (by rw [hR]; exact in_rw (by simp) cIv8)
      (by rw [hW]; exact in_rw (by simp) (hp.cBlk0 hk)) (by rw [hW]; exact in_rw (by simp) (hp.cBlk8 hk))
  obtain ⟨s₂, run₂, x0₂, x1₂, x2₂, x3₂, x4₂, cs₂, sp₂, mem₂, rd₂, wr₂⟩ := callArgs_ok s₁
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨s₁, run₁, WP.of_runBlock ⟨s₂, run₂, ?_⟩⟩
  have keep (r : Reg) (hr : r ∈ preserved) : s₂.gpr r = s.gpr r := by
    rw [cs₂ r hr, g₁ r (preserved_ne hr).1 (preserved_ne hr).2]
  exact ⟨hp.callPre hk (by rw [x0₂, g₁ _ (by decide) (by decide), h.x19])
    (by rw [x1₂, g₁ _ (by decide) (by decide), h.x20])
    (by rw [x2₂, g₁ _ (by decide) (by decide), h.x22]) x3₂
    (by rw [x4₂, g₁ _ (by decide) (by decide), h.x24]) (by rw [rd₂, rd₁, h.rd]) (by rw [wr₂, wr₁, h.wr]),
    keep, by rw [sp₂, sp₁], by rw [mem₂, mem₁], by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩

theorem preserved_ne' {r : Reg} (hr : r ∈ preserved) : r ≠ .x11 ∧ r ≠ .x12 := by
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- One block in the direction `enc`, by a block function `b` computing `f`,
which is `ciphOf enc` on bytes. -/
theorem body_ok' (enc : Bool) {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State}
    {b : Impl.Aes.AArch64.Blocks}
    (ok : ∀ s, (Proof.Aes.blocksAArch64 f).pre s →
      ∃ t s', Exec isa b.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksAArch64 f).post s s')
    (nf : b.code.noFrames = true)
    (hf : ∀ R w m p, (f R w (Spec.Aes.stateAt m p)).toList = ciphOf enc R w (bytesAt m p 16)) :
    BodyOk (AesXts.xtsMode enc) (body b) := by
  intro s₀ hp k hk s h
  refine WP.seq (WP.mono (preA_wp hp hk h) fun s₁ a => ?_)
  refine WP.seq (WP.mono (blk_call ok nf a.pre) fun s₂ c => ?_)
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
  have g₃' (r : Reg) (hr : r ∈ preserved) (h30 : r ≠ .x30) : s₃.gpr r = s.gpr r := by
    rw [g₃ r (preserved_ne hr).1 (preserved_ne hr).2, g₂ r hr h30]
  have hR₃ : s₃.rd ++ s₃.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by rw [rd₃, wr₃, hR₂]
  have hW₃ : s₃.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [wr₃, hW₂]
  obtain ⟨s₄, run₄, g₄, sp₄, mem₄, rd₄, wr₄⟩ :=
    mulA_ok s₃ (Q := Iv s₀) (by rw [g₃' .x21 (by simp [preserved]) (by decide), h.x21])
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
  have one (r : Region) (P : Addr) (hd : (⟨P, 16⟩ : Region).Disjoint r) :
      ∀ r' ∈ [r], (⟨P, 16⟩ : Region).Disjoint r' := fun r' hr' => by
    simp only [List.mem_singleton] at hr'; subst hr'; exact hd
  have callIv : ∀ r ∈ [⟨blk s₀ k, 16⟩, ⟨S s₀, 2048⟩], (ivR s₀).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (hp.blk_iv hk).symm
    · exact hp.iv_scr.sub_right (Region.sub_prefix (by decide))
  have hlt : ((blks s₀).take k).length = k := by simp [Spec.Cbc.blocksAt]; omega
  have ivIn : bytesAt s₂.mem (Iv s₀) 16 = chainK (AesXts.xtsMode enc) s₀ k := by
    rw [Proof.Cmac.bytesAt_frame c.frame callIv (by decide), a.mem,
      Proof.Cmac.bytesAt_frame (xorMem_frame _ _ _) (one _ _ (hp.blk_iv hk).symm) (by decide), h.iv]
  have newBlk : bytesAt s₅.mem (blk s₀ k) 16 =
      Spec.Xts.block (ciphOf enc (R s₀) (wK s₀)) (Spec.Xts.next (iv0 s₀) k)
        ((blks s₀)[k]'(by simp [Spec.Cbc.blocksAt]; exact hk)) := by
    rw [mem₅, mem₄, Proof.Cmac.bytesAt_frame (alphaMem_frame _ _) (one _ _ (hp.blk_iv hk)) (by decide), mem₃,
      xorMem_bytes _ (hp.blk_iv hk), ivIn, c.out, hf, UPre.sched_bytes hp big₁, a.mem,
      xorMem_bytes _ (hp.blk_iv hk), h.block hk, h.iv]
    simp only [chainK, AesXts.xtsMode_chain, hlt]
    rfl
  have newIv : bytesAt s₅.mem (Iv s₀) 16 = Spec.Xts.mulAlpha (chainK (AesXts.xtsMode enc) s₀ k) := by
    rw [mem₅, mem₄, alphaMem_bytes, mem₃,
      Proof.Cmac.bytesAt_frame (xorMem_frame _ _ _) (one _ _ (hp.blk_iv hk).symm) (by decide), ivIn]
  have hl : (outK (AesXts.xtsMode enc) s₀ k).length = k := by
    rw [outK, Mode.length_out]; simp [Spec.Cbc.blocksAt]; omega
  have outSucc :
      outK (AesXts.xtsMode enc) s₀ (k + 1) = outK (AesXts.xtsMode enc) s₀ k ++ [bytesAt s₅.mem (blk s₀ k) 16] := by
    rw [newBlk]
    simp only [outK, AesXts.xtsMode_out, take_succ_blks s₀ hk, AesXts.crypt_snoc, hlt]
  obtain ⟨x19', x20', x21', x24', other'⟩ := h.next g
  refine ⟨x19', x20', x21', x22₅, x23₅, x24', other', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [sp₅, sp₄, sp₃, c.sp, a.sp, h.sp]
  · rw [rd₅, rd₄, rd₃, c.rd, a.rd, h.rd]
  · rw [wr₅, wr₄, wr₃, c.wr, a.wr, h.wr]
  · exact h.frame.trans (stepFrame hk fStep)
  · rw [hp.blocksAt_step hk fStep, h.data, outSucc,
      set_prefix _ _ _ hl (by simp [Spec.Cbc.blocksAt]; exact hk)]
  · rw [newIv]
    simp only [chainK, AesXts.xtsMode_chain, take_succ_blks s₀ hk, List.length_append, List.length_singleton,
      hlt, AesXts.next_succ]

theorem encBody_ok (v : BlocksImpl) : BodyOk (AesXts.xtsMode true) (body v.enc) :=
  body_ok' true v.encOk v.encNoFrames fun _ _ _ _ => (aesWith_state _ _ _ _).symm

theorem decBody_ok (v : BlocksImpl) : BodyOk (AesXts.xtsMode false) (body v.dec) :=
  body_ok' false v.decOk v.decNoFrames fun _ _ _ _ => (aesInvWith_state _ _ _ _).symm

/-! ## Constant time -/

theorem pre_taint : ∃ h, (taint.check (Taint.ofRegs [.x19, .x20, .x21, .x22, .x23, .x24])
    (.block (xorInto ++ callArgs)) h).isSome = true := ⟨_, by taint_decide⟩

theorem post_taint : ∃ h, (taint.check (Taint.ofRegs [.x21, .x22, .x23, .x24])
    (.block (xorInto ++ mulA ++ advance)) h).isSome = true := ⟨_, by taint_decide⟩

theorem encBody_ct (v : BlocksImpl) : BodyCt (AesXts.xtsMode true) (body v.enc) :=
  fun hp hp' hq k => VG.Proof.AesCbc.AArch64.body_ct (D := fun s₀ k => blk s₀ k) (fun hq k => pub_blk hq k)
    v.encOk v.encCt v.encNoFrames pre_taint post_taint
    (@fun _ hp _ hk _ h => WP.mono (preA_wp hp hk h) fun _ a => Mid.of h a.pre a.saved a.sp) hp hp' hq k

theorem decBody_ct (v : BlocksImpl) : BodyCt (AesXts.xtsMode false) (body v.dec) :=
  fun hp hp' hq k => VG.Proof.AesCbc.AArch64.body_ct (D := fun s₀ k => blk s₀ k) (fun hq k => pub_blk hq k)
    v.decOk v.decCt v.decNoFrames pre_taint post_taint
    (@fun _ hp _ hk _ h => WP.mono (preA_wp hp hk h) fun _ a => Mid.of h a.pre a.saved a.sp) hp hp' hq k

end VG.Proof.AesXts.AArch64
