import VerifiedGarbage.Proof.AesXts.X86.Steps
import VerifiedGarbage.Proof.AesCbc.X86.CT

/-!
# XTS-AES on x86: one block, and constant time

`body_ok'`: one run of `body` takes the loop invariant AES-CBC's proofs
share (`Proof/AesCbc/X86/Loop.lean`) from `k` blocks to `k + 1`, for
`xtsMode enc`, for any implementation of the block functions
(`BlocksImpl`), with `vg_aes_encrypt_blocks` for encryption and
`vg_aes_decrypt_blocks` for decryption. The tweak is XORed into the data
block (`preA_wp`), which is enciphered in place, the tweak is XORed in
again, and the tweak is multiplied by `α` (`Steps.lean`). `encBody_ct` and
`decBody_ct`: they are constant time, by the shared framework, with the call
on the data block.
-/

namespace VG.Proof.AesXts.X86

open VG VG.X86 VG.Impl.AesXts.X86
open VG.Impl.AesCbc.X86 (blkCall callArgs)
open VG.Impl.CmacAes.X86 (argOp advance xor4)
open VG.Proof.CmacAes.X86 (wp_arg xor4_ok add0)
open VG.Proof.AesCbc (aesWith_state aesInvWith_state xorIn4_bytes set_prefix Mode ciphOf)
open VG.Proof.AesCbc.X86
open VG.Proof.Aes.X86 (BlocksImpl)
open VG.Spec.Aes (bytesAt)

theorem pre_eq : pre = .mov .ebx (argOp 2) :: (xor4 .esi .ebx .esi 0 0 0 ++ callArgs) := rfl

theorem preA_wp {M : Mode} {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀)
    {s : State} (h : LInv M s₀ k s) :
    WP isa (.block pre) s (PreA s₀ k s
      (Proof.Cmac.xor4Mem s.mem (blk s₀ k) (blk s₀ k) ((Iv s₀).setWidth 64))) := by
  have hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rd, h.wr]
  have big := UPre.big_of h.frame
  have hargs := hp.args_of big
  have hd := hp.d32 hk
  have qN := hp.dataN hk
  have hdf := hp.data_fit
  have hiv := hp.iv_fit
  rw [pre_eq]
  refine wp_arg (s₀ := s₀) h.esp (by rw [hrw]; exact hp.arg_in (by decide)) (hargs 2 (by decide)) fun s₁ u₁ => ?_
  have i₁ : s₁.gpr .esi = D32 s₀ k := by rw [u₁.other _ (by decide), h.esi]
  have b₁ : s₁.gpr .ebx = Iv s₀ := u₁.gpr
  have rw₁ : s₁.rd ++ s₁.wr = [schR s₀, argsR s₀, ivR s₀, dataR s₀, scrR s₀] := by
    rw [u₁.rd, u₁.wr, h.rd, h.wr, hp.rd, hp.wr]; rfl
  have w₁ : s₁.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [u₁.wr, h.wr, hp.wr]
  refine xor4_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [i₁, qN]; omega) (by rw [b₁]; omega) (by rw [i₁, qN]; omega)
    (by rw [i₁, add0, hd, rw₁]; exact covBlk hk (by simp))
    (by rw [b₁, add0, rw₁]; exact covIv (by simp))
    (by rw [i₁, add0, hd, w₁]; exact covBlk hk (by simp)) fun s₂ g₂ => ?_
  have m₂ : s₂.mem = Proof.Cmac.xor4Mem s.mem (blk s₀ k) (blk s₀ k) ((Iv s₀).setWidth 64) := by
    rw [g₂.mem, i₁, b₁, add0, add0, hd, u₁.mem]
  have f₂ : Frame [⟨blk s₀ k, 16⟩] s.mem s₂.mem := by rw [m₂]; exact Proof.Cmac.xor4Mem_frame _ _ _ _
  have big₂ : Frame (Big s₀) s₀.mem s₂.mem := big.trans (f₂.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨dataR s₀, by simp, UPre.data_sub hk⟩)
  refine WP.mono (callArgs_wp hp hk (by rw [g₂.gpr _ (by decide) (by decide), i₁])
    (by rw [g₂.gpr _ (by decide) (by decide), u₁.other _ (by decide), h.esp])
    (by rw [g₂.rd, u₁.rd, h.rd]) (by rw [g₂.wr, u₁.wr, h.wr]) (hp.args_of big₂)) fun s₃ a => ?_
  exact ⟨a.pre, by rw [a.esi, g₂.gpr _ (by decide) (by decide), u₁.other _ (by decide)],
    by rw [a.esp, g₂.gpr _ (by decide) (by decide), u₁.other _ (by decide)], by rw [a.mem, m₂],
    by rw [a.rd, g₂.rd, u₁.rd], by rw [a.wr, g₂.wr, u₁.wr]⟩

theorem post_eq : post = .mov .ebx (argOp 2) :: (xor4 .esi .ebx .esi 0 0 0 ++ (mulA ++ advance)) := by
  simp only [post, List.append_assoc]; rfl

/-- One block in the direction `enc`, by a block function `b` computing `f`,
which is `ciphOf enc` on bytes. -/
theorem body_ok' (enc : Bool) {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State}
    {b : Impl.Aes.X86.Blocks}
    (ok : ∀ s, (Proof.Aes.blocksX86 f).pre s →
      ∃ t s', Exec isa b.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86 f).post s s')
    (nosp : NoSp b.code) (stack : stackUse b.code = 0)
    (hf : ∀ R w m p, (f R w (Spec.Aes.stateAt m p)).toList = ciphOf enc R w (bytesAt m p 16)) :
    BodyOk (AesXts.xtsMode enc) (body b) := by
  intro s₀ hp k hk s h
  have hd := hp.d32 hk
  have qN := hp.dataN hk
  have hdf := hp.data_fit
  have hiv := hp.iv_fit
  refine WP.seq (WP.mono (preA_wp hp hk h) fun s₁ a => ?_)
  refine WP.seq (WP.mono (blk_call ok nosp stack a.pre) fun s₂ c => ?_)
  have esp₁ : s₁.gpr .esp = E s₀ := by rw [a.esp, h.esp]
  have hb : below (s₁.gpr .esp) 24 = stkR s₀ := by rw [esp₁]; exact hp.below_eq
  -- Memory so far.
  have f₁ : Frame [⟨blk s₀ k, 16⟩] s.mem s₁.mem := by rw [a.mem]; exact Proof.Cmac.xor4Mem_frame _ _ _ _
  have f₂ : Frame [⟨blk s₀ k, 16⟩, ⟨(S s₀).setWidth 64, 2048⟩, stkR s₀] s₁.mem s₂.mem := by
    have fr := c.frame; rw [hb, hd] at fr; exact fr
  have fs₂ : Frame [⟨blk s₀ k, 16⟩, ivR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stkR s₀] s.mem s₂.mem :=
    (f₁.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact stepIn (.inl rfl)).trans
      (f₂.sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact stepIn (.inl rfl)
        · exact stepIn (.inr (.inr (.inl (Region.sub_prefix (by decide)))))
        · exact stepIn (.inr (.inr (.inr rfl))))
  have bigOf : ∀ {m : Mem}, Frame [⟨blk s₀ k, 16⟩, ivR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stkR s₀] s.mem m →
      Frame (Big s₀) s₀.mem m := fun hf => (UPre.big_of h.frame).trans ((stepFrame hk hf).sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨ivR s₀, by simp, fun _ h => h⟩
    · exact ⟨dataR s₀, by simp, fun _ h => h⟩
    · exact ⟨scrR s₀, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨stkR s₀, by simp, fun _ h => h⟩)
  have big₁ : Frame (Big s₀) s₀.mem s₁.mem := bigOf (f₁.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact stepIn (.inl rfl))
  have big₂ := bigOf fs₂
  have esi₂ : s₂.gpr .esi = D32 s₀ k := by rw [c.saved .esi (by simp [calleeSaved]), a.esi, h.esi]
  have esp₂ : s₂.gpr .esp = E s₀ := by rw [c.saved .esp (by simp [calleeSaved]), esp₁]
  have rw₂ : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [c.rd, c.wr, a.rd, a.wr, h.rd, h.wr]
  have rwl : s₂.rd ++ s₂.wr = [schR s₀, argsR s₀, ivR s₀, dataR s₀, scrR s₀] := by
    rw [rw₂, hp.rd, hp.wr]; rfl
  have w₂ : s₂.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [c.wr, a.wr, h.wr, hp.wr]
  rw [post_eq]
  refine wp_arg (s₀ := s₀) esp₂ (by rw [rw₂]; exact hp.arg_in (by decide)) (hp.args_of big₂ 2 (by decide))
    fun s₃ u₃ => ?_
  have b₃ : s₃.gpr .ebx = Iv s₀ := u₃.gpr
  have i₃ : s₃.gpr .esi = D32 s₀ k := by rw [u₃.other _ (by decide), esi₂]
  refine xor4_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [i₃, qN]; omega) (by rw [b₃]; omega) (by rw [i₃, qN]; omega)
    (by rw [i₃, add0, hd, u₃.rd, u₃.wr, rwl]; exact covBlk hk (by simp))
    (by rw [b₃, add0, u₃.rd, u₃.wr, rwl]; exact covIv (by simp))
    (by rw [i₃, add0, hd, u₃.wr, w₂]; exact covBlk hk (by simp)) fun s₄ g₄ => ?_
  have m₄ : s₄.mem = Proof.Cmac.xor4Mem s₂.mem (blk s₀ k) (blk s₀ k) ((Iv s₀).setWidth 64) := by
    rw [g₄.mem, i₃, b₃, add0, add0, hd, u₃.mem]
  have f₄ : Frame [⟨blk s₀ k, 16⟩] s₂.mem s₄.mem := by rw [m₄]; exact Proof.Cmac.xor4Mem_frame _ _ _ _
  have b₄ : s₄.gpr .ebx = Iv s₀ := by rw [g₄.gpr _ (by decide) (by decide), b₃]
  have rwl₄ : s₄.rd ++ s₄.wr = [schR s₀, argsR s₀, ivR s₀, dataR s₀, scrR s₀] := by
    rw [g₄.rd, g₄.wr, u₃.rd, u₃.wr, rwl]
  have wl₄ : s₄.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [g₄.wr, u₃.wr, w₂]
  obtain ⟨s₅, run₅, g₅, mem₅, rd₅, wr₅⟩ := mulA_ok s₄ (Q := (Iv s₀).setWidth 64) (by rw [b₄]) (by rw [b₄]; omega)
    (fun d n hdn => by rw [rwl₄]; exact ⟨ivR s₀, by simp, Offset.contains_base _ hdn (by omega)⟩)
    (fun d n hdn => by rw [wl₄]; exact ⟨ivR s₀, by simp, Offset.contains_base _ hdn (by omega)⟩)
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨s₅, run₅, ?_⟩
  have f₅ : Frame [ivR s₀] s₄.mem s₅.mem := by rw [mem₅]; exact alphaMem_frame _ _
  have fStep : Frame [⟨blk s₀ k, 16⟩, ivR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stkR s₀] s.mem s₅.mem :=
    (fs₂.trans (f₄.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact stepIn (.inl rfl))).trans
      (f₅.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact stepIn (.inr (.inl rfl)))
  have keep₅ (r : Reg) (h₁ : r ≠ .eax) (h₂ : r ≠ .ecx) (h₃ : r ≠ .edx) (h₄ : r ≠ .edi) (h₅ : r ≠ .ebp)
      (h₆ : r ≠ .ebx) : s₅.gpr r = s₂.gpr r := by
    rw [g₅ r h₁ h₂ h₃ h₄ h₅, g₄.gpr _ h₁ h₂, u₃.other _ h₆]
  refine WP.mono (advance_wp hp hk
    (by rw [keep₅ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), esi₂])
    (by rw [keep₅ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), esp₂])
    (hp.args_of (bigOf fStep)) (by rw [rd₅, wr₅, g₄.rd, g₄.wr, u₃.rd, u₃.wr, rw₂]))
    fun s₈ ⟨esi₈, esp₈, _, mem₈, rd₈, wr₈, zf₈⟩ => ⟨?_, zf₈⟩
  have callIv : ∀ r ∈ [⟨blk s₀ k, 16⟩, ⟨(S s₀).setWidth 64, 2048⟩, stkR s₀], (ivR s₀).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (hp.blk_iv hk).symm
    · exact hp.iv_scr.sub_right (Region.sub_prefix (by decide))
    · exact hp.b_iv.symm
  have hlt : ((blks s₀).take k).length = k := by simp [Spec.Cbc.blocksAt]; omega
  have ivIn : bytesAt s₂.mem ((Iv s₀).setWidth 64) 16 = chainK (AesXts.xtsMode enc) s₀ k := by
    rw [Proof.Cmac.bytesAt_frame f₂ callIv (by decide), a.mem,
      Proof.Cmac.bytesAt_frame (Proof.Cmac.xor4Mem_frame _ _ _ _) (one (hp.blk_iv hk).symm) (by decide), h.iv]
  have newBlk : bytesAt s₈.mem (blk s₀ k) 16 =
      Spec.Xts.block (ciphOf enc (R s₀) (wK s₀)) (Spec.Xts.next (iv0 s₀) k)
        ((blks s₀)[k]'(by simp [Spec.Cbc.blocksAt]; exact hk)) := by
    rw [mem₈, Proof.Cmac.bytesAt_frame f₅ (one (hp.blk_iv hk)) (by decide), m₄, xorIn4_bytes _ (hp.blk_iv hk),
      ivIn, ← hd, c.out, hd, hf, UPre.sched_bytes hp big₁, a.mem, xorIn4_bytes _ (hp.blk_iv hk), h.block hk, h.iv]
    simp only [chainK, AesXts.xtsMode_chain, hlt]
    rfl
  have newIv : bytesAt s₈.mem ((Iv s₀).setWidth 64) 16 = Spec.Xts.mulAlpha (chainK (AesXts.xtsMode enc) s₀ k) := by
    rw [mem₈, mem₅, alphaMem_bytes, m₄,
      Proof.Cmac.bytesAt_frame (Proof.Cmac.xor4Mem_frame _ _ _ _) (one (hp.blk_iv hk).symm) (by decide), ivIn]
  have hl : (outK (AesXts.xtsMode enc) s₀ k).length = k := by
    rw [outK, Mode.length_out]; simp [Spec.Cbc.blocksAt]; omega
  have outSucc :
      outK (AesXts.xtsMode enc) s₀ (k + 1) = outK (AesXts.xtsMode enc) s₀ k ++ [bytesAt s₈.mem (blk s₀ k) 16] := by
    rw [newBlk]
    simp only [outK, AesXts.xtsMode_out, take_succ_blks s₀ hk, AesXts.crypt_snoc, hlt]
  refine ⟨esi₈, esp₈, by rw [rd₈, rd₅, g₄.rd, u₃.rd, c.rd, a.rd, h.rd],
    by rw [wr₈, wr₅, g₄.wr, u₃.wr, c.wr, a.wr, h.wr], by rw [mem₈]; exact h.frame.trans (stepFrame hk fStep),
    ?_, ?_⟩
  · rw [mem₈, hp.blocksAt_step hk fStep, h.data, ← mem₈, outSucc,
      set_prefix _ _ _ hl (by simp [Spec.Cbc.blocksAt]; exact hk)]
  · rw [newIv]
    simp only [chainK, AesXts.xtsMode_chain, take_succ_blks s₀ hk, List.length_append, List.length_singleton,
      hlt, AesXts.next_succ]

theorem encBody_ok (v : BlocksImpl) : BodyOk (AesXts.xtsMode true) (body v.enc) :=
  body_ok' true v.encOk v.encNosp v.encStack fun _ _ _ _ => (aesWith_state _ _ _ _).symm

theorem decBody_ok (v : BlocksImpl) : BodyOk (AesXts.xtsMode false) (body v.dec) :=
  body_ok' false v.decOk v.decNosp v.decStack fun _ _ _ _ => (aesInvWith_state _ _ _ _).symm

/-! ## Constant time -/

theorem pre_taint : ∃ h, (taint.check (argTaint [.esi] (4 + 4 * 6)) (.block pre) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem post_taint : ∃ h, (taint.check (argTaint [.esi] (4 + 4 * 6)) (.block post) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem encBody_ct (v : BlocksImpl) : BodyCt (AesXts.xtsMode true) (body v.enc) :=
  fun hp hp' hq k => body_ct (fun hq k => pub_D32 hq k) v.encOk v.encCt v.encNosp v.encStack pre_taint post_taint
    (@fun _ hp _ hk _ h => WP.mono (preA_wp hp hk h) fun _ a => Mid.of hp hk h a
      ((Proof.Cmac.xor4Mem_frame _ _ _ _).sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩)) hp hp' hq k

theorem decBody_ct (v : BlocksImpl) : BodyCt (AesXts.xtsMode false) (body v.dec) :=
  fun hp hp' hq k => body_ct (fun hq k => pub_D32 hq k) v.decOk v.decCt v.decNosp v.decStack pre_taint post_taint
    (@fun _ hp _ hk _ h => WP.mono (preA_wp hp hk h) fun _ a => Mid.of hp hk h a
      ((Proof.Cmac.xor4Mem_frame _ _ _ _).sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩)) hp hp' hq k

end VG.Proof.AesXts.X86
