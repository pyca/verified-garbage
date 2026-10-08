import VerifiedGarbage.Proof.AesOfb.Spec
import VerifiedGarbage.Proof.AesCbc.X86.CT
import VerifiedGarbage.Impl.AesOfb.X86

/-!
# AES-OFB on x86: one block, and constant time

`body_ok`: one run of `body` takes the loop invariant AES-CBC's proofs
share (`Proof/AesCbc/X86/Loop.lean`) from `k` blocks to `k + 1`, for
`ofbMode`, for any implementation of the block functions (`BlocksImpl`).
`body_ct`: it is constant time, by the shared framework, with the call on
the block at `iv`.
-/

namespace VG.Proof.AesOfb.X86

open VG VG.X86 VG.Impl.AesOfb.X86
open VG.Impl.CmacAes.X86 (argOp advance xor4)
open VG.Impl.AesCbc.X86 (whole blkCall)
open VG.Proof.CmacAes.X86 (wp_arg xor4_ok add0 arg_ofNat)
open VG.Proof.MdStream.X86 (Upd wp_mov wp_movi)
open VG.Proof.AesCbc
open VG.Proof.AesCbc.X86
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86 (BlocksImpl)

/-- The arguments of a call on the block at `iv`, with the working space at
the start of the scratch buffer. -/
theorem blkPreIv {s₀ : State} (hp : UPre s₀) {s : State}
    (eax : s.gpr .eax = W s₀) (ecx : s.gpr .ecx = arg s₀ 1) (ebx : s.gpr .ebx = Iv s₀)
    (edi : s.gpr .edi = 1) (ebp : s.gpr .ebp = S s₀) (esp : s.gpr .esp = E s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    BlkPre s (W s₀) (Iv s₀) (S s₀) (R s₀) := by
  have hb : below (s.gpr .esp) 24 = stkR s₀ := by rw [esp]; exact hp.below_eq
  refine ⟨eax, by rw [ecx]; exact arg_ofNat s₀ 1, ebx, edi, ebp, hp.rounds, by rw [esp]; exact hp.esp24,
    hp.sch_iv, hp.sch_scr.sub_right (Region.sub_prefix (by decide)),
    hp.iv_scr.sub_right (Region.sub_prefix (by decide)), by rw [hb]; exact hp.b_sch, by rw [hb]; exact hp.b_iv,
    by rw [hb]; exact hp.b_scr.sub_right (Region.sub_prefix (by decide)), hp.sch_fit, hp.iv_fit,
    by have := hp.scr_fit; omega, ?_, ?_⟩
  · rw [hrd, hwr, hp.rd, hp.wr]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨schR s₀, by simp, 0, by simp, by simp⟩
  · rw [hwr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨ivR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩

/-- What the code before the call leaves. -/
structure IvA (s₀ : State) (s s₁ : State) : Prop where
  pre : BlkPre s₁ (W s₀) (Iv s₀) (S s₀) (R s₀)
  esi : s₁.gpr .esi = s.gpr .esi
  esp : s₁.gpr .esp = s.gpr .esp
  mem : s₁.mem = s.mem
  rd : s₁.rd = s.rd
  wr : s₁.wr = s.wr

theorem ivArgs_eq : ivArgs = [.mov .eax (argOp 0), .mov .ecx (argOp 1), .mov .ebx (argOp 2),
    .mov .edi (.imm 1), .mov .ebp (argOp 5)] := rfl

theorem ivA_wp {M : Mode} {s₀ : State} (hp : UPre s₀) {k : Nat} {s : State} (h : LInv M s₀ k s) :
    WP isa (.block ivArgs) s (IvA s₀ s) := by
  have hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rd, h.wr]
  have hargs := hp.args_of (UPre.big_of h.frame)
  have hesp := h.esp
  rw [ivArgs_eq]
  refine wp_arg (s₀ := s₀) hesp (by rw [hrw]; exact hp.arg_in (by decide)) (hargs 0 (by decide)) fun s₁ u₁ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₁.other _ (by decide), hesp]) (by rw [u₁.rd, u₁.wr, hrw]; exact hp.arg_in (by decide))
    (by rw [u₁.mem]; exact hargs 1 (by decide)) fun s₂ u₂ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₂.other _ (by decide), u₁.other _ (by decide), hesp])
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr, hrw]; exact hp.arg_in (by decide))
    (by rw [u₂.mem, u₁.mem]; exact hargs 2 (by decide)) fun s₃ u₃ => wp_movi fun s₄ u₄ => ?_
  refine wp_arg (s₀ := s₀)
    (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hesp])
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr, hrw]; exact hp.arg_in (by decide))
    (by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]; exact hargs 5 (by decide)) fun s₅ u₅ => WP.block_nil ?_
  have keep : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .ebx → r ≠ .edi → r ≠ .ebp → s₅.gpr r = s.gpr r :=
    fun r ha hc hb hd hp' => by
      rw [u₅.other _ hp', u₄.other _ hd, u₃.other _ hb, u₂.other _ hc, u₁.other _ ha]
  have rd₅ : s₅.rd = s.rd := by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have wr₅ : s₅.wr = s.wr := by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have esp₅ : s₅.gpr .esp = E s₀ := by rw [keep _ (by decide) (by decide) (by decide) (by decide) (by decide), hesp]
  refine ⟨blkPreIv hp ?_ ?_ ?_ ?_ u₅.gpr esp₅ (by rw [rd₅, h.rd]) (by rw [wr₅, h.wr]),
    keep _ (by decide) (by decide) (by decide) (by decide) (by decide), by rw [esp₅, hesp],
    by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem], rd₅, wr₅⟩
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr]
  · rw [u₅.other _ (by decide), u₄.gpr]

theorem post_eq : post = .mov .ebx (argOp 2) :: (xor4 .esi .ebx .esi 0 0 0 ++ advance) := rfl

theorem body_ok (v : BlocksImpl) : BodyOk ofbMode (body v.enc) := by
  intro s₀ hp k hk s h
  have hd := hp.d32 hk
  have qN := hp.dataN hk
  have hdf := hp.data_fit
  have hiv := hp.iv_fit
  refine WP.seq (WP.mono (ivA_wp hp h) fun s₁ a => ?_)
  refine WP.seq (WP.mono (blk_call v.encOk v.encNosp v.encStack a.pre) fun s₂ c => ?_)
  have esp₁ : s₁.gpr .esp = E s₀ := by rw [a.esp, h.esp]
  have hb : below (s₁.gpr .esp) 24 = stkR s₀ := by rw [esp₁]; exact hp.below_eq
  -- Memory so far.
  have f₂ : Frame [ivR s₀, ⟨(S s₀).setWidth 64, 2048⟩, stkR s₀] s.mem s₂.mem := by
    have fr := c.frame; rw [hb, a.mem] at fr; exact fr
  have fs₂ : Frame [⟨blk s₀ k, 16⟩, ivR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stkR s₀] s.mem s₂.mem :=
    f₂.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact stepIn (.inr (.inl rfl))
      · exact stepIn (.inr (.inr (.inl (Region.sub_prefix (by decide)))))
      · exact stepIn (.inr (.inr (.inr rfl)))
  have bigOf : ∀ {m : Mem}, Frame [⟨blk s₀ k, 16⟩, ivR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stkR s₀] s.mem m →
      Frame (Big s₀) s₀.mem m := fun hf => (UPre.big_of h.frame).trans ((stepFrame hk hf).sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨ivR s₀, by simp, fun _ h => h⟩
    · exact ⟨dataR s₀, by simp, fun _ h => h⟩
    · exact ⟨scrR s₀, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨stkR s₀, by simp, fun _ h => h⟩)
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
  have fStep : Frame [⟨blk s₀ k, 16⟩, ivR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stkR s₀] s.mem s₄.mem :=
    fs₂.trans (f₄.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact stepIn (.inl rfl))
  have esp₄ : s₄.gpr .esp = E s₀ := by rw [g₄.gpr _ (by decide) (by decide), u₃.other _ (by decide), esp₂]
  refine WP.mono (advance_wp hp hk (by rw [g₄.gpr _ (by decide) (by decide), i₃]) esp₄
    (hp.args_of (bigOf fStep)) (by rw [g₄.rd, g₄.wr, u₃.rd, u₃.wr, rw₂]))
    fun s₅ ⟨esi₅, esp₅, _, mem₅, rd₅, wr₅, zf₅⟩ => ⟨?_, zf₅⟩
  have hblk := h.block hk
  have big : Frame (Big s₀) s₀.mem s.mem := UPre.big_of h.frame
  have newIv : bytesAt s₅.mem ((Iv s₀).setWidth 64) 16 =
      Spec.Cbc.aesWith (R s₀) (wK s₀) (chainK ofbMode s₀ k) := by
    rw [mem₅, m₄, Proof.Cmac.bytesAt_frame (Proof.Cmac.xor4Mem_frame _ _ _ _) (one (hp.blk_iv hk).symm)
        (by decide),
      c.out, a.mem, UPre.sched_bytes hp big, ← aesWith_state, h.iv]
  have newBlk : bytesAt s₅.mem (blk s₀ k) 16 =
      Spec.Cbc.xor ((blks s₀)[k]'(by simp [Spec.Cbc.blocksAt]; exact hk))
        (bytesAt s₅.mem ((Iv s₀).setWidth 64) 16) := by
    rw [mem₅, m₄, xorIn4_bytes _ (hp.blk_iv hk), ← hblk,
      Proof.Cmac.bytesAt_frame f₂ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact hp.blk_iv hk
        · exact (hp.data_scr.sub_left (UPre.data_sub hk)).sub_right (Region.sub_prefix (by decide))
        · exact hp.b_data.symm.sub_left (UPre.data_sub hk)) (by decide),
      Proof.Cmac.bytesAt_frame (Proof.Cmac.xor4Mem_frame _ _ _ _) (one (hp.blk_iv hk).symm) (by decide)]
  have hl : ((blks s₀).take k).length = k := by simp [Spec.Cbc.blocksAt]; omega
  have outSucc : outK ofbMode s₀ (k + 1) = outK ofbMode s₀ k ++ [bytesAt s₅.mem (blk s₀ k) 16] := by
    rw [newBlk, newIv]
    simp only [outK, chainK, ofbMode_out, ofbMode_chain, take_succ_blks s₀ hk, crypt_snoc, hl]
  have hl' : (outK ofbMode s₀ k).length = k := by rw [outK, Mode.length_out, hl]
  refine ⟨esi₅, esp₅, by rw [rd₅, g₄.rd, u₃.rd, c.rd, a.rd, h.rd],
    by rw [wr₅, g₄.wr, u₃.wr, c.wr, a.wr, h.wr], by rw [mem₅]; exact h.frame.trans (stepFrame hk fStep),
    ?_, ?_⟩
  · rw [mem₅, hp.blocksAt_step hk fStep, h.data, ← mem₅, outSucc,
      set_prefix _ _ _ hl' (by simp [Spec.Cbc.blocksAt]; exact hk)]
  · rw [newIv]
    simp only [chainK, ofbMode_chain, take_succ_blks s₀ hk, List.length_append, List.length_singleton, hl,
      next_succ]

/-! ## Constant time -/

theorem pre_taint : ∃ h, (taint.check (argTaint [.esi] (4 + 4 * 6)) (.block ivArgs) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem post_taint : ∃ h, (taint.check (argTaint [.esi] (4 + 4 * 6)) (.block post) h).isSome = true :=
  ⟨_, by taint_decide⟩

/-- What the code before the call leaves, as `Mid`. -/
theorem mid_of {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s s₁ : State}
    {M : Mode} (h : LInv M s₀ k s) (a : IvA s₀ s s₁) : Mid s₀ k (Iv s₀) s₁ :=
  ⟨hk, a.pre, ⟨ivR s₀, by simp, fun _ h => h⟩, by rw [a.esi, h.esi],
    ⟨by rw [a.esp, h.esp], by rw [a.wr, h.wr], fun _ hi => by rw [a.mem]; exact hp.arg_keep (UPre.big_of h.frame) hi⟩,
    by rw [a.mem]; exact UPre.big_of h.frame⟩

theorem body_ct (v : BlocksImpl) : BodyCt ofbMode (body v.enc) :=
  fun hp hp' hq k => VG.Proof.AesCbc.X86.body_ct (D := fun s₀ _ => Iv s₀) (fun hq _ => pub_arg hq (by decide))
    v.encOk v.encCt v.encNosp v.encStack pre_taint post_taint
    (@fun _ hp _ hk _ h => WP.mono (ivA_wp hp h) fun _ a => mid_of hp hk h a) hp hp' hq k

end VG.Proof.AesOfb.X86
