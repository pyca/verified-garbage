import VerifiedGarbage.Proof.AesCfb.Spec
import VerifiedGarbage.Proof.AesOfb.X86.Body
import VerifiedGarbage.Impl.AesCfb.X86

/-!
# AES-CFB128 on x86: one block, and constant time

`encBody_ok` and `decBody_ok`: one run of `body` takes the loop invariant
AES-CBC's proofs share (`Proof/AesCbc/X86/Loop.lean`) from `k` blocks to
`k + 1`, for `cfbMode`, for any implementation of the block functions
(`BlocksImpl`). The code before the call and the call are AES-OFB's
(`Proof/AesOfb/X86/Body.lean`). `encBody_ct` and `decBody_ct`: they are
constant time, by the shared framework, with the call on the block at `iv`.
-/

namespace VG.Proof.AesCfb.X86

open VG VG.X86 VG.Impl.AesCfb.X86
open VG.Impl.CmacAes.X86 (argOp advance xor4 zero4)
open VG.Impl.AesCbc.X86 (whole blkCall)
open VG.Impl.AesOfb.X86 (ivArgs)
open VG.Proof.AesOfb.X86 (IvA ivA_wp mid_of)
open VG.Proof.CmacAes.X86 (wp_arg xor4_ok zero4_ok add0)
open VG.Proof.AesCbc
open VG.Proof.AesCbc.X86
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86 (BlocksImpl)

/-- What the code before the call, the call and `Pⱼ ⊕ Oⱼ` (or `Cⱼ ⊕ Oⱼ`)
into the data block leave, for either direction: `ebx` holds `iv`. -/
structure AfterXor (s₀ : State) (k : Nat) (s s₄ : State) : Prop where
  esi : s₄.gpr .esi = D32 s₀ k
  ebx : s₄.gpr .ebx = Iv s₀
  esp : s₄.gpr .esp = E s₀
  rd : s₄.rd = s₀.rd
  wr : s₄.wr = s₀.wr
  regs : s₄.rd ++ s₄.wr = [schR s₀, argsR s₀, ivR s₀, dataR s₀, scrR s₀]
  frame : Frame [⟨blk s₀ k, 16⟩, ivR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stkR s₀] s.mem s₄.mem
  blk : bytesAt s₄.mem (blk s₀ k) 16 =
    Spec.Cbc.xor (bytesAt s.mem (blk s₀ k) 16) (bytesAt s₄.mem ((Iv s₀).setWidth 64) 16)
  iv : bytesAt s₄.mem ((Iv s₀).setWidth 64) 16 =
    Spec.Cbc.aesWith (R s₀) (wK s₀) (bytesAt s.mem ((Iv s₀).setWidth 64) 16)

theorem head_ok {M : Mode} (v : BlocksImpl) {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s : State}
    (h : LInv M s₀ k s) (rest : List Instr) {Q : State → Prop}
    (hq : ∀ s₄, AfterXor s₀ k s s₄ → WP isa (.block rest) s₄ Q) :
    WP isa (body v.enc (([.mov .ebx (argOp 2)] : List Instr) ++ xor4 .esi .ebx .esi 0 0 0 ++ rest)) s Q := by
  have hd := hp.d32 hk
  have qN := hp.dataN hk
  have hdf := hp.data_fit
  have hiv := hp.iv_fit
  refine WP.seq (WP.mono (ivA_wp hp h) fun s₁ a => ?_)
  refine WP.seq (WP.mono (blk_call v.encOk v.encNosp v.encStack a.pre) fun s₂ c => ?_)
  have esp₁ : s₁.gpr .esp = E s₀ := by rw [a.esp, h.esp]
  have hb : below (s₁.gpr .esp) 24 = stkR s₀ := by rw [esp₁]; exact hp.below_eq
  have f₂ : Frame [ivR s₀, ⟨(S s₀).setWidth 64, 2048⟩, stkR s₀] s.mem s₂.mem := by
    have fr := c.frame; rw [hb, a.mem] at fr; exact fr
  have fs₂ : Frame [⟨blk s₀ k, 16⟩, ivR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stkR s₀] s.mem s₂.mem :=
    f₂.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact stepIn (.inr (.inl rfl))
      · exact stepIn (.inr (.inr (.inl (Region.sub_prefix (by decide)))))
      · exact stepIn (.inr (.inr (.inr rfl)))
  have big₂ : Frame (Big s₀) s₀.mem s₂.mem :=
    (UPre.big_of h.frame).trans ((stepFrame hk fs₂).sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨ivR s₀, by simp, fun _ h => h⟩
      · exact ⟨dataR s₀, by simp, fun _ h => h⟩
      · exact ⟨scrR s₀, by simp, Region.sub_prefix (by decide)⟩
      · exact ⟨stkR s₀, by simp, fun _ h => h⟩)
  have esi₂ : s₂.gpr .esi = D32 s₀ k := by rw [c.saved .esi (by simp [calleeSaved]), a.esi, h.esi]
  have esp₂ : s₂.gpr .esp = E s₀ := by rw [c.saved .esp (by simp [calleeSaved]), esp₁]
  have rw₂ : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [c.rd, c.wr, a.rd, a.wr, h.rd, h.wr]
  have rwl : s₂.rd ++ s₂.wr = [schR s₀, argsR s₀, ivR s₀, dataR s₀, scrR s₀] := by
    rw [rw₂, hp.rd, hp.wr]; rfl
  have w₂ : s₂.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [c.wr, a.wr, h.wr, hp.wr]
  rw [List.append_assoc, List.singleton_append]
  refine wp_arg (s₀ := s₀) esp₂ (by rw [rw₂]; exact hp.arg_in (by decide)) (hp.args_of big₂ 2 (by decide))
    fun s₃ u₃ => ?_
  have b₃ : s₃.gpr .ebx = Iv s₀ := u₃.gpr
  have i₃ : s₃.gpr .esi = D32 s₀ k := by rw [u₃.other _ (by decide), esi₂]
  refine xor4_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [i₃, qN]; omega) (by rw [b₃]; omega) (by rw [i₃, qN]; omega)
    (by rw [i₃, add0, hd, u₃.rd, u₃.wr, rwl]; exact covBlk hk (by simp))
    (by rw [b₃, add0, u₃.rd, u₃.wr, rwl]; exact covIv (by simp))
    (by rw [i₃, add0, hd, u₃.wr, w₂]; exact covBlk hk (by simp)) fun s₄ g₄ => hq s₄ ?_
  have m₄ : s₄.mem = Proof.Cmac.xor4Mem s₂.mem (blk s₀ k) (blk s₀ k) ((Iv s₀).setWidth 64) := by
    rw [g₄.mem, i₃, b₃, add0, add0, hd, u₃.mem]
  have f₄ : Frame [⟨blk s₀ k, 16⟩] s₂.mem s₄.mem := by rw [m₄]; exact Proof.Cmac.xor4Mem_frame _ _ _ _
  have big : Frame (Big s₀) s₀.mem s.mem := UPre.big_of h.frame
  have iv₄ : bytesAt s₄.mem ((Iv s₀).setWidth 64) 16 = bytesAt s₂.mem ((Iv s₀).setWidth 64) 16 :=
    Proof.Cmac.bytesAt_frame f₄ (one (hp.blk_iv hk).symm) (by decide)
  refine ⟨by rw [g₄.gpr _ (by decide) (by decide), i₃], by rw [g₄.gpr _ (by decide) (by decide), b₃],
    by rw [g₄.gpr _ (by decide) (by decide), u₃.other _ (by decide), esp₂],
    by rw [g₄.rd, u₃.rd, c.rd, a.rd, h.rd], by rw [g₄.wr, u₃.wr, c.wr, a.wr, h.wr],
    by rw [g₄.rd, g₄.wr, u₃.rd, u₃.wr, rwl],
    fs₂.trans (f₄.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact stepIn (.inl rfl)),
    ?_, ?_⟩
  · rw [iv₄, m₄, xorIn4_bytes _ (hp.blk_iv hk),
      Proof.Cmac.bytesAt_frame f₂ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact hp.blk_iv hk
        · exact (hp.data_scr.sub_left (UPre.data_sub hk)).sub_right (Region.sub_prefix (by decide))
        · exact hp.b_data.symm.sub_left (UPre.data_sub hk)) (by decide)]
  · rw [iv₄, c.out, a.mem, UPre.sched_bytes hp big, ← aesWith_state]

/-- What the invariant needs after a block, from what the block leaves. -/
theorem linv_succ {M : Mode} {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s s₄ s₆ : State}
    (h : LInv M s₀ k s) (x : AfterXor s₀ k s s₄)
    (g₆ : ∀ r, r ≠ .eax → r ≠ .ecx → s₆.gpr r = s₄.gpr r) (rd₆ : s₆.rd = s₄.rd) (wr₆ : s₆.wr = s₄.wr)
    (f₆ : Frame [ivR s₀] s₄.mem s₆.mem)
    (hout : outK M s₀ (k + 1) = outK M s₀ k ++ [bytesAt s₆.mem (blk s₀ k) 16])
    (hiv : bytesAt s₆.mem ((Iv s₀).setWidth 64) 16 = chainK M s₀ (k + 1)) :
    WP isa (.block advance) s₆ fun s' => LInv M s₀ (k + 1) s' ∧ s'.zf = some (decide (k + 1 = N s₀)) := by
  have fStep : Frame [⟨blk s₀ k, 16⟩, ivR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stkR s₀] s.mem s₆.mem :=
    x.frame.trans (f₆.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact stepIn (.inr (.inl rfl)))
  have bigOf : Frame (Big s₀) s₀.mem s₆.mem := (UPre.big_of h.frame).trans ((stepFrame hk fStep).sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨ivR s₀, by simp, fun _ h => h⟩
    · exact ⟨dataR s₀, by simp, fun _ h => h⟩
    · exact ⟨scrR s₀, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨stkR s₀, by simp, fun _ h => h⟩)
  have hl' : (outK M s₀ k).length = k := by
    rw [outK, Mode.length_out]; simp [Spec.Cbc.blocksAt]; omega
  refine WP.mono (advance_wp hp hk (by rw [g₆ _ (by decide) (by decide), x.esi])
    (by rw [g₆ _ (by decide) (by decide), x.esp]) (hp.args_of bigOf)
    (by rw [rd₆, wr₆, x.rd, x.wr])) fun s₇ ⟨esi₇, esp₇, _, mem₇, rd₇, wr₇, zf₇⟩ => ⟨?_, zf₇⟩
  refine ⟨esi₇, esp₇, by rw [rd₇, rd₆, x.rd], by rw [wr₇, wr₆, x.wr],
    by rw [mem₇]; exact h.frame.trans (stepFrame hk fStep), ?_, ?_⟩
  · rw [mem₇, hp.blocksAt_step hk fStep, h.data, hout,
      set_prefix _ _ _ hl' (by simp [Spec.Cbc.blocksAt]; exact hk)]
  · rw [mem₇, hiv]

theorem encPost_eq : encPost =
    ([.mov .ebx (argOp 2)] : List Instr) ++ xor4 .esi .ebx .esi 0 0 0 ++
      (zero4 .ebx 0 ++ (xor4 .ebx .esi .ebx 0 0 0 ++ advance)) := by
  simp only [encPost, List.append_assoc]

theorem decPost_eq : decPost =
    ([.mov .ebx (argOp 2)] : List Instr) ++ xor4 .esi .ebx .esi 0 0 0 ++ (xor4 .ebx .esi .ebx 0 0 0 ++ advance) := by
  simp only [decPost, List.append_assoc]

theorem encBody_ok (v : BlocksImpl) : BodyOk (cfbMode true) (body v.enc encPost) := by
  intro s₀ hp k hk s h
  have hd := hp.d32 hk
  have qN := hp.dataN hk
  have hdf := hp.data_fit
  have hiv := hp.iv_fit
  rw [encPost_eq]
  refine head_ok v hp hk h _ fun s₄ x => ?_
  refine zero4_ok (by decide) (by rw [x.ebx]; omega) (by rw [x.ebx, add0, x.wr, hp.wr]; exact covIv (by simp))
    fun s₅ g₅ m₅ rd₅ wr₅ => ?_
  have b₅ : s₅.gpr .ebx = Iv s₀ := by rw [g₅ _ (by decide), x.ebx]
  have i₅ : s₅.gpr .esi = D32 s₀ k := by rw [g₅ _ (by decide), x.esi]
  refine xor4_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [b₅]; omega) (by rw [i₅, qN]; omega) (by rw [b₅]; omega)
    (by rw [b₅, add0, rd₅, wr₅, x.regs]; exact covIv (by simp))
    (by rw [i₅, add0, hd, rd₅, wr₅, x.regs]; exact covBlk hk (by simp))
    (by rw [b₅, add0, wr₅, x.wr, hp.wr]; exact covIv (by simp)) fun s₆ g₆ => ?_
  have m₆ : s₆.mem = copy4Mem s₄.mem ((Iv s₀).setWidth 64) (blk s₀ k) := by
    rw [g₆.mem, b₅, i₅, add0, add0, hd, m₅, x.ebx, add0]; rfl
  have f₆ : Frame [ivR s₀] s₄.mem s₆.mem := by rw [m₆]; exact copy4Mem_frame _ _ _
  have b₆ : bytesAt s₆.mem (blk s₀ k) 16 = bytesAt s₄.mem (blk s₀ k) 16 :=
    Proof.Cmac.bytesAt_frame f₆ (one (hp.blk_iv hk)) (by decide)
  have i₆ : bytesAt s₆.mem ((Iv s₀).setWidth 64) 16 = bytesAt s₆.mem (blk s₀ k) 16 := by
    rw [b₆, m₆, copy4Mem_bytes _ (hp.blk_iv hk).symm]
  have newBlk : bytesAt s₆.mem (blk s₀ k) 16 =
      Spec.Cbc.xor ((blks s₀)[k]'(by simp [Spec.Cbc.blocksAt]; exact hk))
        (Spec.Cbc.aesWith (R s₀) (wK s₀) (chainK (cfbMode true) s₀ k)) := by
    rw [b₆, x.blk, h.block hk, x.iv, h.iv]
  have outSucc :
      outK (cfbMode true) s₀ (k + 1) = outK (cfbMode true) s₀ k ++ [bytesAt s₆.mem (blk s₀ k) 16] := by
    rw [newBlk]
    simp only [outK, chainK, cfbMode_out, cfbMode_chain, cfb, cts, ite_true, take_succ_blks s₀ hk,
      encrypt_snoc]
  refine linv_succ hp hk h x (fun r h₁ h₂ => by rw [g₆.gpr r h₁ h₂, g₅ r h₁]) (by rw [g₆.rd, rd₅])
    (by rw [g₆.wr, wr₅]) f₆ outSucc ?_
  rw [i₆]
  simp only [chainK, cfbMode_chain, cts, ite_true, outSucc, next_snoc]

theorem decBody_ok (v : BlocksImpl) : BodyOk (cfbMode false) (body v.enc decPost) := by
  intro s₀ hp k hk s h
  have hd := hp.d32 hk
  have qN := hp.dataN hk
  have hdf := hp.data_fit
  have hiv := hp.iv_fit
  rw [decPost_eq]
  refine head_ok v hp hk h _ fun s₄ x => ?_
  refine xor4_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [x.ebx]; omega) (by rw [x.esi, qN]; omega) (by rw [x.ebx]; omega)
    (by rw [x.ebx, add0, x.regs]; exact covIv (by simp))
    (by rw [x.esi, add0, hd, x.regs]; exact covBlk hk (by simp))
    (by rw [x.ebx, add0, x.wr, hp.wr]; exact covIv (by simp)) fun s₆ g₆ => ?_
  have m₆ : s₆.mem = Proof.Cmac.xor4Mem s₄.mem ((Iv s₀).setWidth 64) ((Iv s₀).setWidth 64) (blk s₀ k) := by
    rw [g₆.mem, x.ebx, x.esi, add0, add0, hd]
  have f₆ : Frame [ivR s₀] s₄.mem s₆.mem := by rw [m₆]; exact Proof.Cmac.xor4Mem_frame _ _ _ _
  have b₆ : bytesAt s₆.mem (blk s₀ k) 16 = bytesAt s₄.mem (blk s₀ k) 16 :=
    Proof.Cmac.bytesAt_frame f₆ (one (hp.blk_iv hk)) (by decide)
  have hb := h.block hk
  have i₆ : bytesAt s₆.mem ((Iv s₀).setWidth 64) 16 = (blks s₀)[k]'(by simp [Spec.Cbc.blocksAt]; exact hk) := by
    rw [m₆, xorIn4_bytes _ (hp.blk_iv hk).symm, x.blk, hb]
    exact xor_xor_cancel (by simp [Spec.Aes.bytesAt, ← hb])
  have newBlk : bytesAt s₆.mem (blk s₀ k) 16 =
      Spec.Cbc.xor ((blks s₀)[k]'(by simp [Spec.Cbc.blocksAt]; exact hk))
        (Spec.Cbc.aesWith (R s₀) (wK s₀) (chainK (cfbMode false) s₀ k)) := by
    rw [b₆, x.blk, hb, x.iv, h.iv]
  have outSucc :
      outK (cfbMode false) s₀ (k + 1) = outK (cfbMode false) s₀ k ++ [bytesAt s₆.mem (blk s₀ k) 16] := by
    rw [newBlk]
    simp only [outK, chainK, cfbMode_out, cfbMode_chain, cfb, cts, Bool.false_eq_true, ite_false,
      take_succ_blks s₀ hk, decrypt_snoc]
  refine linv_succ hp hk h x (fun r h₁ h₂ => g₆.gpr r h₁ h₂) g₆.rd g₆.wr f₆ outSucc ?_
  rw [i₆]
  simp only [chainK, cfbMode_chain, cts, Bool.false_eq_true, ite_false, take_succ_blks s₀ hk, next_snoc]

/-! ## Constant time -/

theorem pre_taint : ∃ h, (taint.check (argTaint [.esi] (4 + 4 * 6)) (.block ivArgs) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem encPost_taint : ∃ h, (taint.check (argTaint [.esi] (4 + 4 * 6)) (.block encPost) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem decPost_taint : ∃ h, (taint.check (argTaint [.esi] (4 + 4 * 6)) (.block decPost) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem encBody_ct (v : BlocksImpl) : BodyCt (cfbMode true) (body v.enc encPost) :=
  fun hp hp' hq k => VG.Proof.AesCbc.X86.body_ct (D := fun s₀ _ => Iv s₀) (fun hq _ => pub_arg hq (by decide))
    v.encOk v.encCt v.encNosp v.encStack pre_taint encPost_taint
    (@fun _ hp _ hk _ h => WP.mono (ivA_wp hp h) fun _ a => mid_of hp hk h a) hp hp' hq k

theorem decBody_ct (v : BlocksImpl) : BodyCt (cfbMode false) (body v.enc decPost) :=
  fun hp hp' hq k => VG.Proof.AesCbc.X86.body_ct (D := fun s₀ _ => Iv s₀) (fun hq _ => pub_arg hq (by decide))
    v.encOk v.encCt v.encNosp v.encStack pre_taint decPost_taint
    (@fun _ hp _ hk _ h => WP.mono (ivA_wp hp h) fun _ a => mid_of hp hk h a) hp hp' hq k

end VG.Proof.AesCfb.X86
