module

public import VerifiedGarbage.Impl.AesCfb.X86
public import VerifiedGarbage.Proof.AesCfb.Rounds
public import VerifiedGarbage.Proof.Aes.X86.BlocksVariant
public import VerifiedGarbage.Spec.Cfb.Contract
import VerifiedGarbage.Proof.AesCbc.X86.Verified
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Aes.X86.AesNi.Lit
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.AesCfb.Spec
import VerifiedGarbage.Proof.AesOfb.X86.Body
public import VerifiedGarbage.Proof.AesCbc.X86.CT
import VerifiedGarbage.Proof.CmacAes.X86.UpdateLoop
import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.AesCfb.Spec
meta import VerifiedGarbage.Proof.AesOfb.X86.Body
meta import VerifiedGarbage.Impl.AesCfb.X86
meta import VerifiedGarbage.Proof.AesCbc.X86.CT
meta import VerifiedGarbage.Proof.CmacAes.X86.UpdateLoop
meta import VerifiedGarbage.Proof.Cmac.Frame
public import VerifiedGarbage.Proof.AesCbc.X86.Wiped
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.AesCbc.X86.Decrypt
import VerifiedGarbage.Proof.CmacAes.X86.UpdateCorrect
import VerifiedGarbage.Proof.Aes.X86.AesNi.Rounds
import VerifiedGarbage.Proof.Framework.X86.Reduce
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
import VerifiedGarbage.Proof.Framework.X86.SseTaint
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.SpTest
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.AesCbc.X86.Wiped
meta import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.AesCbc.X86.Decrypt
meta import VerifiedGarbage.Proof.AesCbc.X86.Verified
meta import VerifiedGarbage.Proof.CmacAes.X86.UpdateCorrect
meta import VerifiedGarbage.Proof.Aes.X86.AesNi.Rounds
meta import VerifiedGarbage.Proof.Framework.X86.Reduce
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.SpTest
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Contract

/-! ### `AesCfb.X86.Body`, which this module and modules that import it used -/

section

/-!
# AES-CFB128 on x86: one block, and constant time

`encBody_ok` and `decBody_ok`: one run of `body` takes the loop invariant
AES-CBC's proofs share (`Proof/AesCbc/X86/Body.lean`) from `k` blocks to
`k + 1`, for `cfbMode`, for any implementation of the block functions
(`BlocksImpl`). The code before the call and the call are AES-OFB's
(`Proof/AesOfb/X86/Body.lean`). `encBody_ct` and `decBody_ct`: they are
constant time, by the shared framework, with the call on the block at `iv`.
-/

@[expose] public section

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
  obtain hd := hp.d32 hk
  obtain qN := hp.dataN hk
  have hdf := hp.data_fit
  have hiv := hp.iv_fit
  refine WP.seq (WP.mono (ivA_wp hp h) fun s₁ a => ?_)
  refine WP.seq (WP.mono (blk_call v.encOk v.encNosp v.encStack a.pre) fun s₂ c => ?_)
  obtain esp₁ : s₁.gpr .esp = E s₀ := by rw [a.esp, h.esp]
  obtain hb : below (s₁.gpr .esp) 24 = stkR s₀ := by rw [esp₁]; exact hp.below_eq
  obtain f₂ : Frame [ivR s₀, ⟨(S s₀).setWidth 64, 2048⟩, stkR s₀] s.mem s₂.mem := by
    obtain fr := c.frame; rw [hb, a.mem] at fr; exact fr
  obtain fs₂ : Frame [⟨blk s₀ k, 16⟩, ivR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stkR s₀] s.mem s₂.mem :=
    f₂.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact stepIn (.inr (.inl rfl))
      · exact stepIn (.inr (.inr (.inl (Region.sub_prefix (by decide)))))
      · exact stepIn (.inr (.inr (.inr rfl)))
  obtain big₂ : Frame (Big s₀) s₀.mem s₂.mem :=
    (UPre.big_of h.frame).trans ((stepFrame hk fs₂).sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨ivR s₀, by simp, fun _ h => h⟩
      · exact ⟨dataR s₀, by simp, fun _ h => h⟩
      · exact ⟨scrR s₀, by simp, Region.sub_prefix (by decide)⟩
      · exact ⟨stkR s₀, by simp, fun _ h => h⟩)
  obtain esi₂ : s₂.gpr .esi = D32 s₀ k := by rw [c.saved .esi (by simp [calleeSaved]), a.esi, h.esi]
  obtain esp₂ : s₂.gpr .esp = E s₀ := by rw [c.saved .esp (by simp [calleeSaved]), esp₁]
  obtain rw₂ : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [c.rd, c.wr, a.rd, a.wr, h.rd, h.wr]
  obtain rwl : s₂.rd ++ s₂.wr = [schR s₀, argsR s₀, ivR s₀, dataR s₀, scrR s₀] := by
    rw [rw₂, hp.rd, hp.wr]; rfl
  obtain w₂ : s₂.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [c.wr, a.wr, h.wr, hp.wr]
  rw [List.append_assoc, List.singleton_append]
  refine wp_arg (s₀ := s₀) esp₂ (by rw [rw₂]; exact hp.arg_in (by decide)) (hp.args_of big₂ 2 (by decide))
    fun s₃ u₃ => ?_
  have b₃ : s₃.gpr .ebx = Iv s₀ := u₃.gpr
  obtain i₃ : s₃.gpr .esi = D32 s₀ k := by rw [u₃.other _ (by decide), esi₂]
  refine xor4_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [i₃, qN]; omega_using [hk, hdf]) (by rw [b₃]; omega_using [hiv]) (by rw [i₃, qN]; omega_using [hk, hdf])
    (by rw [i₃, add0, hd, u₃.rd, u₃.wr, rwl]; exact covBlk hk (by simp))
    (by rw [b₃, add0, u₃.rd, u₃.wr, rwl]; exact covIv (by simp))
    (by rw [i₃, add0, hd, u₃.wr, w₂]; exact covBlk hk (by simp)) fun s₄ g₄ => hq s₄ ?_
  obtain m₄ : s₄.mem = Proof.Cmac.xor4Mem s₂.mem (blk s₀ k) (blk s₀ k) ((Iv s₀).setWidth 64) := by
    rw [g₄.mem, i₃, b₃, add0, add0, hd, u₃.mem]
  obtain f₄ : Frame [⟨blk s₀ k, 16⟩] s₂.mem s₄.mem := by rw [m₄]; exact Proof.Cmac.xor4Mem_frame _ _ _ _
  obtain big : Frame (Big s₀) s₀.mem s.mem := UPre.big_of h.frame
  obtain iv₄ : bytesAt s₄.mem ((Iv s₀).setWidth 64) 16 = bytesAt s₂.mem ((Iv s₀).setWidth 64) 16 :=
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
  obtain fStep : Frame [⟨blk s₀ k, 16⟩, ivR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stkR s₀] s.mem s₆.mem :=
    x.frame.trans (f₆.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact stepIn (.inr (.inl rfl)))
  obtain bigOf : Frame (Big s₀) s₀.mem s₆.mem := (UPre.big_of h.frame).trans ((stepFrame hk fStep).sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨ivR s₀, by simp, fun _ h => h⟩
    · exact ⟨dataR s₀, by simp, fun _ h => h⟩
    · exact ⟨scrR s₀, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨stkR s₀, by simp, fun _ h => h⟩)
  obtain hl' : (outK M s₀ k).length = k := by
    rw [outK, Mode.length_out]; simp [Spec.Cbc.blocksAt]; omega_using [hk]
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
  obtain hd := hp.d32 hk
  obtain qN := hp.dataN hk
  have hdf := hp.data_fit
  have hiv := hp.iv_fit
  rw [encPost_eq]
  refine head_ok v hp hk h _ fun s₄ x => ?_
  refine zero4_ok (by decide) (by rw [x.ebx]; omega_using [hiv]) (by rw [x.ebx, add0, x.wr, hp.wr]; exact covIv (by simp))
    fun s₅ g₅ m₅ rd₅ wr₅ => ?_
  obtain b₅ : s₅.gpr .ebx = Iv s₀ := by rw [g₅ _ (by decide), x.ebx]
  obtain i₅ : s₅.gpr .esi = D32 s₀ k := by rw [g₅ _ (by decide), x.esi]
  refine xor4_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [b₅]; omega_using [hiv]) (by rw [i₅, qN]; omega_using [hk, hdf]) (by rw [b₅]; omega_using [hiv])
    (by rw [b₅, add0, rd₅, wr₅, x.regs]; exact covIv (by simp))
    (by rw [i₅, add0, hd, rd₅, wr₅, x.regs]; exact covBlk hk (by simp))
    (by rw [b₅, add0, wr₅, x.wr, hp.wr]; exact covIv (by simp)) fun s₆ g₆ => ?_
  obtain m₆ : s₆.mem = copy4Mem s₄.mem ((Iv s₀).setWidth 64) (blk s₀ k) := by
    rw [g₆.mem, b₅, i₅, add0, add0, hd, m₅, x.ebx, add0]; rfl
  obtain f₆ : Frame [ivR s₀] s₄.mem s₆.mem := by rw [m₆]; exact copy4Mem_frame _ _ _
  obtain b₆ : bytesAt s₆.mem (blk s₀ k) 16 = bytesAt s₄.mem (blk s₀ k) 16 :=
    Proof.Cmac.bytesAt_frame f₆ (one (hp.blk_iv hk)) (by decide)
  obtain i₆ : bytesAt s₆.mem ((Iv s₀).setWidth 64) 16 = bytesAt s₆.mem (blk s₀ k) 16 := by
    rw [b₆, m₆, copy4Mem_bytes _ (hp.blk_iv hk).symm]
  obtain newBlk : bytesAt s₆.mem (blk s₀ k) 16 =
      Spec.Cbc.xor ((blks s₀)[k]'(by simp [Spec.Cbc.blocksAt]; exact hk))
        (Spec.Cbc.aesWith (R s₀) (wK s₀) (chainK (cfbMode true) s₀ k)) := by
    rw [b₆, x.blk, h.block hk, x.iv, h.iv]
  obtain outSucc :
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
  obtain hd := hp.d32 hk
  obtain qN := hp.dataN hk
  have hdf := hp.data_fit
  have hiv := hp.iv_fit
  rw [decPost_eq]
  refine head_ok v hp hk h _ fun s₄ x => ?_
  refine xor4_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [x.ebx]; omega_using [hiv]) (by rw [x.esi, qN]; omega_using [hk, hdf]) (by rw [x.ebx]; omega_using [hiv])
    (by rw [x.ebx, add0, x.regs]; exact covIv (by simp))
    (by rw [x.esi, add0, hd, x.regs]; exact covBlk hk (by simp))
    (by rw [x.ebx, add0, x.wr, hp.wr]; exact covIv (by simp)) fun s₆ g₆ => ?_
  obtain m₆ : s₆.mem = Proof.Cmac.xor4Mem s₄.mem ((Iv s₀).setWidth 64) ((Iv s₀).setWidth 64) (blk s₀ k) := by
    rw [g₆.mem, x.ebx, x.esi, add0, add0, hd]
  obtain f₆ : Frame [ivR s₀] s₄.mem s₆.mem := by rw [m₆]; exact Proof.Cmac.xor4Mem_frame _ _ _ _
  obtain b₆ : bytesAt s₆.mem (blk s₀ k) 16 = bytesAt s₄.mem (blk s₀ k) 16 :=
    Proof.Cmac.bytesAt_frame f₆ (one (hp.blk_iv hk)) (by decide)
  obtain hb := h.block hk
  obtain i₆ : bytesAt s₆.mem ((Iv s₀).setWidth 64) 16 = (blks s₀)[k]'(by simp [Spec.Cbc.blocksAt]; exact hk) := by
    rw [m₆, xorIn4_bytes _ (hp.blk_iv hk).symm, x.blk, hb]
    exact xor_xor_cancel (by simp [Spec.Aes.bytesAt, ← hb])
  obtain newBlk : bytesAt s₆.mem (blk s₀ k) 16 =
      Spec.Cbc.xor ((blks s₀)[k]'(by simp [Spec.Cbc.blocksAt]; exact hk))
        (Spec.Cbc.aesWith (R s₀) (wK s₀) (chainK (cfbMode false) s₀ k)) := by
    rw [b₆, x.blk, hb, x.iv, h.iv]
  obtain outSucc :
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

/-! ## Encryption with AES-NI

`Impl.AesCfb.X86.encryptNi`, which keeps the last ciphertext block in
`xmm0` and calls nothing, meets the contract that the code around a block
function meets (`modeX86 (cfbMode true)`). Its loop's invariant and
everything but one block are AES-OFB's (`Proof.AesOfb.X86.Ni.whole_wp`). -/

namespace VG.Proof.AesCfb.X86.Ni

open VG VG.X86 VG.X86.RegUpd
open VG.Impl.AesCfb.X86 (encNiBody encryptNi)
open VG.Impl.CmacAes.X86 (at_)
open VG.Proof.Aes.X86.AesNi (aes_ok st st_ext getD_ofFn getD_st byte_xor)
open VG.Proof.CmacAes.X86 (niKeys st_readW st_getD sub_one_ofNat add0' ea_at')
open VG.Proof.AesOfb.X86.Ni (NInv)
open VG.Proof.AesCbc
open VG.Proof.AesCbc.X86
open VG.Spec.Aes (bytesAt)

/-- `pxor` of an enciphered block with a data block is §6.3's `Pⱼ ⊕ Oⱼ`. -/
private theorem st_xor (o d : BitVec 128) :
    (st (XBinOp.eval .pxor o d)).toList = Spec.Cbc.xor (st d).toList (st o).toList := by
  apply Proof.Cmac.ext16 (by simp) (by simp [Spec.Cbc.xor])
  intro i hi
  rw [st_getD _ hi, xor_eq, Proof.Cmac.getD_xor (by simp) (by simpa using hi), st_getD d hi, st_getD o hi]
  exact (byte_xor o d i).trans (BitVec.xor_comm _ _)

/-- One block. -/
private theorem body_wp {s₀ : State} (hp : UPre s₀) {m : Mem}
    (hm : Frame [ivR s₀, dataR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stkR s₀] (savedMem s₀) m) {k : Nat}
    (hk : k < N s₀) {s : State} (h : NInv (cfbMode true) s₀ m k s) :
    WP isa encNiBody s fun s' =>
      NInv (cfbMode true) s₀ m (k + 1) s' ∧ s'.zf = some (decide (k + 1 = N s₀)) := by
  obtain big : Frame (Big s₀) s₀.mem s.mem := (UPre.big_of hm).trans (h.frame.mono (by simp))
  obtain hdf := hp.data_fit
  obtain cB : (dataR s₀).Contains (blk s₀ k) 16 :=
    Offset.contains_base _ (by omega_using [hk]) (by omega_using [hdf, hk])
  obtain hK := niKeys (s := s) (nr := R s₀) (by rcases hp.rounds with h | h | h <;> omega_using [h]) hp.sch_fit h.eax
    (by rw [h.rd]; simp [hp.rd])
  rw [UPre.sched_bytes hp big] at hK
  -- The last ciphertext block enciphered in `xmm0`.
  refine WP.seq (WP.mono (aes_ok [.xmm0] (by decide) (by decide) hp.rounds s hK h.ecx) fun s₂ ⟨c₂, f₂⟩ => ?_)
  obtain ⟨o, ho⟩ : ∃ o, s₂.xmm .xmm0 = o := ⟨_, rfl⟩
  obtain newOut : (st o).toList = Spec.Cbc.aesWith (R s₀) (wK s₀) (chainK (cfbMode true) s₀ k) := by
    rw [← ho, c₂ _ List.mem_cons_self, ← h.chain]
    exact congrArg (fun y => (Spec.Aes.cipher (R s₀) _ y).toList) (st_ext fun i hi => by
      rw [getD_ofFn hi]
      exact (st_getD _ hi).trans (getD_st _ hi).symm).symm
  obtain ea₂ : s₂.ea (at_ .esi 0) = blk s₀ k := by
    rw [ea_at', f₂.gpr, h.esi]
    show (Dp s₀ + BitVec.ofNat 32 (16 * k) + BitVec.ofNat 32 0).setWidth 64 = _
    rw [add0']
    exact hp.dataA hk
  obtain hin : InRegions (s₂.rd ++ s₂.wr) (blk s₀ k) 16 := by
    rw [f₂.wr, h.wr]
    exact ⟨dataR s₀, by simp [hp.wr], cB⟩
  -- The data block through `xmm7` XORed into it, and the ciphertext block stored.
  obtain ⟨d, hd⟩ : ∃ d, s₂.mem.readW (blk s₀ k) 128 = d := ⟨_, rfl⟩
  obtain ⟨x, hx⟩ : ∃ x, XBinOp.eval .pxor o d = x := ⟨_, rfl⟩
  obtain ⟨s₃, hs₃⟩ : ∃ s₃, (s₂.setXmm .xmm7 d).setXmm .xmm0
    (XBinOp.eval .pxor ((s₂.setXmm .xmm7 d).xmm .xmm0) ((s₂.setXmm .xmm7 d).xmm .xmm7)) = s₃ := ⟨_, rfl⟩
  rw [WP.block_cons_iff]
  refine ⟨s₂.setXmm .xmm7 d, by
    simp only [isa, reduceExec, State.load128, ea₂, hin, ite_true, Option.map_some, hd], ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨s₃, hs₃ ▸ rfl, ?_⟩
  obtain x₃ : s₃.xmm .xmm0 = x := by
    rw [← hs₃, xmm_setXmm_self, xmm_setXmm_self, xmm_setXmm_of_ne _ _ (by decide), ho, hx]
  obtain g₃ : s₃.gpr = s.gpr := by rw [← hs₃, gpr_setXmm, gpr_setXmm, f₂.gpr]
  obtain m₃ : s₃.mem = s.mem := by rw [← hs₃, mem_setXmm, mem_setXmm, f₂.mem]
  obtain rd₃ : s₃.rd = s₀.rd := by rw [← hs₃, rd_setXmm, rd_setXmm, f₂.rd, h.rd]
  obtain wr₃ : s₃.wr = s₀.wr := by rw [← hs₃, wr_setXmm, wr_setXmm, f₂.wr, h.wr]
  obtain ea₃ : s₃.ea (at_ .esi 0) = blk s₀ k := by rw [← ea₂]; simp only [State.ea, g₃, f₂.gpr]
  obtain hout : InRegions s₃.wr (blk s₀ k) 16 := by
    rw [wr₃]
    exact ⟨dataR s₀, by simp [hp.wr], cB⟩
  obtain ⟨s₄, hs₄⟩ : ∃ s₄ : State, { s₃ with mem := s₃.mem.writeW (blk s₀ k) x } = s₄ := ⟨_, rfl⟩
  rw [WP.block_cons_iff]
  refine ⟨s₄, by simp only [isa, reduceExec, State.store128, ea₃, hout, ite_true, x₃, hs₄], ?_⟩
  obtain g₄ : s₄.gpr = s.gpr := by rw [← hs₄]; exact g₃
  obtain m₄ : s₄.mem = s.mem.writeW (blk s₀ k) x := by rw [← hs₄, ← m₃]
  obtain rd₄ : s₄.rd = s₀.rd := by rw [← hs₄]; exact rd₃
  obtain wr₄ : s₄.wr = s₀.wr := by rw [← hs₄]; exact wr₃
  obtain x₄ : s₄.xmm .xmm0 = x := by rw [← hs₄]; exact x₃
  -- The new block, which is the next chaining value, and the blocks after it.
  obtain fw : Frame [⟨blk s₀ k, 16⟩] s.mem s₄.mem := by
    rw [m₄]
    exact (Frame.refl _ _).writeW (r := ⟨blk s₀ k, 16⟩) List.mem_cons_self _ (Region.contains_self _ _)
  obtain nb : bytesAt s₄.mem (blk s₀ k) 16 = (st x).toList := by
    rw [m₄, ← st_readW, Mem.readW_writeW_self _ _ 16 _ (by decide)]
  obtain hl' : (outK (cfbMode true) s₀ k).length = k := by
    rw [outK, Mode.length_out]; simp [Spec.Cbc.blocksAt]; omega_using [hk]
  obtain newBlk : (st x).toList =
      Spec.Cbc.xor ((blks s₀)[k]'(by simp [Spec.Cbc.blocksAt]; exact hk)) (st o).toList := by
    rw [← hx, ← block_of_data h.data hk, ← st_readW, ← f₂.mem, hd]
    exact st_xor o d
  obtain outSucc : outK (cfbMode true) s₀ (k + 1) = outK (cfbMode true) s₀ k ++ [(st x).toList] := by
    rw [newBlk, newOut]
    simp only [outK, chainK, cfbMode_out, cfbMode_chain, cfb, cts, ite_true, take_succ_blks s₀ hk,
      encrypt_snoc]
  obtain hpos : 0 < N s₀ - k := by omega_using [hk]
  obtain edi' : s.gpr .edi - 1 = BitVec.ofNat 32 (N s₀ - (k + 1)) := by
    rw [h.edi, sub_one_ofNat hpos]; rfl
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, reduceExec, execAlu, readSrc, isa, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;>
    simp only [gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg,
      wr_arithFlags, xmm_setReg, xmm_arithFlags, zf_setReg, zf_arithFlags, reduceCtorEq, ↓reduceIte, g₄]
  · rw [h.esi, BitVec.add_assoc]
    exact congrArg (Dp s₀ + ·) (BitVec.ofNat_add ..).symm
  · exact edi'
  · exact h.eax
  · exact h.ecx
  · exact h.edx
  · exact h.esp
  · exact rd₄
  · exact wr₄
  · rw [m₄]
    exact h.frame.writeW (r := dataR s₀) List.mem_cons_self _ cB
  · rw [hp.blocksAt_step hk (fw.mono (by simp)), nb, h.data, outSucc,
      set_prefix _ _ _ hl' (by simp [Spec.Cbc.blocksAt]; exact hk)]
  · rw [x₄]
    simp only [chainK, cfbMode_chain, cts, ite_true, outSucc, next_snoc]
  · rw [edi', MdStream.X86.ofNat_beq_zero (by have : N s₀ < 2 ^ 32 := (arg s₀ 4).isLt; omega_using [this])]
    exact congrArg some (decide_eq_decide.mpr (by omega_using [hk]))

/-- It runs to the contract's postcondition, as the code around a block
function does (`whole_wp`). -/
theorem correct (s : State) (hs : (modeX86 (cfbMode true)).pre s) :
    ∃ t s', Exec isa encryptNi s t s' ∧ abiPreserved s s' ∧ (modeX86 (cfbMode true)).post s s' :=
  (Proof.AesOfb.X86.Ni.whole_wp (fun hp _ hm _ hk _ h => body_wp hp hm hk h) hs).mono fun _ h => ⟨h.1, h.2.1⟩

theorem ct : ConstantTime isa (modeX86 (cfbMode true)).pre (modeX86 (cfbMode true)).pub encryptNi :=
  VG.Taint.constantTime (A := sseTaint) Decrypt.τ₀
    (fun _ _ h₁ h₂ hp => Decrypt.agree₀ (UPre.of h₁) (UPre.of h₂) hp) (by taint_decide)

/-- It writes `esp` nowhere: it has no frame and no call. -/
theorem noSp : NoSp encryptNi := NoSp.of_all (by lit_decide)

theorem stack : stackUse encryptNi = 0 := by lit_decide

theorem spSafe : encryptNi.all (fun i => !isa.writesSp i) = true := Code.all_of_spTest (by lit_decide)

end VG.Proof.AesCfb.X86.Ni

end

end

/-!
# AES-CFB128 on x86: `Verified`

Correctness and constant time (for any implementation `v` of the block
functions), from the loop AES-CBC's proofs share, a state satisfying the
precondition, and the shared contracts of `Spec/Cfb/Contract.lean`, with 24
bytes of stack: each call of a block function pushes its five arguments and
the return address.

The whole-block code of encryption for `v` is `encryptCode v`: with AES-NI
(`hardware`, as AES-CBC and AES-OFB choose their code), the loop that keeps
the last ciphertext block in a register and calls nothing
(`Impl.AesCfb.X86.encryptNi`, `Ni` above), which needs none of those 24
bytes; for any other implementation, `encrypt` around its block function.
Both meet the same contract (`encryptCode_verified`).
-/

@[expose] public section

namespace VG.Proof.AesCfb.X86

open VG VG.X86 VG.Impl.AesCfb.X86
open VG.Proof.AesCbc.X86.Wiped (hardware)
open VG.Impl.AesCbc.X86 (whole blkCall)
open VG.Impl.AesOfb.X86 (ivArgs)
open VG.Proof.AesCbc (cts)
open VG.Proof.AesCbc.X86
open VG.Proof.Aes.X86 (BlocksImpl)

theorem encrypt_spSafe (v : BlocksImpl) : (encrypt v.enc).all (fun i => !isa.writesSp i) = true := by
  simp only [encrypt, whole, body, blkCall, Code.all, v.encSpSafe]
  decide +kernel

theorem decrypt_spSafe (v : BlocksImpl) : (decrypt v.enc).all (fun i => !isa.writesSp i) = true := by
  simp only [decrypt, whole, body, blkCall, Code.all, v.encSpSafe]
  decide +kernel

/-- The shared contract of encryption, from the code's own
(`modeX86 (cfbMode true)`). -/
theorem encrypt_implies :
    (modeX86 (cfbMode true)).Implies (Proof.AesCfb.encryptRoundsContract X86.abi 24) := by
  have a0 : arg sat 0 = 0x1000 := by decide
  have a1 : arg sat 1 = 10 := by decide
  have a2 : arg sat 2 = 0x2000 := by decide
  have a3 : arg sat 3 = 0x3000 := by decide
  have a4 : arg sat 4 = 0 := by decide
  have a5 : arg sat 5 = 0x4000 := by decide
  have e : argAddr sat 0 = 0x8004 := by decide
  have esp : sat.gpr .esp = 0x8000 := rfl
  sig_implies [Proof.AesCfb.encryptRoundsContract, Spec.Cfb.aesSig, Spec.Cbc.aesSig, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes, modeX86, cfbMode, cfb, cts] [a0, a1, a2, a3, a4, a5, e, esp] using sat

theorem encrypt_verified (v : BlocksImpl) :
    Verified X86.target (encrypt v.enc) (Proof.AesCfb.encryptRoundsContract X86.abi 24) :=
  Verified.of_correct (fun _ hs => whole_wp (encBody_ok v) hs) (whole_ct (encBody_ok v) (encBody_ct v))
    encrypt_implies

/-! ## The code of encryption of each implementation -/

/-- The whole-block code of encryption for `v`: with AES-NI, the loop that
keeps the last ciphertext block in a register with no call
(`Impl.AesCfb.X86.encryptNi`); for any other implementation, `encrypt`
around its block function. -/
def encryptCode (v : BlocksImpl) : Prog isa := if hardware v then encryptNi else encrypt v.enc

/-- `encryptCode v` runs to the code's own contract. -/
theorem encryptCode_correct (v : BlocksImpl) (s : State) (hs : (modeX86 (cfbMode true)).pre s) :
    ∃ t s', Exec isa (encryptCode v) s t s' ∧ abiPreserved s s' ∧ (modeX86 (cfbMode true)).post s s' := by
  unfold encryptCode
  split
  · exact Ni.correct s hs
  · exact whole_wp (encBody_ok v) hs

theorem encryptCode_ct (v : BlocksImpl) :
    ConstantTime isa (modeX86 (cfbMode true)).pre (modeX86 (cfbMode true)).pub (encryptCode v) := by
  unfold encryptCode
  split
  · exact Ni.ct
  · exact whole_ct (encBody_ok v) (encBody_ct v)

theorem encryptCode_verified (v : BlocksImpl) :
    Verified X86.target (encryptCode v) (Proof.AesCfb.encryptRoundsContract X86.abi 24) :=
  Verified.of_correct (encryptCode_correct v) (encryptCode_ct v) encrypt_implies

theorem encryptCode_spSafe (v : BlocksImpl) : (encryptCode v).all (fun i => !isa.writesSp i) = true := by
  unfold encryptCode
  split
  · exact Ni.spSafe
  · exact encrypt_spSafe v

theorem decrypt_verified (v : BlocksImpl) :
    Verified X86.target (decrypt v.enc) (Proof.AesCfb.decryptRoundsContract X86.abi 24) :=
  Verified.of_correct (fun _ hs => whole_wp (decBody_ok v) hs) (whole_ct (decBody_ok v) (decBody_ct v)) (by
    have a0 : arg sat 0 = 0x1000 := by decide
    have a1 : arg sat 1 = 10 := by decide
    have a2 : arg sat 2 = 0x2000 := by decide
    have a3 : arg sat 3 = 0x3000 := by decide
    have a4 : arg sat 4 = 0 := by decide
    have a5 : arg sat 5 = 0x4000 := by decide
    have e : argAddr sat 0 = 0x8004 := by decide
    have esp : sat.gpr .esp = 0x8000 := rfl
    sig_implies [Proof.AesCfb.decryptRoundsContract, Spec.Cfb.aesSig, Spec.Cbc.aesSig, X86.abi, X86.argSlots,
      X86.argVal, X86.argBytes, modeX86, cfbMode, cfb, cts] [a0, a1, a2, a3, a4, a5, e, esp] using sat)

end VG.Proof.AesCfb.X86
