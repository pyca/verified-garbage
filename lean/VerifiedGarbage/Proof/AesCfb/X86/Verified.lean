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
import VerifiedGarbage.Proof.Aes.X86.AesNi.BlocksLoop
import VerifiedGarbage.Proof.Aes.X86.AesNi.BlocksMain
meta import VerifiedGarbage.Proof.Aes.X86.AesNi.BlocksLoop
meta import VerifiedGarbage.Proof.Aes.X86.AesNi.BlocksMain

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

/-! ## Decryption with AES-NI

`Impl.AesCfb.X86.decryptNi`, which enciphers the blocks before six
ciphertext blocks at a time, and then those before the blocks left as a
group of three, a group of two and one block, calling nothing, meets the
contract that the code around a block function meets
(`modeX86 (cfbMode false)`). After each group the last of its ciphertext
blocks is at `iv` (`DInv`); the groups' counts are those of
`vg_aes_decrypt_blocks_aesni` (`Proof/Aes/X86/AesNi/BlocksMain.lean`). -/

namespace VG.Proof.AesCfb.X86.NiDec

open VG VG.X86 VG.X86.RegUpd
open VG.Impl.AesCfb.X86 (decNiLoad decNiXor decNiGroup decNi6 decNi3 decNiBit decNiPre decNiTail decNiMid
  decryptNi)
open VG.Impl.CmacAes.X86 (at_ argOp)
open VG.Impl.Aes.X86.AesNi (loadData regs6 regs3 regs2 regs1)
open VG.Proof.Aes.X86.AesNi (aes_ok st st_ext getD_ofFn getD_st loadData_ok)
open VG.Proof.Aes.X86.AesNi.Ecb (Lanes regs_nodup bit_lt)
open VG.Proof.Aes.X86 (in_rd addr_zero addr_add)
open VG.Proof.CmacAes.X86 (niKeys st_readW st_getD wp_arg arg_ofNat ea_at')
open VG.X86.Wp (wp_addi wp_subi wp_cmpi toNat_ofNat_lt ofNat_beq_zero Fupd)
open VG.Proof.AesCbc
open VG.Proof.AesCbc.X86
open VG.Proof.AesCbc.X86.Decrypt (x_load)
open VG.Spec.Aes (bytesAt)

/-- The chaining value after block `k` is ciphertext block `k`. -/
private theorem chain_succ (s₀ : State) {k : Nat} (hk : k < N s₀) :
    chainK (cfbMode false) s₀ (k + 1) = (blks s₀)[k]'(by simp [Spec.Cbc.blocksAt]; exact hk) := by
  simp only [chainK, cfbMode_chain, cts, Bool.false_eq_true, ite_false, take_succ_blks s₀ hk, next_snoc]

/-- The output after block `k`: §6.3's `Pⱼ = Cⱼ ⊕ CIPH_K(Cⱼ₋₁)` more. -/
private theorem out_succ (s₀ : State) {k : Nat} (hk : k < N s₀) :
    outK (cfbMode false) s₀ (k + 1) = outK (cfbMode false) s₀ k ++
      [Spec.Cbc.xor ((blks s₀)[k]'(by simp [Spec.Cbc.blocksAt]; exact hk))
        (Spec.Cbc.aesWith (R s₀) (wK s₀) (chainK (cfbMode false) s₀ k))] := by
  simp only [outK, chainK, cfbMode_out, cfbMode_chain, cfb, cts, Bool.false_eq_true, ite_false,
    take_succ_blks s₀ hk, decrypt_snoc]

/-- The cipher of a register's block, as the mode states it. -/
private theorem aes_list {nr : Nat} {w : List Byte} {x : BitVec 128} {l : List Byte} (h : (st x).toList = l) :
    (Spec.Aes.cipher nr w (st x)).toList = Spec.Cbc.aesWith nr w l := by
  subst h
  exact congrArg (fun y => (Spec.Aes.cipher nr w y).toList) (st_ext fun i hi => by
    rw [getD_ofFn hi]
    exact (st_getD _ hi).trans (getD_st _ hi).symm).symm

/-- `movdqu [b + o], x`, keeping the SSE registers. -/
private theorem x_store' {is : List Instr} {s : State} {Q : State → Prop} {x : XReg} {b : Reg} {B : BitVec 32}
    {o : Nat} (hb : s.gpr b = B) (hout : InRegions s.wr (addr B o) 16)
    (k : WP isa (.block is) { s with mem := s.mem.writeW (addr B o) (s.xmm x) } Q) :
    WP isa (.block (.movdquStore (at_ b o) x :: is)) s Q :=
  Wp.cons (by simp only [reduceExec, State.store128, ea_at', hb, hout, ↓reduceIte]) k

/-- A block's ciphertext into `xmm7`, XORed into the register `b`, which is
stored over it. -/
private theorem xor1_ok (b : XReg) (j : Nat) (s : State) (hb : b ≠ .xmm7)
    (hin : InRegions s.wr (addr (s.gpr .esi) (16 * j)) 16) :
    WP isa (.block [.movdquLoad .xmm7 (at_ .esi (16 * j)), .xop (.bin .pxor b .xmm7),
      .movdquStore (at_ .esi (16 * j)) b]) s fun t =>
      t.mem = s.mem.writeW (addr (s.gpr .esi) (16 * j))
        (XBinOp.eval .pxor (s.xmm b) (s.mem.readW (addr (s.gpr .esi) (16 * j)) 128)) ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ (∀ r, r ≠ b → r ≠ .xmm7 → t.xmm r = s.xmm r) := by
  have hin' : InRegions (s.rd ++ s.wr) (addr (s.gpr .esi) (16 * j)) 16 := in_rd hin
  apply WP.of_runBlock
  simp only [↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, reduceExec, XOp.exec, isa,
    State.load128, State.store128, ea_at', gpr_setXmm, mem_setXmm, rd_setXmm, wr_setXmm, xmm_setXmm,
    hin, hin', hb, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, trivial, trivial, fun r h1 h2 => ?_⟩
  simp only [h1, h2, ite_false]

/-- Writing the block at `iv` leaves the data. -/
private theorem data_iv {s₀ : State} (hp : UPre s₀) {m m' : Mem} (hf : Frame [ivR s₀] m m') :
    Spec.Cbc.blocksAt m' ((Dp s₀).setWidth 64) (N s₀) = Spec.Cbc.blocksAt m ((Dp s₀).setWidth 64) (N s₀) := by
  simp only [Spec.Cbc.blocksAt]
  refine List.map_congr_left fun j hj => Proof.Cmac.bytesAt_frame hf (fun r hr => ?_) (by decide)
  simp only [List.mem_singleton] at hr; subst hr
  exact hp.iv_data.symm.sub_left (UPre.data_sub (List.mem_range.mp hj))

/-- A block not yet deciphered is the ciphertext block. -/
private theorem block_ge {s₀ : State} {m : Mem} {c k : Nat}
    (hd : Spec.Cbc.blocksAt m ((Dp s₀).setWidth 64) (N s₀) = outK (cfbMode false) s₀ c ++ (blks s₀).drop c)
    (hc : c ≤ k) (hk : k < N s₀) :
    bytesAt m (blk s₀ k) 16 = (blks s₀)[k]'(by simp [Spec.Cbc.blocksAt]; exact hk) := by
  have hl : (outK (cfbMode false) s₀ c).length = c := by
    rw [outK, Mode.length_out]; simp [Spec.Cbc.blocksAt]; omega_using [hc, hk]
  have h := congrArg (·[k]?) hd
  simp only [List.getElem?_eq_getElem (show k < (Spec.Cbc.blocksAt m ((Dp s₀).setWidth 64) (N s₀)).length by
      rw [length_blocksAt]; exact hk),
    List.getElem?_append_right (show (outK (cfbMode false) s₀ c).length ≤ k by omega_using [hl, hc]), hl,
    List.getElem?_drop, show c + (k - c) = k by omega_using [hc],
    List.getElem?_eq_getElem (show k < (blks s₀).length by simp [Spec.Cbc.blocksAt]; exact hk)] at h
  show bytesAt m ((Dp s₀).setWidth 64 + BitVec.ofNat 64 (16 * k)) 16 = _
  rw [← getElem_blocksAt _ _ hk]
  exact Option.some.inj h

/-- After `c` blocks, with `esi` at block `p` and `edi` the number of blocks
from block `q` on: since the prologue left the memory `m`, only the block at
`iv` and the data have changed; the first `c` blocks are deciphered, and the
block at `iv` is the chaining value after them. -/
structure DInv (s₀ : State) (m : Mem) (c p q : Nat) (s : State) : Prop where
  le : c ≤ N s₀
  esi : s.gpr .esi = Dp s₀ + BitVec.ofNat 32 (16 * p)
  edi : s.gpr .edi = BitVec.ofNat 32 (N s₀ - q)
  eax : s.gpr .eax = W s₀
  ecx : s.gpr .ecx = BitVec.ofNat 32 (R s₀)
  edx : s.gpr .edx = Iv s₀
  esp : s.gpr .esp = E s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [ivR s₀, dataR s₀] m s.mem
  data : Spec.Cbc.blocksAt s.mem ((Dp s₀).setWidth 64) (N s₀) = outK (cfbMode false) s₀ c ++ (blks s₀).drop c
  iv : bytesAt s.mem ((Iv s₀).setWidth 64) 16 = chainK (cfbMode false) s₀ c

/-- `DInv` is kept by moving `esi` and `edi`, and changing the flags. -/
theorem DInv.move {s₀ : State} {m : Mem} {c p q p' q' : Nat} {s t : State} (hI : DInv s₀ m c p q s)
    (hg : ∀ r, r ≠ .esi → r ≠ .edi → t.gpr r = s.gpr r)
    (hesi : t.gpr .esi = Dp s₀ + BitVec.ofNat 32 (16 * p')) (hedi : t.gpr .edi = BitVec.ofNat 32 (N s₀ - q'))
    (hm : t.mem = s.mem) (hr : t.rd = s.rd) (hw : t.wr = s.wr) : DInv s₀ m c p' q' t :=
  { le := hI.le
    esi := hesi
    edi := hedi
    eax := by rw [hg _ (by decide) (by decide), hI.eax]
    ecx := by rw [hg _ (by decide) (by decide), hI.ecx]
    edx := by rw [hg _ (by decide) (by decide), hI.edx]
    esp := by rw [hg _ (by decide) (by decide), hI.esp]
    rd := by rw [hr, hI.rd]
    wr := by rw [hw, hI.wr]
    frame := by rw [hm]; exact hI.frame
    data := by rw [hm]; exact hI.data
    iv := by rw [hm]; exact hI.iv }

/-- `DInv` is kept by changing the flags. -/
theorem DInv.fupd {s₀ : State} {m : Mem} {c p q : Nat} {s t : State} (hI : DInv s₀ m c p q s)
    (u : Fupd s t) : DInv s₀ m c p q t :=
  hI.move (fun r _ _ => by rw [u.gpr]) (by rw [u.gpr, hI.esi]) (by rw [u.gpr, hI.edi]) u.mem u.rd u.wr

/-- The registers' blocks XORed with their own ciphertext, in order, and
stored: blocks `c + j` on. -/
private theorem xorData_ok {s₀ : State} (hp : UPre s₀) {c : Nat} :
    ∀ (rs : List XReg) (j : Nat) (s : State), rs.Nodup → .xmm7 ∉ rs →
    (∀ k, c + k < N s₀ → addr (s.gpr .esi) (16 * k) = blk s₀ (c + k)) →
    c + j + rs.length ≤ N s₀ → s.wr = s₀.wr →
    Spec.Cbc.blocksAt s.mem ((Dp s₀).setWidth 64) (N s₀) =
      outK (cfbMode false) s₀ (c + j) ++ (blks s₀).drop (c + j) →
    (∀ k (h : k < rs.length), (st (s.xmm rs[k])).toList =
      Spec.Cbc.aesWith (R s₀) (wK s₀) (chainK (cfbMode false) s₀ (c + j + k))) →
    WP isa (.block (decNiXor rs j)) s fun t =>
      Spec.Cbc.blocksAt t.mem ((Dp s₀).setWidth 64) (N s₀) =
        outK (cfbMode false) s₀ (c + j + rs.length) ++ (blks s₀).drop (c + j + rs.length) ∧
      Frame [dataR s₀] s.mem t.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr
  | [], _, s, _, _, _, _, _, hd, _ => WP.block_nil ⟨hd, Frame.refl _ _, rfl, rfl, rfl⟩
  | b :: bs, j, s, hnd, h7, ha, hc, hw, hd, hv => by
    have hb : b ≠ .xmm7 := fun h => h7 (h ▸ List.mem_cons_self)
    have hbs : b ∉ bs := (List.nodup_cons.mp hnd).1
    have h7' : .xmm7 ∉ bs := fun h => h7 (List.mem_cons_of_mem _ h)
    simp only [List.length_cons] at hc
    obtain hk : c + j < N s₀ := by omega_using [hc]
    obtain ea : addr (s.gpr .esi) (16 * j) = blk s₀ (c + j) := ha j hk
    obtain hdf := hp.data_fit
    obtain cB : (dataR s₀).Contains (blk s₀ (c + j)) 16 :=
      Offset.contains_base _ (by omega_using [hk]) (by omega_using [hdf, hk])
    obtain hdat : dataR s₀ ∈ s₀.wr := by rw [hp.wr]; exact List.mem_cons_of_mem _ List.mem_cons_self
    rw [decNiXor, WP.block_append_iff]
    refine WP.mono (xor1_ok b j s hb (by rw [ea, hw]; exact ⟨_, hdat, cB⟩)) fun t ⟨hm, hg, hr, hw', ho⟩ => ?_
    rw [ea] at hm
    obtain ⟨x, hx⟩ : ∃ x, XBinOp.eval .pxor (s.xmm b) (s.mem.readW (blk s₀ (c + j)) 128) = x := ⟨_, rfl⟩
    rw [hx] at hm
    obtain fD : Frame [dataR s₀] s.mem t.mem := by
      rw [hm]; exact (Frame.refl _ _).writeW (r := dataR s₀) List.mem_cons_self _ cB
    obtain fw : Frame [⟨blk s₀ (c + j), 16⟩] s.mem t.mem := by
      rw [hm]
      exact (Frame.refl _ _).writeW (r := ⟨blk s₀ (c + j), 16⟩) List.mem_cons_self _ (Region.contains_self _ _)
    obtain nb : bytesAt t.mem (blk s₀ (c + j)) 16 = (st x).toList := by
      rw [hm, ← st_readW, Mem.readW_writeW_self _ _ 16 _ (by decide)]
    obtain hl' : (outK (cfbMode false) s₀ (c + j)).length = c + j := by
      rw [outK, Mode.length_out]; simp [Spec.Cbc.blocksAt]; omega_using [hk]
    obtain h0 : (st (s.xmm b)).toList =
        Spec.Cbc.aesWith (R s₀) (wK s₀) (chainK (cfbMode false) s₀ (c + j)) := hv 0 (Nat.zero_lt_succ _)
    obtain outSucc : outK (cfbMode false) s₀ (c + j + 1) = outK (cfbMode false) s₀ (c + j) ++ [(st x).toList] := by
      rw [← hx, Ni.st_xor, st_readW, block_of_data hd hk, h0]
      exact out_succ s₀ hk
    obtain hd' : Spec.Cbc.blocksAt t.mem ((Dp s₀).setWidth 64) (N s₀) =
        outK (cfbMode false) s₀ (c + (j + 1)) ++ (blks s₀).drop (c + (j + 1)) := by
      rw [← Nat.add_assoc, hp.blocksAt_step hk (fw.mono (by simp)), nb, hd, outSucc,
        set_prefix _ _ _ hl' (by simp [Spec.Cbc.blocksAt]; exact hk)]
    refine WP.mono (xorData_ok hp bs (j + 1) t (List.nodup_cons.mp hnd).2 h7' (by rw [hg]; exact ha)
      (by omega_using [hc]) (hw'.trans hw) hd' (fun k hk' => by
        rw [ho _ (fun h => hbs (h ▸ List.getElem_mem hk')) (fun h => h7' (h ▸ List.getElem_mem hk')),
          show c + (j + 1) + k = c + j + (k + 1) by omega_using []]
        exact hv (k + 1) (Nat.succ_lt_succ hk'))) fun u ⟨hu, hf', hg', hr', hw''⟩ => ?_
    obtain he : c + (j + 1) + bs.length = c + j + (b :: bs).length := by
      rw [List.length_cons]; omega_using []
    rw [he] at hu
    exact ⟨hu, fD.trans hf', hg'.trans hg, hr'.trans hr, hw''.trans hw'⟩

/-- The cipher's inputs of a group into its registers, and its last
ciphertext block to `iv`. -/
private theorem load_ok {s₀ : State} (hp : UPre s₀) {m : Mem} {c q : Nat} {s : State} (hI : DInv s₀ m c c q s)
    (b : XReg) (bs : List XReg) (hnd : (b :: bs).Nodup) (h7 : .xmm7 ∉ b :: bs)
    (hc : c + (bs.length + 1) ≤ N s₀) :
    WP isa (.block (decNiLoad (b :: bs))) s fun t =>
      (∀ k (h : k < (b :: bs).length),
        (st (t.xmm (b :: bs)[k])).toList = chainK (cfbMode false) s₀ (c + k)) ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ Frame [ivR s₀] s.mem t.mem ∧
      bytesAt t.mem ((Iv s₀).setWidth 64) 16 = chainK (cfbMode false) s₀ (c + (bs.length + 1)) := by
  have hdf := hp.data_fit
  have hb7 : b ≠ .xmm7 := fun h => h7 (h ▸ List.mem_cons_self)
  have hbs : b ∉ bs := (List.nodup_cons.mp hnd).1
  have h7' : .xmm7 ∉ bs := fun h => h7 (List.mem_cons_of_mem _ h)
  obtain hdat : dataR s₀ ∈ s₀.wr := by rw [hp.wr]; exact List.mem_cons_of_mem _ List.mem_cons_self
  obtain hivw : ivR s₀ ∈ s₀.wr := by rw [hp.wr]; exact List.mem_cons_self
  obtain haddr : ∀ k, c + k < N s₀ → addr (s.gpr .esi) (16 * k) = blk s₀ (c + k) := fun k hk => by
    rw [hI.esi, addr_add, addr_eq (by omega_using [hdf, hk]), ← Nat.mul_add]
  obtain hinB : ∀ k, c + k < N s₀ → InRegions s.wr (blk s₀ (c + k)) 16 := fun k hk => by
    rw [hI.wr]
    exact ⟨dataR s₀, hdat, Offset.contains_base _ (by omega_using [hk]) (by omega_using [hdf, hk])⟩
  obtain hinI : InRegions s.wr ((Iv s₀).setWidth 64) 16 := by
    rw [hI.wr]; exact ⟨ivR s₀, hivw, Region.contains_self _ _⟩
  obtain hblk : ∀ k (hk : c + k < N s₀), bytesAt s.mem (blk s₀ (c + k)) 16 = chainK (cfbMode false) s₀ (c + k + 1) :=
    fun k hk => by rw [block_ge hI.data (Nat.le_add_right _ _) hk, chain_succ s₀ hk]
  -- The block at `iv` into the first register.
  obtain ⟨v0, hv0⟩ : ∃ v0, s.mem.readW (addr (Iv s₀) 0) 128 = v0 := ⟨_, rfl⟩
  obtain c0 : (st v0).toList = chainK (cfbMode false) s₀ c := by
    rw [← hv0, st_readW, addr_zero]; exact hI.iv
  show WP isa (.block (.movdquLoad b (at_ .edx 0) :: (loadData .esi bs 0 ++
    [.movdquLoad .xmm7 (at_ .esi (16 * bs.length)), .movdquStore (at_ .edx 0) .xmm7]))) s _
  refine x_load (B := Iv s₀) (o := 0) hI.edx (by rw [addr_zero]; exact in_rd hinI) ?_
  rw [hv0, WP.block_append_iff]
  -- The blocks but the last into the others.
  refine WP.mono (loadData_ok .esi bs 0 _ (List.nodup_cons.mp hnd).2 (fun k hk => by
      rw [gpr_setXmm, rd_setXmm, wr_setXmm, Nat.zero_add, haddr k (by omega_using [hc, hk])]
      exact in_rd (hinB k (by omega_using [hc, hk])))) fun u ⟨hl, gl, ml, rl, wl, xl⟩ => ?_
  rw [gpr_setXmm] at gl hl
  rw [mem_setXmm] at ml hl
  rw [rd_setXmm] at rl
  rw [wr_setXmm] at wl
  -- The last into `xmm7`, and to `iv`.
  obtain ⟨v7, hv7⟩ : ∃ v7, u.mem.readW (addr (s.gpr .esi) (16 * bs.length)) 128 = v7 := ⟨_, rfl⟩
  obtain c7 : (st v7).toList = chainK (cfbMode false) s₀ (c + (bs.length + 1)) := by
    rw [← hv7, ml, st_readW, haddr bs.length (by omega_using [hc]), hblk bs.length (by omega_using [hc])]; rfl
  refine x_load (B := s.gpr .esi) (o := 16 * bs.length) (by rw [gl])
    (by rw [rl, wl, haddr bs.length (by omega_using [hc])]; exact in_rd (hinB _ (by omega_using [hc]))) ?_
  rw [hv7]
  refine x_store' (B := Iv s₀) (o := 0) (by rw [gpr_setXmm, gl]; exact hI.edx)
    (by rw [wr_setXmm, wl, addr_zero]; exact hinI) (WP.block_nil ⟨fun k hk => ?_, ?_, ?_, ?_, ?_, ?_⟩)
  · show (st ((u.setXmm .xmm7 v7).xmm (b :: bs)[k])).toList = _
    cases k with
    | zero =>
      rw [List.getElem_cons_zero, xmm_setXmm_of_ne _ _ hb7, xl b hbs, xmm_setXmm_self, Nat.add_zero]
      exact c0
    | succ k =>
      obtain hk' : k < bs.length := Nat.lt_of_succ_lt_succ hk
      have hne : bs[k] ≠ .xmm7 := fun h => h7' (h ▸ List.getElem_mem hk')
      rw [List.getElem_cons_succ, xmm_setXmm_of_ne _ _ hne,
        hl k hk', Nat.zero_add, haddr k (by omega_using [hc, hk']), ← bytesAt_toList,
        hblk k (by omega_using [hc, hk'])]
      rfl
  · show u.gpr = s.gpr
    exact gl
  · show u.rd = s.rd
    exact rl
  · show u.wr = s.wr
    exact wl
  · show Frame [ivR s₀] s.mem (u.mem.writeW (addr (Iv s₀) 0) ((u.setXmm .xmm7 v7).xmm .xmm7))
    rw [ml, addr_zero]
    exact (Frame.refl _ _).writeW (r := ivR s₀) List.mem_cons_self _ (Region.contains_self _ _)
  · show bytesAt (u.mem.writeW (addr (Iv s₀) 0) ((u.setXmm .xmm7 v7).xmm .xmm7)) ((Iv s₀).setWidth 64) 16 = _
    rw [xmm_setXmm_self, addr_zero, ← st_readW, Mem.readW_writeW_self _ _ 16 _ (by decide)]
    exact c7

section Groups

variable {s₀ : State} (hp : UPre s₀) {m : Mem}
  (hm : Frame [ivR s₀, dataR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stkR s₀] (savedMem s₀) m)
include hp

include hm in
/-- The blocks `c … c + n - 1` (`n` the number of registers) deciphered. -/
theorem blocks_ok (rs : List XReg) (hrs : Lanes rs) (rest : List Instr) {Q : State → Prop} {c q : Nat}
    (hc : c + rs.length ≤ N s₀) {s : State} (hI : DInv s₀ m c c q s)
    (hQ : ∀ t, DInv s₀ m (c + rs.length) c q t → WP isa (.block rest) t Q) :
    WP isa (decNiGroup rs rest) s Q := by
  obtain ⟨hnd, h6⟩ := regs_nodup rs hrs
  obtain h7 : .xmm7 ∉ rs := by rcases hrs with rfl | rfl | rfl | rfl <;> decide
  obtain ⟨b, bs, rfl⟩ : ∃ b bs, rs = b :: bs := by rcases hrs with rfl | rfl | rfl | rfl <;> exact ⟨_, _, rfl⟩
  have hdf := hp.data_fit
  simp only [List.length_cons] at hc
  refine WP.seq (WP.mono (load_ok hp hI b bs hnd h7 hc) fun t ⟨hl, gt, rt, wt, ft, it⟩ => ?_)
  -- The round keys, which the block at `iv` is apart from.
  obtain big : Frame (Big s₀) s₀.mem t.mem :=
    (UPre.big_of hm).trans ((hI.frame.trans (ft.mono (by simp))).mono (by simp))
  obtain hK := niKeys (s := t) (nr := R s₀) (by rcases hp.rounds with h | h | h <;> omega_using [h]) hp.sch_fit
    (by rw [gt]; exact hI.eax) (by rw [rt, hI.rd]; simp [hp.rd])
  rw [UPre.sched_bytes hp big] at hK
  refine WP.seq (WP.mono (aes_ok (b :: bs) hnd h6 hp.rounds t hK (by rw [gt]; exact hI.ecx)) fun v ⟨ha, fa⟩ => ?_)
  obtain gv : v.gpr = s.gpr := fa.gpr.trans gt
  rw [WP.block_append_iff]
  refine WP.mono (xorData_ok hp (c := c) (b :: bs) 0 v hnd h7
    (fun k hk => by rw [gv, hI.esi, addr_add, addr_eq (by omega_using [hdf, hk]), ← Nat.mul_add])
    (by rw [List.length_cons]; omega_using [hc]) (by rw [fa.wr, wt, hI.wr])
    (by rw [Nat.add_zero, fa.mem, data_iv hp ft]; exact hI.data)
    (fun k hk => by rw [Nat.add_zero, ha _ (List.getElem_mem hk)]; exact aes_list (hl k hk)))
    fun z ⟨hd, fz, gz, rz, wz⟩ => ?_
  rw [Nat.add_zero] at hd
  rw [fa.mem] at fz
  exact hQ z
    { le := by rw [List.length_cons]; exact hc
      esi := by rw [gz, gv]; exact hI.esi
      edi := by rw [gz, gv]; exact hI.edi
      eax := by rw [gz, gv]; exact hI.eax
      ecx := by rw [gz, gv]; exact hI.ecx
      edx := by rw [gz, gv]; exact hI.edx
      esp := by rw [gz, gv]; exact hI.esp
      rd := by rw [rz, fa.rd, rt, hI.rd]
      wr := by rw [wz, fa.wr, wt, hI.wr]
      frame := hI.frame.trans ((ft.mono (by simp)).trans (fz.mono (by simp)))
      data := hd
      iv := by
        rw [Proof.Cmac.bytesAt_frame fz (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact hp.iv_data) (by decide)]
        exact it }

omit hp in
/-- `add esi, 16 n; sub edi, n`, after `n` more blocks. -/
theorem advance_ok {rest : List Instr} {c n : Nat} (hc : c + n ≤ N s₀) {s : State}
    (hI : DInv s₀ m (c + n) c c s) {Q : State → Prop}
    (hQ : ∀ s', DInv s₀ m (c + n) (c + n) (c + n) s' → WP isa (.block rest) s' Q) :
    WP isa (.block (.alu .add .esi (.imm (BitVec.ofNat 32 (16 * n))) :: .alu .sub .edi
      (.imm (BitVec.ofNat 32 n)) :: rest)) s Q := by
  obtain e : BitVec.ofNat 32 (N s₀ - c) - BitVec.ofNat 32 n = BitVec.ofNat 32 (N s₀ - (c + n)) := by
    rw [Wp.sub_ofNat (by omega_using [hc]), Nat.sub_sub]
  refine wp_addi fun s₁ u₁ => wp_subi fun s₂ u₂ _ _ => hQ s₂ ?_
  refine hI.move (fun r h1 h2 => by rw [u₂.other r h2, u₁.other r h1]) ?_ ?_
    (by rw [u₂.mem, u₁.mem]) (by rw [u₂.rd, u₁.rd]) (by rw [u₂.wr, u₁.wr])
  · rw [u₂.other _ (by decide), u₁.gpr, hI.esi, BitVec.add_assoc, ← BitVec.ofNat_add, ← Nat.mul_add]
  · rw [u₂.gpr, u₁.other _ (by decide), hI.edi, e]

omit hp in
/-- `add esi, 16 n`, after `n` more blocks: `edi` is as it was. -/
theorem skip_ok {c n q : Nat} {s : State} (hI : DInv s₀ m (c + n) c q s) :
    WP isa (.block [.alu .add .esi (.imm (BitVec.ofNat 32 (16 * n)))]) s (DInv s₀ m (c + n) (c + n) q) := by
  refine wp_addi fun s₁ u₁ => WP.block_nil ?_
  refine hI.move (fun r h1 _ => u₁.other r h1) ?_ (by rw [u₁.other _ (by decide), hI.edi]) u₁.mem u₁.rd u₁.wr
  rw [u₁.gpr, hI.esi, BitVec.add_assoc, ← BitVec.ofNat_add, ← Nat.mul_add]

include hm in
/-- The turn of six blocks. -/
theorem body6_ok {c : Nat} (hc : c + 6 ≤ N s₀) {s : State} (hI : DInv s₀ m c c c s) :
    WP isa decNi6 s fun s' => DInv s₀ m (c + 6) (c + 6) (c + 6) s' ∧
      s'.cf = some (decide (N s₀ - (c + 6) < 6)) := by
  obtain hn : N s₀ < 2 ^ 32 := (arg s₀ 4).isLt
  refine blocks_ok hp hm regs6 (.inl rfl) _ hc hI fun s₁ hI₁ => ?_
  refine advance_ok (n := 6) hc hI₁ fun s₂ hI₂ => ?_
  refine wp_cmpi fun s₃ u₃ hcf _ => WP.block_nil ⟨hI₂.fupd u₃, ?_⟩
  rw [hcf, hI₂.edi, toNat_ofNat_lt (by omega_using [hn])]; rfl

include hm in
/-- The three blocks, if three are left. -/
theorem three_ok {c : Nat} {s : State} (hI : DInv s₀ m c c c s) (hlt : N s₀ - c < 6) :
    WP isa decNi3 s fun s' => ∃ c', N s₀ - c' < 3 ∧ DInv s₀ m c' c' c' s' := by
  obtain hn : N s₀ < 2 ^ 32 := (arg s₀ 4).isLt
  have hle := hI.le
  refine WP.seq (WP.mono (Q := fun (s₁ : State) => DInv s₀ m c c c s₁ ∧ s₁.cf = some (decide (N s₀ - c < 3)))
    (wp_cmpi fun s₁ u₁ hcf _ => WP.block_nil ⟨hI.fupd u₁, ?_⟩) fun s₁ ⟨hI₁, hcf₁⟩ => ?_)
  · rw [hcf, hI.edi, toNat_ofNat_lt (by omega_using [hn])]; rfl
  refine WP.ite (decide (N s₀ - c < 3)) (by simp [eval, hcf₁]) (fun h => ?_) (fun h => ?_)
  · exact WP.block_nil ⟨c, by simpa using h, hI₁⟩
  · obtain hc : c + 3 ≤ N s₀ := by simp at h; omega_using [h, hle]
    refine blocks_ok hp hm regs3 (.inr (.inl rfl)) _ hc hI₁ fun s₂ hI₂ => ?_
    exact advance_ok (n := 3) (rest := []) hc hI₂ fun s₃ hI₃ =>
      WP.block_nil ⟨c + 3, by omega_using [hlt], hI₃⟩

include hm in
/-- A group of the blocks left after block `c`: taken if the count from
block `q` on has the group's bit, which is set when the blocks left are
at least the group's; then `esi` is past it. -/
theorem group_ok (rs : List XReg) (hrs : Lanes rs) {Q : State → Prop} {c q : Nat}
    {s : State} (hI : DInv s₀ m c c q s)
    (hbit : (BitVec.ofNat 32 (N s₀ - q) &&& BitVec.ofNat 32 rs.length == 0) = decide (N s₀ - c < rs.length))
    (hskip : N s₀ - c < rs.length → ∀ s', DInv s₀ m c c q s' → Q s')
    (hrun : c + rs.length ≤ N s₀ → ∀ s', DInv s₀ m (c + rs.length) (c + rs.length) q s' → Q s') :
    WP isa (decNiBit rs) s Q := by
  have hle := hI.le
  refine WP.seq (WP.mono (Q := fun (s₁ : State) => DInv s₀ m c c q s₁ ∧
      s₁.zf = some (BitVec.ofNat 32 (N s₀ - q) &&& BitVec.ofNat 32 rs.length == 0))
    (Wp.cons rfl (WP.block_nil ⟨hI.fupd ⟨rfl, rfl, rfl, rfl, rfl⟩, by rw [← hI.edi]; rfl⟩))
    fun s₁ ⟨hI₁, hzf⟩ => ?_)
  rw [hbit] at hzf
  refine WP.ite (decide (N s₀ - c < rs.length)) (by simp [eval, hzf]) (fun h => ?_) (fun h => ?_)
  · exact WP.block_nil (hskip (by simpa using h) _ hI₁)
  · obtain hc : c + rs.length ≤ N s₀ := by simp at h; omega_using [h, hle]
    exact blocks_ok hp hm rs hrs _ hc hI₁ fun s₂ hI₂ => WP.mono (skip_ok hI₂) fun s₃ hI₃ => hrun hc s₃ hI₃

include hm in
/-- The blocks left after `c₀`, six at a time and then three, two and
one. -/
theorem tail_ok {c₀ : Nat} {s₁ : State} (hI₁ : DInv s₀ m c₀ c₀ c₀ s₁)
    (hcf : s₁.cf = some (decide (N s₀ - c₀ < 6))) :
    WP isa decNiTail s₁ fun s => ∃ q, DInv s₀ m (N s₀) (N s₀) q s := by
  refine WP.seq (WP.mono (Q := fun s => ∃ c, N s₀ - c < 6 ∧ DInv s₀ m c c c s) ?_
    fun s₂ ⟨c, hc, hI₂⟩ => ?_)
  · refine WP.ite (decide (N s₀ - c₀ < 6)) (by simp [eval, hcf]) (fun h => ?_) (fun h => ?_)
    · exact WP.block_nil ⟨c₀, by simpa using h, hI₁⟩
    · let I6 : Nat → State → Prop := fun k s => ∃ c, k = N s₀ - c ∧ c + 6 ≤ N s₀ ∧ DInv s₀ m c c c s
      have hstep : ∀ k s, I6 k s → WP isa decNi6 s (fun s' =>
          (eval .ae s' = some false ∧ ∃ c, N s₀ - c < 6 ∧ DInv s₀ m c c c s') ∨
          (eval .ae s' = some true ∧ ∃ k' < k, I6 k' s')) := by
        rintro k s ⟨c, rfl, hc, hI⟩
        refine WP.mono (body6_ok hp hm hc hI) fun s' ⟨hI', hcf'⟩ => ?_
        by_cases hlt : N s₀ - (c + 6) < 6
        · exact .inl ⟨by simp [eval, hcf', hlt], c + 6, hlt, hI'⟩
        · exact .inr ⟨by simp [eval, hcf', hlt], N s₀ - (c + 6), by omega_using [hc], c + 6, rfl,
            by omega_using [hlt], hI'⟩
      exact WP.loop (M := isa) I6 hstep (N s₀ - c₀) s₁ ⟨c₀, rfl, by simp at h; omega_using [h], hI₁⟩
  refine WP.seq (WP.mono (three_ok hp hm hI₂ hc) fun s₃ ⟨q, hq, hI₃⟩ => ?_)
  -- The blocks left, fewer than three, as `edi` has them from here on: their bits 2 and 1.
  obtain ⟨b2, b1⟩ := bit_lt (N s₀ - q) hq
  have hle := hI₃.le
  refine WP.seq (WP.mono (Q := fun s => ∃ c, N s₀ - c = (N s₀ - q) % 2 ∧ DInv s₀ m c c q s)
    (group_ok hp hm regs2 (.inr (.inr (.inl rfl))) hI₃ (by rw [show regs2.length = 2 from rfl, b2])
      (fun h s' hI' => ⟨q, by rw [show regs2.length = 2 from rfl] at h; omega_using [h], hI'⟩)
      (fun h s' hI' => ⟨q + 2, by rw [show regs2.length = 2 from rfl] at h; omega_using [h, hq], hI'⟩))
    fun s₄ ⟨c₄, e₄, hI₄⟩ => ?_)
  refine group_ok hp hm regs1 (.inr (.inr (.inr rfl))) hI₄ (by rw [show regs1.length = 1 from rfl, b1, e₄])
    (fun h s' hI' => ?_) (fun h s' hI' => ?_)
  · obtain e : c₄ = N s₀ := by
      have := hI'.le; rw [show regs1.length = 1 from rfl] at h; omega_using [this, h]
    exact ⟨q, e ▸ hI'⟩
  · obtain e : c₄ + regs1.length = N s₀ := by
      rw [show regs1.length = 1 from rfl] at h ⊢; omega_using [h, e₄]
    exact ⟨q, e ▸ hI'⟩

end Groups

/-- The arguments loaded, and the count of blocks compared with 6. -/
theorem pre_ok {s₀ : State} (hp : UPre s₀) {s : State} (h : LInv (cfbMode false) s₀ 0 s) :
    WP isa (.block decNiPre) s fun t => DInv s₀ s.mem 0 0 0 t ∧ t.cf = some (decide (N s₀ - 0 < 6)) := by
  obtain big := UPre.big_of h.frame
  obtain hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rd, h.wr]
  have hin : ∀ i < 6, InRegions (s.rd ++ s.wr) (argAddr s₀ i) 4 := fun i hi => by rw [hrw]; exact hp.arg_in hi
  have harg : ∀ i < 6, s.mem.readW (argAddr s₀ i) 32 = arg s₀ i := fun i hi => hp.arg_keep big hi
  refine wp_arg (s₀ := s₀) h.esp (hin 4 (by decide)) (harg 4 (by decide)) fun s₁ u₁ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₁.other _ (by decide)]; exact h.esp)
    (by rw [u₁.rd, u₁.wr]; exact hin 0 (by decide)) (by rw [u₁.mem]; exact harg 0 (by decide)) fun s₂ u₂ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₂.other _ (by decide), u₁.other _ (by decide)]; exact h.esp)
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hin 1 (by decide))
    (by rw [u₂.mem, u₁.mem]; exact harg 1 (by decide)) fun s₃ u₃ => ?_
  refine wp_arg (s₀ := s₀)
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]; exact h.esp)
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hin 2 (by decide))
    (by rw [u₃.mem, u₂.mem, u₁.mem]; exact harg 2 (by decide)) fun s₄ u₄ => ?_
  obtain m₄ : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  obtain edi₄ : s₄.gpr .edi = arg s₀ 4 := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  refine wp_cmpi fun s₅ u₅ hcf _ => WP.block_nil ⟨?_, ?_⟩
  · exact
      { le := Nat.zero_le _
        esi := by
          rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
            u₁.other _ (by decide)]
          exact h.esi
        edi := by rw [u₅.gpr, edi₄, Nat.sub_zero]; exact arg_ofNat s₀ 4
        eax := by rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]
        ecx := by rw [u₅.gpr, u₄.other _ (by decide), u₃.gpr]; exact arg_ofNat s₀ 1
        edx := by rw [u₅.gpr, u₄.gpr]
        esp := by
          rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
            u₁.other _ (by decide)]
          exact h.esp
        rd := by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd]
        wr := by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr]
        frame := by rw [u₅.mem, m₄]; exact Frame.refl _ _
        data := by rw [u₅.mem, m₄]; exact h.data
        iv := by rw [u₅.mem, m₄]; exact h.iv }
  · rw [hcf, edi₄, Nat.sub_zero]; rfl

/-- The blocks: the invariant the epilogue starts from, with only the block
at `iv` and the data changed since the prologue. -/
theorem mid_wp {s₀ : State} (hp : UPre s₀) {s₁ : State} (h : LInv (cfbMode false) s₀ 0 s₁) :
    WP isa decNiMid s₁ fun t => LInv (cfbMode false) s₀ (N s₀) t ∧ Frame (FB s₀ 0) s₁.mem t.mem :=
  WP.seq (WP.mono (pre_ok hp h) fun _ ⟨hI, hcf⟩ =>
    WP.mono (tail_ok hp h.frame hI hcf) fun _ ⟨_, hI'⟩ =>
      ⟨⟨hI'.esi, hI'.esp, hI'.rd, hI'.wr, h.frame.trans (hI'.frame.mono (by simp)), hI'.data, hI'.iv⟩,
        hI'.frame.mono (by simp)⟩)

/-- It runs to the contract's postcondition, as the code around a block
function does (`whole_wp`). -/
theorem correct (s : State) (hs : (modeX86 (cfbMode false)).pre s) :
    ∃ t s', Exec isa decryptNi s t s' ∧ abiPreserved s s' ∧ (modeX86 (cfbMode false)).post s s' :=
  (endsZ_wp (b := 0) hs fun h _ => mid_wp (UPre.of hs) h).mono fun _ h => ⟨h.1, h.2.1⟩

theorem ct : ConstantTime isa (modeX86 (cfbMode false)).pre (modeX86 (cfbMode false)).pub decryptNi :=
  VG.Taint.constantTime (A := sseTaint) Decrypt.τ₀
    (fun _ _ h₁ h₂ hp => Decrypt.agree₀ (UPre.of h₁) (UPre.of h₂) hp) (by taint_decide)

/-- It writes `esp` nowhere: it has no frame and no call. -/
theorem noSp : NoSp decryptNi := NoSp.of_all (by lit_decide)

theorem stack : stackUse decryptNi = 0 := by lit_decide

theorem spSafe : decryptNi.all (fun i => !isa.writesSp i) = true := Code.all_of_spTest (by lit_decide)

end VG.Proof.AesCfb.X86.NiDec

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
Both meet the same contract (`encryptCode_verified`). Decryption's is
`decryptCode v` likewise: with AES-NI, `Impl.AesCfb.X86.decryptNi` (`NiDec`
above), six blocks at a time with no call.
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

/-- The shared contract of decryption, from the code's own
(`modeX86 (cfbMode false)`). -/
theorem decrypt_implies :
    (modeX86 (cfbMode false)).Implies (Proof.AesCfb.decryptRoundsContract X86.abi 24) := by
  have a0 : arg sat 0 = 0x1000 := by decide
  have a1 : arg sat 1 = 10 := by decide
  have a2 : arg sat 2 = 0x2000 := by decide
  have a3 : arg sat 3 = 0x3000 := by decide
  have a4 : arg sat 4 = 0 := by decide
  have a5 : arg sat 5 = 0x4000 := by decide
  have e : argAddr sat 0 = 0x8004 := by decide
  have esp : sat.gpr .esp = 0x8000 := rfl
  sig_implies [Proof.AesCfb.decryptRoundsContract, Spec.Cfb.aesSig, Spec.Cbc.aesSig, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes, modeX86, cfbMode, cfb, cts] [a0, a1, a2, a3, a4, a5, e, esp] using sat

theorem decrypt_verified (v : BlocksImpl) :
    Verified X86.target (decrypt v.enc) (Proof.AesCfb.decryptRoundsContract X86.abi 24) :=
  Verified.of_correct (fun _ hs => whole_wp (decBody_ok v) hs) (whole_ct (decBody_ok v) (decBody_ct v))
    decrypt_implies

/-! ## The code of decryption of each implementation -/

/-- The whole-block code of decryption for `v`: with AES-NI, the code that
enciphers six blocks at a time with no call (`Impl.AesCfb.X86.decryptNi`);
for any other implementation, `decrypt` around its block function. -/
def decryptCode (v : BlocksImpl) : Prog isa := if hardware v then decryptNi else decrypt v.enc

/-- `decryptCode v` runs to the code's own contract. -/
theorem decryptCode_correct (v : BlocksImpl) (s : State) (hs : (modeX86 (cfbMode false)).pre s) :
    ∃ t s', Exec isa (decryptCode v) s t s' ∧ abiPreserved s s' ∧ (modeX86 (cfbMode false)).post s s' := by
  unfold decryptCode
  split
  · exact NiDec.correct s hs
  · exact whole_wp (decBody_ok v) hs

theorem decryptCode_ct (v : BlocksImpl) :
    ConstantTime isa (modeX86 (cfbMode false)).pre (modeX86 (cfbMode false)).pub (decryptCode v) := by
  unfold decryptCode
  split
  · exact NiDec.ct
  · exact whole_ct (decBody_ok v) (decBody_ct v)

theorem decryptCode_verified (v : BlocksImpl) :
    Verified X86.target (decryptCode v) (Proof.AesCfb.decryptRoundsContract X86.abi 24) :=
  Verified.of_correct (decryptCode_correct v) (decryptCode_ct v) decrypt_implies

theorem decryptCode_spSafe (v : BlocksImpl) : (decryptCode v).all (fun i => !isa.writesSp i) = true := by
  unfold decryptCode
  split
  · exact NiDec.spSafe
  · exact decrypt_spSafe v

end VG.Proof.AesCfb.X86
