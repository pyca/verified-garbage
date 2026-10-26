module

import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.Callee
public import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.Contract
import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.Init
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Env
meta import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.Callee
meta import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.Contract
meta import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.Init
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.Env
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Impl.Sm4Gcm.PPC64LE
import Mathlib.Data.List.Induction
import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Impl.Sm4Gcm.PPC64LE
public import VerifiedGarbage.Proof.Aes.SboxSpec
public import VerifiedGarbage.Proof.Framework.Bitslice.Atoms
public import VerifiedGarbage.Proof.Framework.Inline
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
public import VerifiedGarbage.Proof.Framework.PPC64LE.SlotTaint
public import VerifiedGarbage.Proof.Framework.PPC64LE.StraightK
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.Modes.PPC64LE.Seq
public import VerifiedGarbage.Proof.Sm4.SboxTable

/-!
# SM4-GCM on PPC64LE: `vg_sm4_gcm_init` is constant time

Untrusted: everything here is checked by Lean. As AES-GCM's
(`Proof/AesGcm/PPC64LE/InitCT.lean`): the code around SM4's inlined code by
the taint analysis, from the public arguments and the registers the
correctness proof pins; SM4's code by its own proofs (`CT.key`, `CT.ctr`).
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.PPC64LE

open VG VG.PPC64LE VG.Impl.Sm4Gcm.PPC64LE
open VG.Impl.AesGcm.PPC64LE (restore)
open VG.Proof.AesGcm.PPC64LE (CT ct_of CT.taintEq covers_mem covers_prefix)

theorem initPre_taint : ∃ h, (VG.Taint.check VG.PPC64LE.taint (Taint.ofRegs [.r3, .r4, .r5, .r6])
    (.block initPre) h).isSome = true := ⟨_, by taint_decide⟩

theorem initArgs_taint : ∃ h, (VG.Taint.check VG.PPC64LE.taint (Taint.ofRegs [.r28, .r29, .r31])
    (.block initArgs) h).isSome = true := ⟨_, by taint_decide⟩

theorem restore_taint : ∃ h, (VG.Taint.check VG.PPC64LE.taint (Taint.ofRegs [.r31])
    (.block restore) h).isSome = true := ⟨_, by taint_decide⟩

theorem init_ct : ConstantTime isa initPPC64LE.pre initPPC64LE.pub init := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  obtain ⟨q3, q4, q5, q6, qsp⟩ := hq
  have hpre₁ := h₁
  obtain ⟨-, -, -, -, dcs, -, fc, fs, -, dcx, dsx, fx⟩ := hpre₁
  generalize hK : σ₁.gpr .r3 = K at *
  generalize hC : σ₁.gpr .r4 = C at *
  generalize hW : σ₁.gpr .r5 = W at *
  generalize hX : σ₁.gpr .r6 = X at *
  generalize hSP : σ₁.sp = SP at *
  let I₀ : State → Prop := fun s => initPPC64LE.pre s ∧ s.gpr .r3 = K ∧ s.gpr .r4 = C ∧ s.gpr .r5 = W ∧
    s.gpr .r6 = X ∧ s.sp = SP
  let I₁ : State → Prop := fun s => KeyCall s K C X ∧
    s.gpr .r29 = C ∧ s.gpr .r31 = W ∧ s.gpr .r28 = X ∧ s.sp = SP ∧
    s.wr = [⟨C, 256⟩, ⟨W, scrBytes⟩, ⟨X, xBytes⟩]
  let I₂ : State → Prop := fun s => s.gpr .r29 = C ∧ s.gpr .r31 = W ∧ s.gpr .r28 = X ∧
    s.sp = SP ∧ s.wr = [⟨C, 256⟩, ⟨W, scrBytes⟩, ⟨X, xBytes⟩]
  let I₃ : State → Prop := fun s => CtrCall s C (W + BitVec.ofNat 64 96) (C + BitVec.ofNat 64 240)
    X 1 ∧ s.gpr .r31 = W ∧ s.sp = SP
  let I₄ : State → Prop := fun s => s.gpr .r31 = W ∧ s.sp = SP
  refine ⟨I₀, ⟨h₁, hK, hC, hW, hX, hSP⟩, ⟨h₂, q3.symm, q4.symm, q5.symm, q6.symm, qsp.symm⟩, ?_⟩
  refine CT.seq (J := I₁) ?_ (fun s ⟨hs, e3, e4, e5, e6, esp⟩ => WP.mono (is1_wp hs) fun s₁ h1 => ?_) ?_
  · obtain ⟨_, hc⟩ := initPre_taint
    exact CT.taintEq (I := I₀) _
      (fun r => if r = .r3 then K else if r = .r4 then C else if r = .r5 then W else X) SP
      (fun s ⟨_, e3, e4, e5, e6, esp⟩ => ⟨esp, by simp [e3, e4, e5, e6]⟩) hc
  · have kc := init_kc hs h1
    rw [e3, e4, e6] at kc
    obtain ⟨-, hwr, -⟩ := hs
    refine ⟨kc, by rw [h1.r29, e4], by rw [h1.r31, e5], by rw [h1.r28, e6],
      by rw [h1.keeps.sp, esp], by rw [h1.keeps.wr, hwr, e4, e5, e6]⟩
  refine CT.seq (J := I₂) ?_ (fun s ⟨kc, e29, e31, e28, esp, ewr⟩ => WP.mono (key_wp kc) fun s₂ kp =>
    ⟨by rw [kp.saved _ (by decide), e29], by rw [kp.saved _ (by decide), e31],
      by rw [kp.saved _ (by decide), e28], by rw [kp.sp, esp], by rw [kp.wr, ewr]⟩) ?_
  · exact CT.key fun s₁ s₂ h₁ h₂ => ⟨_, _, _, h₁.1, h₂.1, h₁.2.2.2.2.1.trans h₂.2.2.2.2.1.symm⟩
  refine CT.seq (J := I₃) ?_ (fun s ⟨e29, e31, e28, esp, ewr⟩ =>
    WP.mono (initArgs_ok e29 e31 e28 (by rw [ewr]; exact covers_mem (by simp))
      (by rw [ewr]; exact covers_mem (r := ⟨W, scrBytes⟩) (by simp)))
      fun s₃ ⟨_, a3, a4, a5, a6, a7, hg₃, hk₃⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ := initArgs_taint
    exact CT.taintEq (I := I₂) _ (fun r => if r = .r28 then X else if r = .r29 then C else W)
      SP (fun s ⟨e29, e31, e28, esp, _⟩ => ⟨esp, by simp [e29, e31, e28]⟩) hc
  · have hW₃ : Covers [⟨W, scrBytes⟩] s₃.wr := by rw [hk₃.wr, ewr]; exact covers_mem (by simp)
    have hX₃ : Covers [⟨X, xBytes⟩] s₃.wr := by rw [hk₃.wr, ewr]; exact covers_mem (by simp)
    have hC₃ : Covers [⟨C, 256⟩] s₃.wr := by rw [hk₃.wr, ewr]; exact covers_mem (by simp)
    exact ⟨init_cc dcs dcx dsx fc fs fx hW₃ hX₃ hC₃ a3 a4 a5 a6 a7,
      by rw [hg₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), e31],
      by rw [hk₃.sp, esp]⟩
  refine CT.seq (J := I₄) ?_ (fun s ⟨cc, e31, esp⟩ => WP.mono (ctr_wp cc) fun s₄ cp =>
    ⟨by rw [cp.saved _ (by decide), e31], by rw [cp.sp, esp]⟩) ?_
  · exact CT.ctr fun s₁ s₂ h₁ h₂ => ⟨_, _, _, _, _, h₁.1, h₂.1, h₁.2.2.trans h₂.2.2.symm⟩
  · obtain ⟨_, hc⟩ := restore_taint
    exact CT.taintEq (I := I₄) _ (fun _ => W) SP (fun s ⟨e31, esp⟩ => ⟨esp, by simp [e31]⟩) hc

end VG.Proof.Sm4Gcm.PPC64LE
