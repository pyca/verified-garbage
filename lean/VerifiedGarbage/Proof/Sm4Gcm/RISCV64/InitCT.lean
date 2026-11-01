module

import VerifiedGarbage.Proof.AesGcm.RISCV64.CTBase
public import VerifiedGarbage.Proof.Sm4Gcm.RISCV64.Contract
public import VerifiedGarbage.Proof.Sm4Gcm.RISCV64.Callee
import VerifiedGarbage.Proof.AesGcm.RISCV64.InitCT
import VerifiedGarbage.Proof.Sm4Gcm.RISCV64.Init
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.CTBase
meta import VerifiedGarbage.Proof.Sm4Gcm.RISCV64.Contract
meta import VerifiedGarbage.Proof.Sm4Gcm.RISCV64.Callee
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.InitCT
meta import VerifiedGarbage.Proof.Sm4Gcm.RISCV64.Init
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
public import VerifiedGarbage.Impl.Sm4Gcm.RISCV64
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Impl.Sm4Gcm.RISCV64

/-!
# SM4-GCM on RISC-V: `vg_sm4_gcm_init` is constant time

Untrusted: everything here is checked by Lean. As AES-GCM's
(`Proof/AesGcm/RISCV64/InitCT.lean`): the code around the calls by the taint
analysis, from the public arguments and the registers the correctness proof
pins; SM4's code by its own proofs (`CT.skey`, `CT.sctr`).
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.RISCV64

open VG VG.RISCV64 VG.Impl.Sm4Gcm.RISCV64
open VG.Impl.AesGcm.RISCV64 (restore)
open VG.Proof.AesGcm.RISCV64 (CT ct_of CT.taintEq covers_mem restore_taint)

theorem initPre_taint : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.a0, .a1, .a2])
    (.block initPre) h).isSome = true := ⟨_, by taint_decide⟩

theorem initArgs_taint : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s2, .s0])
    (.block initArgs) h).isSome = true := ⟨_, by taint_decide⟩

theorem init_ct : ConstantTime isa initRISCV64.pre initRISCV64.pub init := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  obtain ⟨q3, q4, q5, qsp⟩ := hq
  have hpre₁ := h₁
  obtain ⟨-, -, -, -, dcs, -, fc, fs, ⟨spal, spge, -, bC, bS, -⟩, hca, hwa⟩ := hpre₁
  generalize hK : σ₁.gpr .a0 = K at *
  generalize hC : σ₁.gpr .a1 = C at *
  generalize hW : σ₁.gpr .a2 = W at *
  generalize hSP : σ₁.sp = SP at *
  let I₀ : State → Prop := fun s => initRISCV64.pre s ∧ s.gpr .a0 = K ∧ s.gpr .a1 = C ∧ s.gpr .a2 = W ∧
    s.sp = SP
  let I₁ : State → Prop := fun s => KeyCall s K C ∧ s.gpr .s2 = C ∧ s.gpr .s0 = W ∧ s.sp = SP ∧
    s.wr = [⟨C, 256⟩, ⟨W, 2560⟩]
  let I₂ : State → Prop := fun s => s.gpr .s2 = C ∧ s.gpr .s0 = W ∧ s.sp = SP ∧ s.wr = [⟨C, 256⟩, ⟨W, 2560⟩]
  let I₃ : State → Prop := fun s => CtrCall s C (W + BitVec.ofNat 64 96) (C + BitVec.ofNat 64 240) 1 ∧
    s.gpr .s0 = W ∧ s.sp = SP
  let I₄ : State → Prop := fun s => s.gpr .s0 = W ∧ s.sp = SP
  refine ⟨I₀, ⟨h₁, hK, hC, hW, hSP⟩, ⟨h₂, q3.symm, q4.symm, q5.symm, qsp.symm⟩, ?_⟩
  refine CT.seq (J := I₁) ?_ (fun s ⟨hs, e3, e4, e5, esp⟩ => WP.mono (is1_wp hs) fun s₁ h1 => ?_) ?_
  · obtain ⟨_, hc⟩ := initPre_taint
    exact CT.taintEq (I := I₀) _ (fun r => if r = .a0 then K else if r = .a1 then C else W) SP
      (fun s ⟨_, e3, e4, e5, esp⟩ => ⟨esp, by simp [e3, e4, e5]⟩) hc
  · have kc := init_kc hs h1
    rw [e3, e4] at kc
    obtain ⟨-, hwr, -⟩ := hs
    refine ⟨kc, by rw [h1.s2, e4], by rw [h1.s0, e5], by rw [h1.keeps.sp, esp], by rw [h1.keeps.wr, hwr, e4, e5]⟩
  refine CT.seq (J := I₂) ?_ (fun s ⟨kc, e29, e31, esp, ewr⟩ => WP.mono (key_call kc) fun s₂ kp =>
    ⟨by rw [kp.saved _ (by decide), e29], by rw [kp.saved _ (by decide), e31], by rw [kp.sp, esp],
      by rw [kp.wr, ewr]⟩) ?_
  · exact CT.skey fun s₁ s₂ h₁ h₂ => ⟨_, _, h₁.1, h₂.1, h₁.2.2.2.1.trans h₂.2.2.2.1.symm⟩
  refine CT.seq (J := I₃) ?_ (fun s ⟨e29, e31, esp, ewr⟩ =>
    WP.mono (initArgs_ok e29 e31 (by rw [ewr]; exact covers_mem (by simp))
      (by rw [ewr]; exact covers_mem (by simp)) hca hwa) fun s₃ ⟨_, a3, a4, a5, a6, hg₃, hk₃⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ := initArgs_taint
    exact CT.taintEq (I := I₂) _ (fun r => if r = .s2 then C else W)
      SP (fun s ⟨e29, e31, esp, _⟩ => ⟨esp, by simp [e29, e31]⟩) hc
  · have hW₃ : Covers [⟨W, 2560⟩] s₃.wr := by rw [hk₃.wr, ewr]; exact covers_mem (by simp)
    have hC₃ : Covers [⟨C, 256⟩] s₃.wr := by rw [hk₃.wr, ewr]; exact covers_mem (by simp)
    have sp₃ : s₃.sp = SP := by rw [hk₃.sp, esp]
    exact ⟨init_cc dcs fc fs hW₃ hC₃ (by rw [sp₃]; exact spal) (by rw [sp₃]; exact spge)
      (by rw [sp₃]; exact bC) (by rw [sp₃]; exact bS) a3 a4 a5 a6,
      by rw [hg₃ _ (by decide) (by decide) (by decide) (by decide) (by decide), e31], sp₃⟩
  refine CT.seq (J := I₄) ?_ (fun s ⟨cc, e31, esp⟩ => WP.mono (ctr_call cc) fun s₄ cp =>
    ⟨by rw [cp.saved _ (by decide), e31], by rw [cp.sp, esp]⟩) ?_
  · exact CT.sctr fun s₁ s₂ h₁ h₂ => ⟨_, _, _, _, h₁.1, h₂.1, h₁.2.2.trans h₂.2.2.symm⟩
  · obtain ⟨_, hc⟩ := restore_taint
    exact CT.taintEq (I := I₄) _ (fun _ => W) SP (fun s ⟨e31, esp⟩ => ⟨esp, by simp [e31]⟩) hc

end VG.Proof.Sm4Gcm.RISCV64
