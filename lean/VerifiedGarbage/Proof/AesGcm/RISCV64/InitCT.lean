module

import VerifiedGarbage.Proof.AesGcm.RISCV64.CTBase
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Contract
import VerifiedGarbage.Proof.AesGcm.RISCV64.Init
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.CTBase
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.Contract
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.Init
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
public import VerifiedGarbage.Impl.AesGcm.RISCV64
public import VerifiedGarbage.Proof.Aes.SboxSpec
public import VerifiedGarbage.Proof.Framework.Bitslice.Atoms
public import VerifiedGarbage.Proof.Framework.Inline
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Spec.Aes
meta import VerifiedGarbage.Impl.AesGcm.RISCV64

/-!
# AES-GCM on RISC-V: `vg_aes_gcm_init` is constant time

Untrusted: everything here is checked by Lean. The code around the calls by
the taint analysis, from the public arguments and the registers the
correctness proof pins; the calls by their callees' proofs, with the
arguments those proofs give.
-/

@[expose] public section

namespace VG.Proof.AesGcm.RISCV64

open VG VG.RISCV64 VG.Impl.AesGcm.RISCV64

theorem initPre_taint : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.a0, .a1, .a2, .a3])
    (.block initPre) h).isSome = true := ⟨_, by taint_decide⟩

theorem initArgs_taint : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s3, .s2, .s0])
    (.block initArgs) h).isSome = true := ⟨_, by taint_decide⟩

theorem restore_taint : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s0])
    (.block restore) h).isSome = true := ⟨_, by taint_decide⟩

theorem init_ct : ConstantTime isa initRISCV64.pre initRISCV64.pub init := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  obtain ⟨q3, q4, q5, q6, qsp⟩ := hq
  have hpre₁ := h₁
  obtain ⟨-, -, -, -, dcs, fc, -, hlen, hca, hwa⟩ := hpre₁
  generalize hK : σ₁.gpr .a0 = K at *
  generalize hL : σ₁.gpr .a1 = KL at *
  generalize hC : σ₁.gpr .a2 = C at *
  generalize hW : σ₁.gpr .a3 = W at *
  generalize hSP : σ₁.sp = SP at *
  have hR := rounds_ok hlen
  let R := Spec.Aes.rounds (KL.toNat / 4)
  let I₀ : State → Prop := fun s => initRISCV64.pre s ∧ s.gpr .a0 = K ∧ s.gpr .a1 = KL ∧ s.gpr .a2 = C ∧
    s.gpr .a3 = W ∧ s.sp = SP
  let I₁ : State → Prop := fun s => KeyCall s K KL.toNat C (W + BitVec.ofNat 64 512) ∧
    s.gpr .s3 = BitVec.ofNat 64 R ∧ s.gpr .s2 = C ∧ s.gpr .s0 = W ∧ s.sp = SP ∧
    s.wr = [⟨C, 256⟩, ⟨W, 2560⟩]
  let I₂ : State → Prop := fun s => s.gpr .s3 = BitVec.ofNat 64 R ∧ s.gpr .s2 = C ∧ s.gpr .s0 = W ∧
    s.sp = SP ∧ s.wr = [⟨C, 256⟩, ⟨W, 2560⟩]
  let I₃ : State → Prop := fun s => CtrCall s C (W + BitVec.ofNat 64 96) (C + BitVec.ofNat 64 240)
    (W + BitVec.ofNat 64 512) R 1 ∧ s.gpr .s0 = W ∧ s.sp = SP
  let I₄ : State → Prop := fun s => s.gpr .s0 = W ∧ s.sp = SP
  refine ⟨I₀, ⟨h₁, hK, hL, hC, hW, hSP⟩, ⟨h₂, q3.symm, q4.symm, q5.symm, q6.symm, qsp.symm⟩, ?_⟩
  refine CT.seq (J := I₁) ?_ (fun s ⟨hs, e3, e4, e5, e6, esp⟩ => WP.mono (is1_wp hs) fun s₁ h1 => ?_) ?_
  · obtain ⟨_, hc⟩ := initPre_taint
    exact CT.taintEq (I := I₀) _ (fun r => if r = .a0 then K else if r = .a1 then KL else
      if r = .a2 then C else W) SP (fun s ⟨_, e3, e4, e5, e6, esp⟩ => ⟨esp, by simp [e3, e4, e5, e6]⟩) hc
  · have kc := init_kc hs h1
    rw [e3, e4, e5, e6] at kc
    obtain ⟨-, hwr, -⟩ := hs
    refine ⟨kc, by rw [h1.s3, initR, e4], by rw [h1.s2, e5], by rw [h1.s0, e6],
      by rw [h1.keeps.sp, esp], by rw [h1.keeps.wr, hwr, e5, e6]⟩
  refine CT.seq (J := I₂) ?_ (fun s ⟨kc, e28, e29, e31, esp, ewr⟩ => WP.mono (key_call kc) fun s₂ kp =>
    ⟨by rw [kp.saved _ (by decide), e28], by rw [kp.saved _ (by decide), e29],
      by rw [kp.saved _ (by decide), e31], by rw [kp.sp, esp], by rw [kp.wr, ewr]⟩) ?_
  · exact CT.key fun s₁ s₂ h₁ h₂ => ⟨_, _, _, _, h₁.1, h₂.1, h₁.2.2.2.2.1.trans h₂.2.2.2.2.1.symm⟩
  refine CT.seq (J := I₃) ?_ (fun s ⟨e28, e29, e31, esp, ewr⟩ =>
    WP.mono (initArgs_ok e29 e31 e28 (by rw [ewr]; exact covers_mem (by simp))
      (by rw [ewr]; exact covers_mem (by simp)) hca hwa) fun s₃ ⟨_, a3, a4, a5, a6, a7, a8, hg₃, hk₃⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ := initArgs_taint
    exact CT.taintEq (I := I₂) _ (fun r => if r = .s3 then BitVec.ofNat 64 R else if r = .s2 then C else W)
      SP (fun s ⟨e28, e29, e31, esp, _⟩ => ⟨esp, by simp [e28, e29, e31]⟩) hc
  · have hW₃ : Covers [⟨W, 2560⟩] s₃.wr := by rw [hk₃.wr, ewr]; exact covers_mem (by simp)
    have hC₃ : Covers [⟨C, 256⟩] s₃.wr := by rw [hk₃.wr, ewr]; exact covers_mem (by simp)
    exact ⟨init_cc dcs fc hR hW₃ hC₃ a3 a4 a5 a6 a7 a8,
      by rw [hg₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), e31],
      by rw [hk₃.sp, esp]⟩
  refine CT.seq (J := I₄) ?_ (fun s ⟨cc, e31, esp⟩ => WP.mono (ctr_call cc) fun s₄ cp =>
    ⟨by rw [cp.saved _ (by decide), e31], by rw [cp.sp, esp]⟩) ?_
  · exact CT.ctr fun s₁ s₂ h₁ h₂ => ⟨_, _, _, _, _, _, h₁.1, h₂.1, h₁.2.2.trans h₂.2.2.symm⟩
  · obtain ⟨_, hc⟩ := restore_taint
    exact CT.taintEq (I := I₄) _ (fun _ => W) SP (fun s ⟨e31, esp⟩ => ⟨esp, by simp [e31]⟩) hc

end VG.Proof.AesGcm.RISCV64
