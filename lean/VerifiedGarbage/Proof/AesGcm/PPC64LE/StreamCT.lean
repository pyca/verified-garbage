module

import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTBase
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Contract
import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTJ0
import VerifiedGarbage.Proof.AesGcm.PPC64LE.InitCT
import VerifiedGarbage.Proof.AesGcm.PPC64LE.StreamInit
import VerifiedGarbage.Proof.AesGcm.PPC64LE.StreamAad
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTBase
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.Contract
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTJ0
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.InitCT
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.StreamInit
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.StreamAad
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import Mathlib.Data.List.Induction
import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Impl.AesGcm.PPC64LE
public import VerifiedGarbage.Proof.Aes.SboxSpec
public import VerifiedGarbage.Proof.Framework.Bitslice.Atoms
public import VerifiedGarbage.Proof.Framework.Inline
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
public import VerifiedGarbage.Proof.Framework.PPC64LE.StraightK
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint

/-!
# AES-GCM on PPC64LE: `vg_aes_gcm_stream_init` and `vg_aes_gcm_stream_aad` are constant time

Untrusted: everything here is checked by Lean. The entry by the taint
analysis from the public arguments; then `j0` (`j0_ct`) or `absorb 16`
(`absorb_ct`) from the invariants the entry's correctness gives; then the
exit from `W`.
-/

@[expose] public section

namespace VG.Proof.AesGcm.PPC64LE

open VG VG.PPC64LE VG.Impl.AesGcm.PPC64LE

theorem streamInitPre_taint : ∃ h, (VG.Taint.check VG.PPC64LE.taint
    (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7]) (.block streamInitPre) h).isSome = true := ⟨_, by taint_decide⟩

theorem streamAadPre_taint : ∃ h, (VG.Taint.check VG.PPC64LE.taint
    (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7, .r8]) (.block streamAadPre) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem streamInit_ct : ConstantTime isa streamInitPPC64LE.pre streamInitPPC64LE.pub streamInit := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  obtain ⟨q3, q4, q5, q6, q7, qsp⟩ := hq
  have L : Lay (σ₁.gpr .r3) (σ₁.gpr .r6) (σ₁.gpr .r7) := by
    obtain ⟨-, -, dcs, dcw, -, -, dsw, wc, -, ws, ww⟩ := h₁
    exact Lay.of wc ws ww dcs dcw dsw
  let I₀ : State → Prop := fun s => streamInitPPC64LE.pre s ∧ s.gpr .r3 = σ₁.gpr .r3 ∧
    s.gpr .r4 = σ₁.gpr .r4 ∧ s.gpr .r5 = σ₁.gpr .r5 ∧ s.gpr .r6 = σ₁.gpr .r6 ∧ s.gpr .r7 = σ₁.gpr .r7 ∧
    s.sp = σ₁.sp
  refine ⟨I₀, ⟨h₁, rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨h₂, q3.symm, q4.symm, q5.symm, q6.symm, q7.symm,
    qsp.symm⟩, ?_⟩
  refine CT.seq (J := J0I (σ₁.gpr .r3) (σ₁.gpr .r6) (σ₁.gpr .r7) σ₁.sp (σ₁.gpr .r4) (σ₁.gpr .r5).toNat) ?_
    (fun s ⟨hs, e3, e4, e5, e6, e7, esp⟩ => WP.mono (si_entry hs) fun s₁ ⟨_, h29, h30, h31, hJ, _⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ := streamInitPre_taint
    exact CT.taintEq (I := I₀) _ σ₁.gpr σ₁.sp (fun s ⟨_, e3, e4, e5, e6, e7, esp⟩ =>
      ⟨esp, by simp [e3, e4, e5, e6, e7]⟩) hc
  · rw [e3] at h29
    rw [e6] at h30
    rw [e7] at h31
    rw [e3, e4, e5, esp] at hJ
    exact ⟨s₁.gpr, _, h29, h30, h31, hJ⟩
  refine CT.seq (J := fun s => s.gpr .r31 = σ₁.gpr .r7 ∧ s.sp = σ₁.sp) (j0_ct L)
    (fun s ⟨V, H, h29, h30, h31, hJ⟩ => WP.mono (j0_ok (L.v h29 h30 h31) hJ) fun s₂ h₂ =>
      ⟨(h₂.env.fr _ (by decide)).trans h31, h₂.env.sp⟩) ?_
  obtain ⟨_, hc⟩ := restore_taint
  exact CT.taintEq _ (fun _ => σ₁.gpr .r7) σ₁.sp (fun s ⟨e31, esp⟩ => ⟨esp, by simp [e31]⟩) hc

theorem streamAad_ct : ConstantTime isa streamAadPPC64LE.pre streamAadPPC64LE.pub streamAad := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  obtain ⟨q3, q4, q5, q6, q7, q8, qsp⟩ := hq
  have L : Lay (σ₁.gpr .r3) (σ₁.gpr .r4) (σ₁.gpr .r8) := by
    obtain ⟨-, -, dcs, dcw, -, -, dsw, wc, -, ws, ww⟩ := h₁
    exact Lay.of wc ws ww dcs dcw dsw
  let q := (σ₁.gpr .r5).toNat % 16
  have hq16 : q < 16 := Nat.mod_lt _ (by decide)
  let I₀ : State → Prop := fun s => streamAadPPC64LE.pre s ∧ s.gpr .r3 = σ₁.gpr .r3 ∧
    s.gpr .r4 = σ₁.gpr .r4 ∧ s.gpr .r5 = σ₁.gpr .r5 ∧ s.gpr .r6 = σ₁.gpr .r6 ∧ s.gpr .r7 = σ₁.gpr .r7 ∧
    s.gpr .r8 = σ₁.gpr .r8 ∧ s.sp = σ₁.sp
  refine ⟨I₀, ⟨h₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨h₂, q3.symm, q4.symm, q5.symm, q6.symm, q7.symm,
    q8.symm, qsp.symm⟩, ?_⟩
  refine CT.seq (J := AbsI (σ₁.gpr .r3) (σ₁.gpr .r4) (σ₁.gpr .r8) σ₁.sp 16 (σ₁.gpr .r6) (σ₁.gpr .r7).toNat q)
    ?_ (fun s ⟨hs, e3, e4, e5, e6, e7, e8, esp⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ := streamAadPre_taint
    exact CT.taintEq (I := I₀) _ σ₁.gpr σ₁.sp (fun s ⟨_, e3, e4, e5, e6, e7, e8, esp⟩ =>
      ⟨esp, by simp [e3, e4, e5, e6, e7, e8]⟩) hc
  · have hx : (List.replicate q (0 : Byte)).length % 16 = (s.gpr .r5).toNat % 16 := by
      rw [List.length_replicate, e5, Nat.mod_mod]
    refine WP.mono (aad_entry hs hx) fun s₁ ⟨_, h29, h30, h31, hIn, _⟩ => ?_
    rw [e3] at h29 hIn
    rw [e4] at h30
    rw [e8] at h31
    rw [e6, e7, esp] at hIn
    exact ⟨s₁.gpr, _, _, h29, h30, h31, by rw [List.length_replicate, Nat.mod_mod], hIn⟩
  refine CT.seq (J := fun s => s.gpr .r31 = σ₁.gpr .r8 ∧ s.sp = σ₁.sp) (absorb_ct L (.inr rfl) hq16)
    (fun s ⟨V, H, x, h29, h30, h31, _, hs⟩ => WP.mono (absorb_ok (L.v h29 h30 h31) (.inr rfl) hs)
      fun s₂ h₂ => ⟨(h₂.env.fr _ (by decide)).trans h31, h₂.env.sp⟩) ?_
  obtain ⟨_, hc⟩ := restore_taint
  exact CT.taintEq _ (fun _ => σ₁.gpr .r8) σ₁.sp (fun s ⟨e31, esp⟩ => ⟨esp, by simp [e31]⟩) hc

end VG.Proof.AesGcm.PPC64LE
