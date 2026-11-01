module

public import VerifiedGarbage.Proof.Gcm.RISCV64.Ghash
import VerifiedGarbage.Proof.AesGcm.RISCV64.CTBase
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Contract
import VerifiedGarbage.Proof.AesGcm.RISCV64.CTJ0
import VerifiedGarbage.Proof.AesGcm.RISCV64.InitCT
import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamInit
import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamAad
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.CTBase
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.Contract
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.CTJ0
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.InitCT
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamInit
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamAad
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
public import VerifiedGarbage.Impl.AesGcm.RISCV64
public import VerifiedGarbage.Proof.Aes.SboxSpec
public import VerifiedGarbage.Proof.Framework.Bitslice.Atoms
public import VerifiedGarbage.Proof.Framework.Inline
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint

/-!
# AES-GCM on RISC-V: `vg_aes_gcm_stream_init` and `vg_aes_gcm_stream_aad` are constant time

Untrusted: everything here is checked by Lean. The entry by the taint
analysis from the public arguments; then `j0` (`j0_ct`) or `absorb 16`
(`absorb_ct`) from the invariants the entry's correctness gives; then the
exit from `W`.
-/

@[expose] public section

namespace VG.Proof.AesGcm.RISCV64

open VG VG.RISCV64 VG.Impl.AesGcm.RISCV64

theorem streamInitPre_taint : ∃ h, (VG.Taint.check VG.RISCV64.taint
    (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4]) (.block streamInitPre) h).isSome = true := ⟨_, by taint_decide⟩

theorem streamAadPre_taint : ∃ h, (VG.Taint.check VG.RISCV64.taint
    (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4, .a5]) (.block streamAadPre) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem streamInit_ct : ConstantTime isa streamInitRISCV64.pre streamInitRISCV64.pub streamInit := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  obtain ⟨q3, q4, q5, q6, q7, qsp⟩ := hq
  have L : Lay (σ₁.gpr .a0) (σ₁.gpr .a3) (σ₁.gpr .a4) := by
    obtain ⟨-, -, dcs, dcw, -, -, dsw, wc, -, ws, ww, -, a0, a3, a4⟩ := h₁
    exact Lay.of wc ws ww dcs dcw dsw a0 a3 a4
  let I₀ : State → Prop := fun s => streamInitRISCV64.pre s ∧ s.gpr .a0 = σ₁.gpr .a0 ∧
    s.gpr .a1 = σ₁.gpr .a1 ∧ s.gpr .a2 = σ₁.gpr .a2 ∧ s.gpr .a3 = σ₁.gpr .a3 ∧ s.gpr .a4 = σ₁.gpr .a4 ∧
    s.sp = σ₁.sp
  refine ⟨I₀, ⟨h₁, rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨h₂, q3.symm, q4.symm, q5.symm, q6.symm, q7.symm,
    qsp.symm⟩, ?_⟩
  refine CT.seq (J := J0I (σ₁.gpr .a0) (σ₁.gpr .a3) (σ₁.gpr .a4) σ₁.sp (σ₁.gpr .a1) (σ₁.gpr .a2).toNat) ?_
    (fun s ⟨hs, e3, e4, e5, e6, e7, esp⟩ => WP.mono (si_entry hs) fun s₁ ⟨_, h29, h30, h31, hJ, _⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ := streamInitPre_taint
    exact CT.taintEq (I := I₀) _ σ₁.gpr σ₁.sp (fun s ⟨_, e3, e4, e5, e6, e7, esp⟩ =>
      ⟨esp, by simp [e3, e4, e5, e6, e7]⟩) hc
  · rw [e3] at h29
    rw [e6] at h30
    rw [e7] at h31
    rw [e3, e4, e5, esp] at hJ
    exact ⟨s₁.gpr, _, h29, h30, h31, hJ⟩
  refine CT.seq (J := fun s => s.gpr .s0 = σ₁.gpr .a4 ∧ s.sp = σ₁.sp) (j0_ct L)
    (fun s ⟨V, H, h29, h30, h31, hJ⟩ => WP.mono (j0_ok (L.v h29 h30 h31) hJ) fun s₂ h₂ =>
      ⟨(h₂.env.fr _ (by decide)).trans h31, h₂.env.sp⟩) ?_
  obtain ⟨_, hc⟩ := restore_taint
  exact CT.taintEq _ (fun _ => σ₁.gpr .a4) σ₁.sp (fun s ⟨e31, esp⟩ => ⟨esp, by simp [e31]⟩) hc

theorem streamAad_ct : ConstantTime isa streamAadRISCV64.pre streamAadRISCV64.pub streamAad := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  obtain ⟨q3, q4, q5, q6, q7, q8, qsp⟩ := hq
  have L : Lay (σ₁.gpr .a0) (σ₁.gpr .a1) (σ₁.gpr .a5) := by
    obtain ⟨-, -, dcs, dcw, -, -, dsw, wc, -, ws, ww, -, a0, a1, a5⟩ := h₁
    exact Lay.of wc ws ww dcs dcw dsw a0 a1 a5
  let q := (σ₁.gpr .a2).toNat % 16
  have hq16 : q < 16 := Nat.mod_lt _ (by decide)
  let I₀ : State → Prop := fun s => streamAadRISCV64.pre s ∧ s.gpr .a0 = σ₁.gpr .a0 ∧
    s.gpr .a1 = σ₁.gpr .a1 ∧ s.gpr .a2 = σ₁.gpr .a2 ∧ s.gpr .a3 = σ₁.gpr .a3 ∧ s.gpr .a4 = σ₁.gpr .a4 ∧
    s.gpr .a5 = σ₁.gpr .a5 ∧ s.sp = σ₁.sp
  refine ⟨I₀, ⟨h₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨h₂, q3.symm, q4.symm, q5.symm, q6.symm, q7.symm,
    q8.symm, qsp.symm⟩, ?_⟩
  refine CT.seq (J := AbsI (σ₁.gpr .a0) (σ₁.gpr .a1) (σ₁.gpr .a5) σ₁.sp 16 (σ₁.gpr .a3) (σ₁.gpr .a4).toNat q)
    ?_ (fun s ⟨hs, e3, e4, e5, e6, e7, e8, esp⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ := streamAadPre_taint
    exact CT.taintEq (I := I₀) _ σ₁.gpr σ₁.sp (fun s ⟨_, e3, e4, e5, e6, e7, e8, esp⟩ =>
      ⟨esp, by simp [e3, e4, e5, e6, e7, e8]⟩) hc
  · have hx : (List.replicate q (0 : Byte)).length % 16 = (s.gpr .a2).toNat % 16 := by
      rw [List.length_replicate, e5, Nat.mod_mod]
    refine WP.mono (aad_entry hs hx) fun s₁ ⟨_, h29, h30, h31, hIn, _⟩ => ?_
    rw [e3] at h29 hIn
    rw [e4] at h30
    rw [e8] at h31
    rw [e6, e7, esp] at hIn
    exact ⟨s₁.gpr, _, _, h29, h30, h31, by rw [List.length_replicate, Nat.mod_mod], hIn⟩
  refine CT.seq (J := fun s => s.gpr .s0 = σ₁.gpr .a5 ∧ s.sp = σ₁.sp) (absorb_ct L (.inr rfl) hq16)
    (fun s ⟨V, H, x, h29, h30, h31, _, hs⟩ => WP.mono (absorb_ok (L.v h29 h30 h31) (.inr rfl) hs)
      fun s₂ h₂ => ⟨(h₂.env.fr _ (by decide)).trans h31, h₂.env.sp⟩) ?_
  obtain ⟨_, hc⟩ := restore_taint
  exact CT.taintEq _ (fun _ => σ₁.gpr .a5) σ₁.sp (fun s ⟨e31, esp⟩ => ⟨esp, by simp [e31]⟩) hc

end VG.Proof.AesGcm.RISCV64
