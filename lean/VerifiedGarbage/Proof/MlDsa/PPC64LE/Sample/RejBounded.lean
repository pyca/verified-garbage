module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Sample.RejBoundedCT
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.MlKem.PPC64LE.Sample
import VerifiedGarbage.Proof.MlKem.PPC64LE.SampleCT
import VerifiedGarbage.Proof.MlKem.PPC64LE.HashCT
import VerifiedGarbage.Proof.MlDsa.PPC64LE.Sample.RejNttCT
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.SigEval
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.MlDsa.PPC64LE.Sample.RejBoundedCT
meta import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.Sample
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.SampleCT
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.HashCT
meta import VerifiedGarbage.Proof.MlDsa.PPC64LE.Sample.RejNttCT
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.SigEval
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Step
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.MlDsa.PPC64LE.Sample.RejBoundedRun
meta import VerifiedGarbage.Proof.MlDsa.PPC64LE.Sample.RejBoundedRun

/-!
# ML-DSA on PPC64LE: `vg_mldsa_rej_bounded_poly`, constant time and `Verified`

As on 32-bit ARM (`Proof/MlDsa/Arm/Sample/RejBounded.lean`). Two runs from
entry states that agree on the public data (the pointers, the low 32 bits of
`η`, the stack pointer, and which half-bytes of the XOF output are accepted,
`rejBoundedLeak`) leak the same trace (`all_ct`): the prologue and the blocks
around the loop by the taint analysis, the sponge by `sponge_ct`, the branch on
`η` because `η` zero-extended is the same in both runs, and the loop
iteration by iteration (`loop_ct`), since the half-bytes of the first 544
bytes of output are accepted alike (`leak_hbOks`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.Sample.RejBounded

open VG VG.PPC64LE
open VG.Proof.MlDsa.PPC64LE.Sample
open VG.Impl.MlDsa.PPC64LE.Sample
open VG.Proof.MlDsa.Sample (hbOks leak_hbOks rejBounded_some rejBounded_none stored_polyIs ifT ifF rbFold
  H_length)
open VG.Proof.MlKem.PPC64LE (relct_noMem)
open VG.Proof.MlKem.PPC64LE.Sample (taint_block relct_wp)
open VG.Spec.MlDsa (H rejBoundedLeak)
open VG.Proof.MlDsa (rejBoundedContract rejBoundedSig)
open VG.Spec.Sha3 (bytesAt)

theorem zx_congr {x y : BitVec 64} (h : x.setWidth 32 = y.setWidth 32) : zx x = zx y :=
  BitVec.eq_of_toNat_eq (by rw [zx_toNat, zx_toNat, h])

theorem Lf_zero (η : Nat) (X : List Byte) : Lf η X 0 = [] := by simp [Lf, rbFold]

/-- Two runs, from entry states that agree on the public data. -/
structure Two (σ₁ σ₂ : State) : Prop where
  hp₁ : SpOk (spOf σ₁) σ₁
  hp₂ : SpOk (spOf σ₂) σ₂
  hη : etaOf σ₁ = 2 ∨ etaOf σ₁ = 4
  sp : σ₁.sp = σ₂.sp
  r3 : σ₁.gpr .r3 = σ₂.gpr .r3
  r4 : (σ₁.gpr .r4).setWidth 32 = (σ₂.gpr .r4).setWidth 32
  r5 : σ₁.gpr .r5 = σ₂.gpr .r5
  r6 : σ₁.gpr .r6 = σ₂.gpr .r6
  leak : rejBoundedLeak (etaOf σ₁) ((spOf σ₁).msg σ₁) = rejBoundedLeak (etaOf σ₂) ((spOf σ₂).msg σ₂)

section
variable {σ₁ σ₂ : State} (h : Two σ₁ σ₂)
include h

theorem sp_eq : spOf σ₂ = spOf σ₁ := by simp only [spOf, h.r3, h.r5, h.r6]

theorem eta_eq : etaOf σ₂ = etaOf σ₁ := by simp only [etaOf, h.r4]

theorem oks : (X σ₁).map (hbOks (etaOf σ₁)) = (X σ₂).map (hbOks (etaOf σ₁)) := by
  have hl := h.leak
  rw [eta_eq h] at hl
  exact leak_hbOks hl (B := 544) (by decide)

/-- The loop for `η`, from the sponge's output. -/
theorem rbLoop_ct {η : Nat} (hη : η = 2 ∨ η = 4) (ho : (X σ₁).map (hbOks η) = (X σ₂).map (hbOks η)) :
    RelCT isa (fun a b => (∃ x, J6 136 544 (spOf σ₁) σ₁ x a) ∧ (∃ y, J6 136 544 (spOf σ₂) σ₂ y b)) (rbLoop η)
      fun a b => Base σ₁ (X σ₁) 544 (Lf η (X σ₁) 544) a ∧ Base σ₂ (X σ₂) 544 (Lf η (X σ₂) 544) b := by
  refine RelCT.seq (R := fun (a b : State) => Base σ₁ (X σ₁) 0 (Lf η (X σ₁) 0) a ∧ Base σ₂ (X σ₂) 0 (Lf η (X σ₂) 0) b)
    (relct_wp (relct_noMem rfl) fun a b ⟨⟨x, ha⟩, ⟨y, hb⟩⟩ => ⟨?_, ?_⟩)
    (loop_ct h.hp₁ h.hp₂ h.sp h.r5 h.r6 hη (X_length σ₁) (X_length σ₂) ho)
  · rw [Lf_zero]; exact init_ok h.hp₁ ha
  · rw [Lf_zero]; exact init_ok h.hp₂ hb

/-- The whole function. -/
theorem all_ct : RelCT isa (fun a b => a = σ₁ ∧ b = σ₂) Impl.MlDsa.PPC64LE.Sample.rejBounded fun _ _ => True := by
  have hp₁ := h.hp₁
  have hp₂ := h.hp₂
  have eP := sp_eq h
  have hp₂' : SpOk (spOf σ₁) σ₂ := eP ▸ hp₂
  have ez : zx (σ₂.gpr .r4) = zx (σ₁.gpr .r4) := zx_congr h.r4.symm
  -- the prologue
  refine RelCT.seq (R := fun (a b : State) => (J0 (spOf σ₁) σ₁ a ∧ a.gpr .r27 = zx (σ₁.gpr .r4)) ∧
      (J0 (spOf σ₁) σ₂ b ∧ b.gpr .r27 = zx (σ₁.gpr .r4)))
    (relct_wp (pro_rb_ct (fun a b hab => by rw [hab.1, hab.2]; exact h.sp)
      fun a b hab => by rw [hab.1, hab.2]; exact h.r6) fun a b hab => ⟨?_, ?_⟩) ?_
  · rw [hab.1]; exact pro_rb hp₁ rfl rfl rfl rfl
  · rw [hab.2]; exact WP.mono (pro_rb hp₂' h.r3.symm h.r5.symm h.r6.symm rfl) fun _ x => ⟨x.1, x.2.trans ez⟩
  -- the sponge
  refine RelCT.seq (R := fun (a b : State) => ((∃ x, J6 136 544 (spOf σ₁) σ₁ x a) ∧ a.gpr .r27 = zx (σ₁.gpr .r4)) ∧
      ((∃ y, J6 136 544 (spOf σ₁) σ₂ y b) ∧ b.gpr .r27 = zx (σ₁.gpr .r4)))
    (relct_wp (RelCT.mono (sponge_ct hp₁ hp₂' h.sp (rate := 136) (outlen := 544) (by decide) (by decide))
      (fun a b hab => ⟨hab.1.1, hab.2.1⟩) fun _ _ h => h) fun a b hab =>
      ⟨WP.mono (sponge_ok hp₁ (by decide) (by decide) hab.1.1) fun _ x => ⟨⟨_, x⟩, (x.gp .r27 (by decide)).trans hab.1.2⟩,
        WP.mono (sponge_ok hp₂' (by decide) (by decide) hab.2.1) fun _ x =>
          ⟨⟨_, x⟩, (x.gp .r27 (by decide)).trans hab.2.2⟩⟩) ?_
  -- the branch on `η`, and the loop
  refine RelCT.seq (R := fun (a b : State) => Base σ₁ (X σ₁) 544 (Lf (etaOf σ₁) (X σ₁) 544) a ∧
      Base σ₂ (X σ₂) 544 (Lf (etaOf σ₁) (X σ₂) 544) b) ?_ ?_
  · refine RelCT.seq (R := fun (a b : State) => ((∃ x, J6 136 544 (spOf σ₁) σ₁ x a) ∧
        a.gpr .r12 = zx (σ₁.gpr .r4) - BitVec.ofNat 64 2) ∧
        ((∃ y, J6 136 544 (spOf σ₂) σ₂ y b) ∧ b.gpr .r12 = zx (σ₁.gpr .r4) - BitVec.ofNat 64 2))
      (relct_wp (relct_noMem rfl) fun a b hab => ⟨?_, ?_⟩) ?_
    · exact WP.mono (cmp_ok hp₁ ⟨hab.1.1, hab.1.2⟩) fun s' ⟨hs, e⟩ => ⟨hs.j6, e⟩
    · obtain ⟨⟨y, hy⟩, e27⟩ := hab.2
      have sj : SJ σ₂ b := ⟨⟨y, by rw [eP]; exact hy⟩, e27.trans ez.symm⟩
      exact WP.mono (cmp_ok hp₂ sj) fun s' ⟨hs, e⟩ => ⟨hs.j6, e.trans (by rw [ez])⟩
    have ho := oks h
    have hz : ∀ a b, (((∃ x, J6 136 544 (spOf σ₁) σ₁ x a) ∧ a.gpr .r12 = zx (σ₁.gpr .r4) - BitVec.ofNat 64 2) ∧
        ((∃ y, J6 136 544 (spOf σ₂) σ₂ y b) ∧ b.gpr .r12 = zx (σ₁.gpr .r4) - BitVec.ofNat 64 2)) →
        isa.eval (.zero .d .r12) a = some (decide (etaOf σ₁ = 2)) ∧ isa.eval (.zero .d .r12) b = isa.eval (.zero .d .r12) a :=
      fun a b hab => ⟨by rw [eval_zero, hab.1.2, eta_test], by rw [eval_zero, eval_zero, hab.1.2, hab.2.2]⟩
    rcases h.hη with e | e
    · rw [e] at ho ⊢
      refine RelCT.ite (fun a b hab => (hz a b hab).2.symm)
        (RelCT.mono (rbLoop_ct h (η := 2) (.inl rfl) ho) (fun a b hab => ⟨hab.1.1.1, hab.1.2.1⟩) fun _ _ h => h)
        (RelCT.of_false fun a b ⟨hab, he⟩ => by rw [(hz a b hab).1, e] at he; exact absurd he (by decide))
    · rw [e] at ho ⊢
      refine RelCT.ite (fun a b hab => (hz a b hab).2.symm)
        (RelCT.of_false fun a b ⟨hab, he⟩ => by rw [(hz a b hab).1, e] at he; exact absurd he (by decide))
        (RelCT.mono (rbLoop_ct h (η := 4) (.inr rfl) ho) (fun a b hab => ⟨hab.1.1.1, hab.1.2.1⟩) fun _ _ h => h)
  -- the end
  exact retEpi_ct (fun a b hab => base_sp hab.1 hab.2 h.sp) fun a b hab => by
    rw [hab.1.env.r31, hab.2.env.r31]; exact h.r6

end

/-! ## `Verified` -/

/-- The precondition, as `SpOk` and `η`. -/
theorem pre_of {s : State} (h : (rejBoundedContract PPC64LE.abi 48).pre s) :
    SpOk (spOf s) s ∧ (etaOf s = 2 ∨ etaOf s = 4) := by
  sig_pre [rejBoundedContract, rejBoundedSig, PPC64LE.abi, PPC64LE.argRegs] at h
  obtain ⟨h0, h1, h2, d1, d2, d3, b1, b2, b3, -, fa, fscr, he⟩ := h
  exact ⟨⟨by rw [h1]; exact List.mem_singleton_self _, h2, d1, d2, d3, b1, b2, b3,
    show (66 : Nat) < 2 ^ 64 by decide, fa, fscr, h0⟩, he⟩

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 2 | .r5 => 0x2000 | .r6 => 0x3000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 66⟩]
  wr := [⟨0x2000, 1024⟩, ⟨0x3000, 2048⟩]

end VG.Proof.MlDsa.PPC64LE.Sample.RejBounded

namespace VG.Proof.MlDsa.PPC64LE.Sample

open VG VG.PPC64LE
open VG.Proof.MlDsa.Sample (rbFold rejBounded_some rejBounded_none stored_polyIs ifT ifF)
open VG.Proof.MlDsa (rejBoundedContract rejBoundedSig)
open RejBounded

theorem rejBounded_verified :
    Verified PPC64LE.target Impl.MlDsa.PPC64LE.Sample.rejBounded (rejBoundedContract PPC64LE.abi 48) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, ⟨satState, ?_⟩⟩
  · obtain ⟨hp, hη⟩ := pre_of hs
    obtain ⟨t, s', he, h3, hst, ha⟩ := correct hp hη
    refine ⟨t, s', he, ha, ?_⟩
    have hL : Lf (etaOf s) (X s) 544 = rbFold (etaOf s) [] (X s) := by
      simp only [Lf]; rw [List.take_of_length_le (by rw [X_length])]
    rw [hL] at h3 hst
    sig_post [rejBoundedContract, rejBoundedSig, PPC64LE.abi, PPC64LE.argRegs]
    rw [h3]
    by_cases hf : (rbFold (etaOf s) [] (X s)).length = 256
    · rw [ifT hf]
      obtain ⟨hred, hpoly⟩ := stored_polyIs hst hf
      exact ⟨fun _ => hred, .inl ⟨rfl, { Spec.MlDsa.minBounds with rejBounded := 544 }, by
        show Option.map _ (Spec.MlDsa.rejBoundedPoly _ 544 _) = _
        exact (rejBounded_some _ hf).trans (congrArg some hpoly.symm)⟩⟩
    · rw [ifF hf]
      exact ⟨fun h1 => absurd h1 (by decide), .inr ⟨rfl, by
        show Option.map _ (Spec.MlDsa.rejBoundedPoly _ 481 _) = none
        exact (congrArg (Option.map _) (rejBounded_none _ (B := 544) (by decide) hf)).trans rfl⟩⟩
  · obtain ⟨hp₁, hη⟩ := pre_of h₁
    obtain ⟨hp₂, -⟩ := pre_of h₂
    sig_pub [rejBoundedContract, rejBoundedSig, PPC64LE.abi, PPC64LE.argRegs] at hpub
    obtain ⟨hsp, hl, h3, h4, h5, h6⟩ := hpub
    exact (all_ct ⟨hp₁, hp₂, hη, hsp, h3, h4, h5, h6, hl⟩ s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  · sig_apply_check
    · decide +kernel
    · sig_reduce [rejBoundedContract, rejBoundedSig, PPC64LE.abi, PPC64LE.argRegs]
      sig_and_intros
      all_goals first
        | trivial
        | decide +kernel

end VG.Proof.MlDsa.PPC64LE.Sample
