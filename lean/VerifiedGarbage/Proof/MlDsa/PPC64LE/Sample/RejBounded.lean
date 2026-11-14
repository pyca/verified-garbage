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
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Sample.RejBoundedRun
meta import VerifiedGarbage.Proof.MlDsa.PPC64LE.Sample.RejBoundedRun

/-!
# ML-DSA on PPC64LE: `vg_mldsa_rej_bounded_poly`, constant time and `Verified`

As on 32-bit ARM (`Proof/MlDsa/Arm/Sample/RejBounded.lean`). Two runs from
entry states that agree on the public data (the pointers, the low 32 bits of
`η`, the stack pointer, and which half-bytes of the XOF output are accepted,
`rejBoundedLeak`) leak the same trace (`all_ct`): the prologue and the blocks
around the loops by the taint analysis, each try (`rbTry_ct`) by `sponge_ct`,
the branch on `η` because `η` zero-extended is the same in both runs, and the
loop iteration by iteration (`loop_ct`), since the half-bytes of the first
544 bytes of output are accepted alike (`leak_hbOks`); so the tries sample as
many coefficients, and the test of whether the first sampled 256 agrees.
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.Sample.RejBounded

open VG VG.PPC64LE
open VG.Proof.MlDsa.PPC64LE.Sample
open VG.Impl.MlDsa.PPC64LE.Sample
open VG.Proof.MlDsa.Sample (hbOks leak_hbOks rejBounded_some rejBounded_none stored_polyIs ifT ifF rbFold
  H_length)
open VG.Proof.MlKem.PPC64LE (relct_noMem relct_nil)
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

theorem oks (n : Nat) (hn : n ≤ 544) : (X n σ₁).map (hbOks (etaOf σ₁)) = (X n σ₂).map (hbOks (etaOf σ₁)) := by
  have hl := h.leak
  rw [eta_eq h] at hl
  exact leak_hbOks hl (B := n) (Nat.le_trans hn (by decide))

/-- The loop for `η` over `n` bytes, from the sponge's output. -/
theorem rbLoop_ct {η : Nat} (hη : η = 2 ∨ η = 4) {n : Nat} (hn0 : 0 < n) (hn : n ≤ 544)
    (ho : (X n σ₁).map (hbOks η) = (X n σ₂).map (hbOks η)) :
    RelCT isa (fun a b => SJ n σ₁ a ∧ SJ n σ₂ b) (rbLoop η n)
      fun a b => ∃ t, Base σ₁ (X n σ₁) t (Lf η (X n σ₁) n) a ∧ Base σ₂ (X n σ₂) t (Lf η (X n σ₂) n) b := by
  refine RelCT.seq (R := fun (a b : State) => Base σ₁ (X n σ₁) 0 (Lf η (X n σ₁) 0) a ∧
      Base σ₂ (X n σ₂) 0 (Lf η (X n σ₂) 0) b)
    (relct_wp (relct_noMem rfl) fun a b ⟨ha, hb⟩ => ⟨?_, ?_⟩)
    (loop_ct h.hp₁ h.hp₂ h.sp h.r5 h.r6 hη (X_length n σ₁) (X_length n σ₂) ho hn0)
  · rw [Lf_zero]; exact init_ok h.hp₁ hn ha
  · rw [Lf_zero]; exact init_ok h.hp₂ hn hb

/-- A try with `n` bytes: the sponge, the branch on `η`, and the loop. -/
theorem rbTry_ct {n : Nat} (hn0 : 0 < n) (hn : n ≤ 544) :
    RelCT isa (fun a b => (J0 (spOf σ₁) σ₁ a ∧ a.gpr .r27 = zx (σ₁.gpr .r4)) ∧
      (J0 (spOf σ₁) σ₂ b ∧ b.gpr .r27 = zx (σ₁.gpr .r4))) (rbTry n)
      fun a b => ∃ t, Base σ₁ (X n σ₁) t (Lf (etaOf σ₁) (X n σ₁) n) a ∧
        Base σ₂ (X n σ₂) t (Lf (etaOf σ₁) (X n σ₂) n) b := by
  have hp₁ := h.hp₁
  have hp₂ := h.hp₂
  have eP := sp_eq h
  have hp₂' : SpOk (spOf σ₁) σ₂ := eP ▸ hp₂
  have ez : zx (σ₂.gpr .r4) = zx (σ₁.gpr .r4) := zx_congr h.r4.symm
  -- the sponge
  refine RelCT.seq (R := fun (a b : State) => SJ n σ₁ a ∧
      ((∃ y, J6 136 n (spOf σ₁) σ₂ y b) ∧ b.gpr .r27 = zx (σ₁.gpr .r4)))
    (relct_wp (RelCT.mono (sponge_ct hp₁ hp₂' h.sp (rate := 136) (outlen := n) (by decide) (by omega_using [hn]))
      (fun a b hab => ⟨hab.1.1, hab.2.1⟩) fun _ _ h => h) fun a b hab =>
      ⟨WP.mono (sponge_ok hp₁ (by decide) (by omega_using [hn]) hab.1.1) fun _ x => ⟨⟨_, x⟩, (x.gp .r27 (by decide)).trans hab.1.2⟩,
        WP.mono (sponge_ok hp₂' (by decide) (by omega_using [hn]) hab.2.1) fun _ x =>
          ⟨⟨_, x⟩, (x.gp .r27 (by decide)).trans hab.2.2⟩⟩) ?_
  -- the branch on `η`, and the loop
  refine RelCT.seq (R := fun (a b : State) => (SJ n σ₁ a ∧ a.gpr .r12 = zx (σ₁.gpr .r4) - BitVec.ofNat 64 2) ∧
      (SJ n σ₂ b ∧ b.gpr .r12 = zx (σ₁.gpr .r4) - BitVec.ofNat 64 2))
    (relct_wp (relct_noMem rfl) fun a b hab => ⟨cmp_ok hp₁ hab.1, ?_⟩) ?_
  · obtain ⟨⟨y, hy⟩, e27⟩ := hab.2
    have sj : SJ n σ₂ b := ⟨⟨y, by rw [eP]; exact hy⟩, e27.trans ez.symm⟩
    exact WP.mono (cmp_ok hp₂ sj) fun s' ⟨hs, e⟩ => ⟨hs, e.trans (by rw [ez])⟩
  have ho := oks h n hn
  have hz : ∀ a b, ((SJ n σ₁ a ∧ a.gpr .r12 = zx (σ₁.gpr .r4) - BitVec.ofNat 64 2) ∧
      (SJ n σ₂ b ∧ b.gpr .r12 = zx (σ₁.gpr .r4) - BitVec.ofNat 64 2)) →
      isa.eval (.zero .d .r12) a = some (decide (etaOf σ₁ = 2)) ∧
        isa.eval (.zero .d .r12) b = isa.eval (.zero .d .r12) a :=
    fun a b hab => ⟨by rw [eval_zero, hab.1.2, eta_test], by rw [eval_zero, eval_zero, hab.1.2, hab.2.2]⟩
  rcases h.hη with e | e
  · rw [e] at ho ⊢
    refine RelCT.ite (fun a b hab => (hz a b hab).2.symm)
      (RelCT.mono (rbLoop_ct h (η := 2) (.inl rfl) hn0 hn ho) (fun a b hab => ⟨hab.1.1.1, hab.1.2.1⟩)
        fun _ _ h => h)
      (RelCT.of_false fun a b ⟨hab, he⟩ => by rw [(hz a b hab).1, e] at he; exact absurd he (by decide))
  · rw [e] at ho ⊢
    refine RelCT.ite (fun a b hab => (hz a b hab).2.symm)
      (RelCT.of_false fun a b ⟨hab, he⟩ => by rw [(hz a b hab).1, e] at he; exact absurd he (by decide))
      (RelCT.mono (rbLoop_ct h (η := 4) (.inr rfl) hn0 hn ho) (fun a b hab => ⟨hab.1.1.1, hab.1.2.1⟩)
        fun _ _ h => h)

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
  -- the try with 272 bytes
  refine RelCT.seq (rbTry_ct h (n := 272) (by decide) (by decide)) (RelCT.exists_ fun t => ?_)
  -- the test of `j = 256`, and the try with 544 bytes if it fails
  refine RelCT.seq (R := fun (a b : State) => (∃ X t L, Base σ₁ X t L a) ∧ (∃ X t L, Base σ₂ X t L b)) ?_ ?_
  · refine RelCT.seq (R := fun (a b : State) =>
        (Base σ₁ (X 272 σ₁) t (Lf (etaOf σ₁) (X 272 σ₁) 272) a ∧
          isa.eval (.zero .d .r12) a = some (decide ((Lf (etaOf σ₁) (X 272 σ₁) 272).length = 256))) ∧
        (Base σ₂ (X 272 σ₂) t (Lf (etaOf σ₁) (X 272 σ₂) 272) b ∧
          isa.eval (.zero .d .r12) b = some (decide ((Lf (etaOf σ₁) (X 272 σ₂) 272).length = 256))))
      (relct_wp (relct_noMem rfl) fun a b hab => ⟨jtest_ok hp₁ hab.1, jtest_ok hp₂ hab.2⟩) ?_
    have hl := len_eq (oks h 272 (by decide)) 272
    refine RelCT.ite (fun a b hab => by rw [hab.1.2, hab.2.2, hl]) ?_ ?_
    · exact RelCT.mono relct_nil (fun _ _ h => h) fun a b hab => ⟨⟨_, _, _, hab.1.1.1⟩, ⟨_, _, _, hab.1.2.1⟩⟩
    · refine RelCT.mono (rbTry_ct h (n := 544) (by decide) (by decide)) (fun a b hab => ⟨?_, ?_⟩)
        fun a b ⟨_, hab⟩ => ⟨⟨_, _, _, hab.1⟩, ⟨_, _, _, hab.2⟩⟩
      · exact ⟨⟨hab.1.1.1.env, hab.1.1.1.r29, hab.1.1.1.r28⟩, hab.1.1.1.r27⟩
      · have b₂ := hab.1.2.1
        exact ⟨eP ▸ ⟨b₂.env, b₂.r29, b₂.r28⟩, b₂.r27.trans ez⟩
  -- the end
  exact retEpi_ct (fun a b ⟨⟨_, _, _, ha⟩, ⟨_, _, _, hb⟩⟩ => base_sp ha hb h.sp)
    fun a b ⟨⟨_, _, _, ha⟩, ⟨_, _, _, hb⟩⟩ => by rw [ha.env.r31, hb.env.r31]; exact h.r6

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
    have key : ∀ n, Lf (etaOf s) (X n s) n = rbFold (etaOf s) [] (X n s) := fun n => by
      simp only [Lf]; rw [List.take_of_length_le (by rw [X_length])]
    sig_post [rejBoundedContract, rejBoundedSig, PPC64LE.abi, PPC64LE.argRegs]
    rw [h3]
    by_cases h1 : (Lf (etaOf s) (X 272 s) 272).length = 256
    · have eL : Lr (etaOf s) s = rbFold (etaOf s) [] (X 272 s) := by rw [Lr, ifT h1, key]
      rw [key] at h1
      rw [eL] at hst ⊢
      rw [ifT h1]
      obtain ⟨hred, hpoly⟩ := stored_polyIs hst h1
      exact ⟨fun _ => hred, .inl ⟨rfl, { Spec.MlDsa.minBounds with rejBounded := 272 }, by
        show Option.map _ (Spec.MlDsa.rejBoundedPoly _ 272 _) = _
        exact (rejBounded_some _ h1).trans (congrArg some hpoly.symm)⟩⟩
    · have eL : Lr (etaOf s) s = rbFold (etaOf s) [] (X 544 s) := by rw [Lr, ifF h1, key]
      rw [eL] at hst ⊢
      by_cases hf : (rbFold (etaOf s) [] (X 544 s)).length = 256
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
