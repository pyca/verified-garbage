module

import VerifiedGarbage.Proof.Argon2.PPC64LE.Derive.CTCall
import VerifiedGarbage.Proof.Argon2.PPC64LE.Derive.FillCT3
import VerifiedGarbage.Proof.Argon2.PPC64LE.Derive.FillCT1
import VerifiedGarbage.Proof.Argon2.PPC64LE.Derive.ReduceCT
import VerifiedGarbage.Proof.Argon2.PPC64LE.Derive.MemCT
import VerifiedGarbage.Proof.Argon2.PPC64LE.Derive.InitialCT
import VerifiedGarbage.Proof.Argon2.PPC64LE.Derive.Correct
import VerifiedGarbage.Proof.Argon2.PPC64LE.Derive.Locals
import VerifiedGarbage.Proof.Argon2.References
import VerifiedGarbage.Proof.Argon2.Iterations
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.Argon2.PPC64LE.Derive.CTCall
meta import VerifiedGarbage.Proof.Argon2.PPC64LE.Derive.FillCT3
meta import VerifiedGarbage.Proof.Argon2.PPC64LE.Derive.FillCT1
meta import VerifiedGarbage.Proof.Argon2.PPC64LE.Derive.ReduceCT
meta import VerifiedGarbage.Proof.Argon2.PPC64LE.Derive.MemCT
meta import VerifiedGarbage.Proof.Argon2.PPC64LE.Derive.InitialCT
meta import VerifiedGarbage.Proof.Argon2.PPC64LE.Derive.Correct
meta import VerifiedGarbage.Proof.Argon2.PPC64LE.Derive.Locals
meta import VerifiedGarbage.Proof.Argon2.References
meta import VerifiedGarbage.Proof.Argon2.Iterations
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
public import VerifiedGarbage.Proof.Argon2.PPC64LE.Derive.CTBase

/-!
# Argon2 on PPC64LE: the derivation is constant time

`body_rel`: the body leaks the same trace in two runs with the same public
data and the same data-dependent references (`derivePPC.pub`), piece by
piece; `derive_ct`: so does the whole function, in its frame.
-/

@[expose] public section

namespace VG.Proof.Argon2.PPC64LE.Derive

open VG VG.PPC64LE
open VG.Spec.Blake2 (bytesAt)

namespace Two
variable {s₀₁ s₀₂ : State} (T : Two s₀₁ s₀₂)
include T

/-- The setup and the parameters' block leak the same trace in two runs. -/
theorem parameters_rel :
    RelCT isa (fun s₁ s₂ => s₁ = entry s₀₁ ∧ s₂ = entry s₀₂)
      (.block (Impl.Argon2.PPC64LE.Derive.setup ++ Impl.Argon2.PPC64LE.Derive.parameters)) fun _ _ => True :=
  RelCT.taint (A := frameTaint) (⟨RegSet.ofList [], 0⟩ : FrameTaint.T) (fun s₁ s₂ ⟨h₁, h₂⟩ => by
      subst h₁ h₂
      exact ⟨⟨by rw [entry_sp, entry_sp, T.pb.E_eq], fun r hr => by simp [RegSet.mem_ofList] at hr⟩,
        fun k _ hb => by simp at hb⟩)
    (by taint_decide)

/-- The body leaks the same trace in two runs with the same data-dependent
references. -/
theorem body_rel
    (href : Spec.Argon2.references (prm s₀₁) (pwB s₀₁) (saltB s₀₁) (secB s₀₁) (adB s₀₁) =
      Spec.Argon2.references (prm s₀₂) (pwB s₀₂) (saltB s₀₂) (secB s₀₂) (adB s₀₂)) :
    RelCT isa (fun s₁ s₂ => s₁ = entry s₀₁ ∧ s₂ = entry s₀₂) Impl.Argon2.PPC64LE.Derive.body
      fun _ _ => True := by
  have pe := T.pb.prm_eq
  have L8 := laneLen_ge T.hp₁
  have hind := Proof.Argon2.references_injective (prm s₀₁) (by omega) (pwB s₀₁) (saltB s₀₁) (secB s₀₁)
    (adB s₀₁) (pwB s₀₂) (saltB s₀₂) (secB s₀₂) (adB s₀₂) (by rw [href, pe])
  rw [← Proof.Argon2.iterations_fill, ← Proof.Argon2.iterations_fill] at hind
  have par : ∀ {s₀ : State}, DPre s₀ → ∀ s, s = entry s₀ →
      WP isa (.block (Impl.Argon2.PPC64LE.Derive.setup ++ Impl.Argon2.PPC64LE.Derive.parameters)) s
        fun t => Inv s₀ t ∧ Prm s₀ t := fun {s₀} hp s h => by
    subst h
    rw [← List.append_nil Impl.Argon2.PPC64LE.Derive.parameters, ← List.append_assoc]
    rw [List.append_assoc]
    exact setup_ok hp fun t i _ => parameters_ok hp i fun t' i' p' => WP.block_nil ⟨i', p'⟩
  unfold Impl.Argon2.PPC64LE.Derive.body
  refine RelCT.seqW T.parameters_rel (par T.hp₁) (par T.hp₂) ?_
  refine RelCT.seqW T.code_rel (fun s h => code_ok T.hp₁ h.1 h.2) (fun s h => code_ok T.hp₂ h.1 h.2) ?_
  refine RelCT.seqW T.memoryInit_rel (fun s h => memoryInit_ok T.hp₁ h.1 h.2.1 h.2.2)
    (fun s h => memoryInit_ok T.hp₂ h.1 h.2.1 h.2.2) ?_
  refine RelCT.seqW ((T.passes_rel (W₁ := Spec.Argon2.initMemory (prm s₀₁)
      (Spec.Argon2.initialHash (prm s₀₁) (pwB s₀₁) (saltB s₀₁) (secB s₀₁) (adB s₀₁)))
      (W₂ := Spec.Argon2.initMemory (prm s₀₂)
      (Spec.Argon2.initialHash (prm s₀₂) (pwB s₀₂) (saltB s₀₂) (secB s₀₂) (adB s₀₂)))
      (by rw [← pe]; exact hind)).mono (fun _ _ h => ⟨⟨h.1.1, h.1.2.1, h.1.2.2⟩, ⟨h.2.1, h.2.2.1, h.2.2.2⟩⟩)
      fun _ _ h => h)
    (fun s h => passes_ok T.hp₁ ⟨h.1, h.2.1, h.2.2⟩) (fun s h => passes_ok T.hp₂ ⟨h.1, h.2.1, h.2.2⟩) ?_
  refine RelCT.seqW (T.reduce_rel.mono (fun _ _ h => ⟨⟨h.1.inv, h.1.pr, h.1.mem⟩, ⟨h.2.inv, h.2.pr, h.2.mem⟩⟩)
      fun _ _ h => h)
    (fun s h => reduce_ok T.hp₁ h.inv h.pr h.mem) (fun s h => reduce_ok T.hp₂ h.inv h.pr h.mem) ?_
  refine RelCT.seqW (T.finalOutput_rel.mono (fun _ _ h => ⟨h.1.1, h.2.1⟩) fun _ _ h => h)
    (G₁ := fun t => Inv s₀₁ t) (G₂ := fun t => Inv s₀₂ t)
    (fun s h => (finalOutput_ok T.hp₁ h.1).mono fun _ h => h.1)
    (fun s h => (finalOutput_ok T.hp₂ h.1).mono fun _ h => h.1) ?_
  exact T.leaf [] [] (fun s₁ s₂ h => ⟨h.1, h.2, by simp, by simp⟩) ⟨_, by taint_decide⟩

end Two

/-! ## The frame -/

theorem alloc_eq {n : Nat} {s a : State} (h : isa.push (.alloc n) s = some a) : a = allocated n s := by
  simp only [isa, push] at h
  split at h <;> cases h
  rfl

/-- Two runs of a frame that reserves stack leak the same trace if the runs of
its body do. -/
theorem RelCT.allocFrame {n : Nat} {body : Prog isa} {P : State → State → Prop}
    (hsp : ∀ a b, P a b → a.sp = b.sp)
    (hb : RelCT isa (fun x y => ∃ a b, P a b ∧ isa.push (.alloc n) a = some x ∧ isa.push (.alloc n) b = some y)
      body fun _ _ => True) :
    RelCT isa P (.frame (.alloc n) body (.free n)) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | frame p₁ b₁ _ =>
    cases e₂ with
    | frame p₂ b₂ _ =>
      obtain ⟨ht, -⟩ := hb _ _ _ _ _ _ ⟨s₁, s₂, hp, p₁, p₂⟩ b₁ b₂
      refine ⟨?_, trivial⟩
      rw [ht]
      simp [addrs, hsp _ _ hp]

/-- The derivation leaks the same trace in two runs with the same public data. -/
theorem derive_rel :
    RelCT isa (fun s₁ s₂ => derivePPC.pre s₁ ∧ derivePPC.pre s₂ ∧ derivePPC.pub s₁ s₂)
      Impl.Argon2.PPC64LE.Derive.derive fun _ _ => True := by
  unfold Impl.Argon2.PPC64LE.Derive.derive
  refine RelCT.allocFrame (fun s₁ s₂ h => h.2.2.1.1) ?_
  intro a b t₁ t₂ a' b' ⟨s₁, s₂, ⟨h₁, h₂, hpub⟩, pa, pb⟩ e₁ e₂
  have ea := alloc_eq pa
  have eb := alloc_eq pb
  subst ea eb
  exact Two.body_rel ⟨h₁, h₂, hpub.1⟩ hpub.2 _ _ t₁ t₂ a' b' ⟨rfl, rfl⟩ e₁ e₂

theorem derive_ct : ConstantTime isa derivePPC.pre derivePPC.pub Impl.Argon2.PPC64LE.Derive.derive :=
  derive_rel.constantTime

end VG.Proof.Argon2.PPC64LE.Derive
