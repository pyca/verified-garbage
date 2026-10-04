import VerifiedGarbage.Proof.Argon2.Arm.Derive.FillCT3
import VerifiedGarbage.Proof.Argon2.Arm.Derive.ReduceCT
import VerifiedGarbage.Proof.Argon2.References

/-!
# Argon2 on ARMv7: the derivation is constant time

`body_rel`: the body leaks the same trace in two runs with the same public
data and the same data-dependent references (`deriveArm.pub`), piece by
piece; `derive_ct`: so does the whole function, in its frames.
-/

namespace VG.Proof.Argon2.Arm.Derive

open VG VG.Arm
open VG.Spec.Blake2 (bytesAt)

namespace Two
variable {s₀₁ s₀₂ : State} (T : Two s₀₁ s₀₂)
include T

/-- The parameters' block leaks the same trace in two runs. -/
theorem parameters_rel :
    RelCT isa (fun s₁ s₂ => s₁ = entry s₀₁ ∧ s₂ = entry s₀₂)
      (.block (.addSp .r11 0 :: Impl.Argon2.Arm.Derive.parameters)) fun _ _ => True := by
  rw [← List.singleton_append]
  refine RelCT.block_split (RelCT.seqW (F₁ := fun s => s = entry s₀₁) (F₂ := fun s => s = entry s₀₂)
    (RelCT.quiet fun _ => rfl)
    (fun s h => by subst h; exact inv_start fun t i _ _ => WP.block_nil i)
    (fun s h => by subst h; exact inv_start fun t i _ _ => WP.block_nil i) ?_)
  exact T.leafI [] (fun s₁ s₂ h => ⟨h.1, h.2, by simp⟩) ⟨_, by taint_decide⟩

/-- The body leaks the same trace in two runs with the same data-dependent
references. -/
theorem body_rel
    (href : Spec.Argon2.references (prm s₀₁) (pwB s₀₁) (saltB s₀₁) (secB s₀₁) (adB s₀₁) =
      Spec.Argon2.references (prm s₀₂) (pwB s₀₂) (saltB s₀₂) (secB s₀₂) (adB s₀₂)) :
    RelCT isa (fun s₁ s₂ => s₁ = entry s₀₁ ∧ s₂ = entry s₀₂) Impl.Argon2.Arm.Derive.body fun _ _ => True := by
  have pe := T.pb.prm_eq
  have L8 := laneLen_ge T.hp₁
  have hind := Proof.Argon2.references_injective (prm s₀₁) (by omega) (pwB s₀₁) (saltB s₀₁) (secB s₀₁) (adB s₀₁)
    (pwB s₀₂) (saltB s₀₂) (secB s₀₂) (adB s₀₂) (by rw [href, pe])
  rw [← Proof.Argon2.iterations_fill, ← Proof.Argon2.iterations_fill] at hind
  unfold Impl.Argon2.Arm.Derive.body
  refine RelCT.seqW T.parameters_rel (G₁ := fun t => Inv s₀₁ t ∧ Prm s₀₁ t)
    (G₂ := fun t => Inv s₀₂ t ∧ Prm s₀₂ t)
    (fun s h => by
      subst h
      rw [← List.append_nil (Instr.addSp .r11 0 :: Impl.Argon2.Arm.Derive.parameters)]
      exact parameters_ok T.hp₁ fun t i p => WP.block_nil ⟨i, p⟩)
    (fun s h => by
      subst h
      rw [← List.append_nil (Instr.addSp .r11 0 :: Impl.Argon2.Arm.Derive.parameters)]
      exact parameters_ok T.hp₂ fun t i p => WP.block_nil ⟨i, p⟩) ?_
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
  exact T.finalOutput_rel.mono (fun _ _ h => ⟨h.1.1, h.2.1⟩) fun _ _ h => h

end Two

/-! ## The frames -/

theorem alloc_eq {n : Nat} {s a : State} (h : isa.push (.alloc n) s = some a) : a = allocated n s := by
  simp only [isa, push] at h
  split at h <;> cases h
  rfl

/-- Two runs of a frame that reserves stack leak the same trace if the runs of
its body do; the stack pointer is where it was. -/
theorem RelCT.allocFrame {n : Nat} {body : Prog isa} {P : State → State → Prop}
    (hsp : ∀ a b, P a b → a.sp = b.sp)
    (hb : RelCT isa (fun x y => ∃ a b, P a b ∧ isa.push (.alloc n) a = some x ∧ isa.push (.alloc n) b = some y)
      body fun _ _ => True) :
    RelCT isa P (.frame (.alloc n) body (.free n)) fun a' b' => a'.sp = b'.sp := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  have q₁ := Exec.sp e₁
  have q₂ := Exec.sp e₂
  cases e₁ with
  | frame p₁ b₁ _ =>
    cases e₂ with
    | frame p₂ b₂ _ =>
      obtain ⟨ht, -⟩ := hb _ _ _ _ _ _ ⟨s₁, s₂, hp, p₁, p₂⟩ b₁ b₂
      refine ⟨?_, show s₁'.sp = s₂'.sp by rw [q₁, q₂, hsp _ _ hp]⟩
      rw [ht]
      rfl

/-- Loads from the stack pointer leak the same trace from the same stack pointer. -/
theorem ldrSps_trace : ∀ (l : List (Reg × Nat)) (s₁ s₂ : State) {a₁ a₂ : State} {t₁ t₂ : List Leak},
    s₁.sp = s₂.sp → execBlock isa (l.map fun p => Instr.ldrSp p.1 p.2) s₁ = some (a₁, t₁) →
    execBlock isa (l.map fun p => Instr.ldrSp p.1 p.2) s₂ = some (a₂, t₂) → t₁ = t₂
  | [], s₁, s₂, a₁, a₂, t₁, t₂, _, h₁, h₂ => by
    simp only [List.map_nil, execBlock, Option.some.injEq, Prod.mk.injEq] at h₁ h₂
    rw [← h₁.2, ← h₂.2]
  | p :: l, s₁, s₂, a₁, a₂, t₁, t₂, hsp, h₁, h₂ => by
    simp only [List.map_cons, execBlock] at h₁ h₂
    split at h₁
    · cases h₁
    rename_i b₁ x₁
    split at h₂
    · cases h₂
    rename_i b₂ x₂
    rw [Option.map_eq_some_iff] at h₁ h₂
    obtain ⟨⟨c₁, u₁⟩, r₁, e₁⟩ := h₁
    obtain ⟨⟨c₂, u₂⟩, r₂, e₂⟩ := h₂
    simp only [Prod.mk.injEq] at e₁ e₂
    rw [← e₁.2, ← e₂.2, ldrSps_trace l b₁ b₂ (by rw [exec_sp x₁, exec_sp x₂, hsp]) r₁ r₂]
    simp only [addrs, hsp]

theorem RelCT.restore {P : State → State → Prop} (hsp : ∀ a b, P a b → a.sp = b.sp) :
    RelCT isa P (.block Impl.Argon2.Arm.Derive.restoreRegs) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  rw [Exec.block_iff] at e₁ e₂
  exact ⟨ldrSps_trace _ s₁ s₂ (hsp _ _ hp) e₁ e₂, trivial⟩

/-- The derivation leaks the same trace in two runs with the same public data. -/
theorem derive_rel :
    RelCT isa (fun s₁ s₂ => deriveArm.pre s₁ ∧ deriveArm.pre s₂ ∧ deriveArm.pub s₁ s₂)
      Impl.Argon2.Arm.Derive.derive fun _ _ => True := by
  unfold Impl.Argon2.Arm.Derive.derive
  refine RelCT.frame (fun s₁ s₂ h => h.2.2.1.1) (RelCT.frame (fun a b ⟨s₁, s₂, h, pa, pb⟩ => by
      rw [push_push_sp pa, push_push_sp pb, h.2.2.1.1]) ?_)
  refine RelCT.seq (RelCT.allocFrame (fun a b ⟨x, y, ⟨s₁, s₂, h, pa, pb⟩, qa, qb⟩ => by
      rw [push_push_sp qa, push_push_sp qb, push_push_sp pa, push_push_sp pb, h.2.2.1.1]) ?_)
    (RelCT.restore fun _ _ h => h)
  intro a b t₁ t₂ a' b' ⟨x, y, ⟨u, v, ⟨s₁, s₂, ⟨h₁, h₂, hpub⟩, pu, pv⟩, px, py⟩, ha, hb⟩ e₁ e₂
  have eu := VG.Proof.Argon2.Arm.push_eq (by decide) pu
  have ev := VG.Proof.Argon2.Arm.push_eq (by decide) pv
  have ex := VG.Proof.Argon2.Arm.push_eq (by decide) px
  have ey := VG.Proof.Argon2.Arm.push_eq (by decide) py
  have ea := alloc_eq ha
  have eb := alloc_eq hb
  subst eu ev ex ey ea eb
  exact Two.body_rel ⟨h₁, h₂, hpub.1⟩ hpub.2 _ _ t₁ t₂ a' b' ⟨rfl, rfl⟩ e₁ e₂

theorem derive_ct : ConstantTime isa deriveArm.pre deriveArm.pub Impl.Argon2.Arm.Derive.derive :=
  derive_rel.constantTime

end VG.Proof.Argon2.Arm.Derive
