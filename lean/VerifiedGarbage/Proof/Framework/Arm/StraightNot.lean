module

public import VerifiedGarbage.Proof.Framework.Arm.Straight
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-!
# ARMv7: straight-line bitwise code with complements, by evaluation

`Framework/Arm/Straight.lean`'s evaluator, with `bic` (`a ∧ ¬b`) and `mvn`
(`¬b`) too: the complement of an abstract value is its XOR with the domain's
constant of all ones, so a domain with that constant (the truth tables,
`Bitslice.table`) evaluates them. `stepN` is `step` on every other
instruction, and `runN` says of a block `evalN` accepts what `run` says of
one `eval` accepts.
-/

@[expose] public section

namespace VG.Arm.Straight

open VG.Bitslice

variable {α : Type}

section
variable (D : Dom α 32) (c : Cfg) (ext : Nat → Option α)

/-- The complement of an abstract value. -/
def notAbs (a : α) : Option α := (D.const (BitVec.allOnes 32)).bind (D.xor a)

/-- The instruction's effect on the abstract values: `step`, and `bic` and `mvn`. -/
def stepN (e : Env α) (i : Instr) : Option (Env α) :=
  match i with
  | .dp .bic d n o =>
    if d = c.base ∨ d = c.ext then none else
    match e.reg n, op2Abs D e o with
    | some a, some b => ((notAbs D b).bind (D.and a)).map fun r => e.set d (some r) none
    | _, _ => none
  | .mvn d o =>
    if d = c.base ∨ d = c.ext then none else
    ((op2Abs D e o).bind (notAbs D)).map fun r => e.set d (some r) none
  | i => step D c ext e i

/-- The block's effect on the abstract values. -/
def evalN : List Instr → Env α → Option (Env α)
  | [], e => some e
  | i :: is, e => (stepN D c ext e i).bind (evalN is)

end

namespace Kernel

open VG.Bitslice.Machine (Op Ent bind)

section
variable (D : Dom α 32) (c : Cfg) (ext : Nat → Option α)

/-- `notAbs`. -/
noncomputable def notK (a : α) : Option α := bind (D.xor a) (D.const (BitVec.allOnes 32))

noncomputable def opN : Instr → Op Reg (Ent α) α :=
  opW D c ext (valK2 D fun a b => bind (D.and a) (notK D b)) (valK1 D (notK D))

theorem notK_eq : notK D = notAbs D := funext fun _ => Machine.bind_eq ..

variable {D c ext}

/-- What the kernel's evaluator computes, `stepN` does. -/
theorem step_of_opN {e : Env α} {i : Instr} {m : Machine.Env Reg (Ent α) α}
    (h : Machine.step (toM e) (opN D c ext i) = some m) : (stepN D c ext e i).map toM = some m := by
  rcases step_of_opW h with h | ⟨d, n, o, rfl, hd, h⟩ | ⟨d, o, rfl, hd, h⟩
  · rw [← h]
    cases i with
    | mvn d o => cases h
    | dp op d n o =>
      cases op with
      | bic =>
        simp only [step] at h
        split at h
        · cases h
        · split at h <;> cases h
      | _ => rfl
    | _ => rfl
  · have := valK2_step h
    simp only [stepN]; rw [ite_eq_right hd, ← this, notK_eq]
    cases e.reg n with
    | none => rfl
    | some a =>
      cases op2Abs D e o with
      | none => rfl
      | some b => show _ = Option.map toM (Option.map _ (Machine.bind _ _)); rw [Machine.bind_eq]
  · have := valK1_step h
    simp only [stepN]; rw [ite_eq_right hd, ← this, notK_eq]

/-- What the kernel's evaluator computes, `evalN` does. -/
theorem eval_of_opN {is : List Instr} {e : Env α} {m : Machine.Env Reg (Ent α) α}
    (h : Machine.eval (opN D c ext) is (toM e) = some m) : ∃ e', evalN D c ext is e = some e' ∧ toM e' = m := by
  induction is generalizing e with
  | nil => exact ⟨e, rfl, Option.some.inj h⟩
  | cons i is ih =>
    simp only [Machine.eval, Option.bind_eq_some_iff] at h
    obtain ⟨m₁, h₁, h₂⟩ := h
    obtain ⟨e₁, he₁, rfl⟩ := Option.map_eq_some_iff.mp (step_of_opN h₁)
    obtain ⟨e', he', hm⟩ := ih h₂
    exact ⟨e', by rw [evalN, he₁]; exact he', hm⟩

end

end Kernel

section
variable (D : Dom α 32) (c : Cfg) (ext : Nat → Option α)

/-- Evaluates the block and checks `post` of the result, for the kernel. -/
noncomputable def checkN (is : List Instr) (e : Env α) (post : Env α → Bool) : Bool :=
  Machine.run (Kernel.toM e) 4 (Nat.log2 c.slots + 1) (Kernel.opN D c ext) (fun e => post (Kernel.ofM e)) is

theorem of_checkN {is : List Instr} {e : Env α} {post : Env α → Bool}
    (h : checkN D c ext is e post = true) : ∃ e', evalN D c ext is e = some e' ∧ post e' = true := by
  obtain ⟨m, hm, hp⟩ := Machine.run_sound h
  obtain ⟨e', he, rfl⟩ := Kernel.eval_of_opN hm
  rw [Kernel.ofM_toM] at hp
  exact ⟨e', he, hp⟩

theorem checkN_mono {is : List Instr} {e : Env α} {p q : Env α → Bool}
    (hpq : ∀ e, p e = true → q e = true) (h : checkN D c ext is e p = true) :
    checkN D c ext is e q = true := Machine.run_mono (fun _ => hpq _) h

end

section
variable {D : Dom α 32} {R : α → BitVec 32 → Prop} {c : Cfg} {ext : Nat → Option α}

theorem notAbs_ok (hD : D.Sound R) {a b : α} {x : BitVec 32} (ha : R a x) (h : notAbs D a = some b) :
    R b (~~~x) := by
  obtain ⟨o, ho, hb⟩ := Option.bind_eq_some_iff.mp h
  have := hD.xor ha (hD.const ho) hb
  rwa [BitVec.xor_allOnes] at this

theorem stepN_ok (hD : D.Sound R) {e e' : Env α} {s : State} (hok : Ok c s)
    (hrel : Rel R c ext e s) {i : Instr} (h : stepN D c ext e i = some e') :
    ∃ s', exec i s = some s' ∧ Post R c ext e' s s' (fun r => dstOf i = some r) := by
  cases i with
  | mvn d o =>
    simp only [stepN] at h
    split at h
    · cases h
    rename_i hd
    simp only [not_or] at hd
    obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨b, hb, hn⟩ := Option.bind_eq_some_iff.mp hr
    obtain ⟨v, hv, hR⟩ := op2Abs_ok hD hrel hb
    refine ⟨_, by simp only [exec, hv, Option.map_some]; rfl, ?_⟩
    refine (post_set hok hrel (a := some r) (cv := none) (fun x hx => ?_) (fun _ h => by cases h)
      hd.1 hd.2).writes fun r h => by simp [dstOf, h]
    cases hx
    exact notAbs_ok hD hR hn
  | dp op d n o =>
    cases op with
    | bic =>
      simp only [stepN] at h
      split at h
      · cases h
      rename_i hd
      simp only [not_or] at hd
      split at h
      · rename_i a b ha hb
        obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨nb, hnb, hand⟩ := Option.bind_eq_some_iff.mp hr
        obtain ⟨v, hv, hR⟩ := op2Abs_ok hD hrel hb
        have hRa := hrel.reg n a ha
        refine ⟨_, by simp only [exec, hv, Option.map_some]; rfl, ?_⟩
        refine (post_set hok hrel (a := some r) (cv := none) (fun x hx => ?_) (fun _ h => by cases h)
          hd.1 hd.2).writes fun r h => by simp [dstOf, h]
        cases hx
        exact hD.and hRa (notAbs_ok hD hR hnb) hand
      · cases h
    | add | sub | and | orr | eor => exact step_ok hD hok hrel h
  | _ => exact step_ok hD hok hrel h

/-- Running a block that the abstract evaluator accepts: it does not fault,
and the machine state is related to the abstract result. -/
theorem runN (hD : D.Sound R) {is : List Instr} {e e' : Env α} {s : State} (hok : Ok c s)
    (hrel : Rel R c ext e s) (h : evalN D c ext is e = some e') :
    ∃ s', runBlock isa is s = some s' ∧
      Post R c ext e' s s' (fun r => (is.all fun i => !clobbers i r) = false) := by
  induction is generalizing e s with
  | nil =>
    cases h
    exact ⟨s, runBlock_nil, hrel, hok, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, Frame.refl _ _⟩
  | cons i is ih =>
    simp only [evalN, Option.bind_eq_some_iff] at h
    obtain ⟨e₁, h₁, h₂⟩ := h
    obtain ⟨s₁, hs₁, p₁⟩ := stepN_ok hD hok hrel h₁
    obtain ⟨s', hs', p⟩ := ih p₁.ok p₁.rel h₂
    refine ⟨s', by rw [runBlock_cons, hs₁, runStep_some]; exact hs', p.rel, p.ok,
      p.rd.trans p₁.rd, p.wr.trans p₁.wr, p.sp.trans p₁.sp, p.base.trans p₁.base,
      p.ext.trans p₁.ext, fun r hr => ?_, ?_⟩
    · simp only [List.all_cons, Bool.and_eq_false_iff, not_or] at hr
      exact (p.other r hr.2).trans (p₁.other r fun h => hr.1 (by simp [clobbers_of_dstOf h]))
    · refine p₁.frame.trans ?_
      have := p.frame
      simp only [slotRegion, p₁.base] at this
      exact this

end

end VG.Arm.Straight
