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

/-- Evaluates the block and checks `post` of the result: for `decide`. -/
def checkN (is : List Instr) (e : Env α) (post : Env α → Bool) : Bool :=
  match evalN D c ext is e with
  | some e' => post e'
  | none => false

theorem of_checkN {is : List Instr} {e : Env α} {post : Env α → Bool}
    (h : checkN D c ext is e post = true) : ∃ e', evalN D c ext is e = some e' ∧ post e' = true := by
  unfold checkN at h
  split at h
  · exact ⟨_, by assumption, h⟩
  · cases h

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
