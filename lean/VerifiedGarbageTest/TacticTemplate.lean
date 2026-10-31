module

public import VerifiedGarbage.Proof.Framework.TacticTemplate
public meta import VerifiedGarbage.Proof.Framework.TacticTemplate

/-!
# `tactic_template`

The arguments of a use replace the template's antiquotations (a splice of
simp lemmas, empty or not, before or after the template's own; a term), and
the template's names mean what they meant where it was defined.
-/

-- Public, as where the project defines its templates (a template is private
-- to a private scope, where its elaborator could not use it).
public section

namespace VG.Test.TacticTemplate

namespace Inner

theorem two_eq : (2 : Nat) = 1 + 1 := rfl

/-- `simp only` with `two_eq` (a name of this namespace), then the lemmas given. -/
tactic_template "two_simp" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| simp only [two_eq, $ts,*])

/-- `simp only` with the lemmas given, then `two_eq`. -/
tactic_template "two_simp'" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| simp only [$ts,*, two_eq])

/-- A constant with the name of a `simp` option. -/
def zeta : Nat := 0

/-- A constant with the name of a field (`Eq.symm`). -/
def symm : Nat := 0

/-- `simp` with configuration options whose names are also constants here
(`zeta`, and `decide` everywhere): they stay option names. -/
tactic_template "cfg_simp" : tactic => `(tactic| simp (config := { zeta := true }) only [two_eq])

tactic_template "cfg_simp'" : tactic => `(tactic| simp +zeta -decide -failIfUnchanged only [two_eq])

tactic_template "cfg_simp''" : tactic => `(tactic| simp (zeta := true) only [two_eq])

/-- `exact` the term given. -/
tactic_template "my_exact " t:term : tactic => `(tactic| exact $t)

/-- `exact` the symmetry of the proof given: a projection whose field (`symm`) is also
a constant here. -/
tactic_template "my_symm " t:term : tactic => `(tactic| exact ($t).symm)

/-- `constructor`, then a bullet for each goal, aligned with `constructor`: the body's
first line starts mid-line. -/
tactic_template "two_bullets" : tactic => `(tactic| (constructor
                                                     · exact rfl
                                                     · exact rfl))

/-- `simp only [two_eq]`, at the location given, if any (`$(loc)?`). -/
tactic_template "two_simp_at" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [two_eq] $(loc)?)

end Inner

-- Outside `Inner`: `two_eq` still names `Inner.two_eq`.
example : (2 : Nat) = 1 + 1 := by two_simp []
example : (2 : Nat) + 0 = 1 + 1 := by two_simp [Nat.add_zero]
example : (2 : Nat) + 0 * 5 = 1 + 1 := by two_simp [Nat.zero_mul, Nat.add_zero]
example : (2 : Nat) = 1 + 1 := by two_simp' []
example : (2 : Nat) + 0 = 1 + 1 := by two_simp' [Nat.add_zero]
example : (2 : Nat) = 1 + 1 := by cfg_simp
example : (2 : Nat) = 1 + 1 := by cfg_simp'
example : (2 : Nat) = 1 + 1 := by cfg_simp''
example : True := by my_exact trivial
example (h : 1 = 2) : 1 = 2 := by my_exact h
example (h : (1 : Nat) = 2) : 2 = 1 := by my_symm h
example : (2 : Nat) = 2 ∧ (3 : Nat) = 3 := by two_bullets
-- An optional argument, absent and present.
example : (2 : Nat) = 1 + 1 := by two_simp_at
example (h : (2 : Nat) = 3) : 1 + 1 = 3 := by two_simp_at at h; exact h

end VG.Test.TacticTemplate
