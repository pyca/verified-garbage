import VerifiedGarbage.Proof.Framework.TacticTemplate

/-!
# `tactic_template`

The arguments of a use replace the template's antiquotations (a splice of
simp lemmas, empty or not, before or after the template's own; a term), and
the template's names mean what they meant where it was defined.
-/

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

/-- `simp` with configuration options whose names are also constants here
(`zeta`, and `decide` everywhere): they stay option names. -/
tactic_template "cfg_simp" : tactic => `(tactic| simp (config := { zeta := true }) only [two_eq])

tactic_template "cfg_simp'" : tactic => `(tactic| simp +zeta -decide -failIfUnchanged only [two_eq])

tactic_template "cfg_simp''" : tactic => `(tactic| simp (zeta := true) only [two_eq])

/-- `exact` the term given. -/
tactic_template "my_exact " t:term : tactic => `(tactic| exact $t)

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

end VG.Test.TacticTemplate
