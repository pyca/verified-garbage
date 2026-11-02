module

public import VerifiedGarbage.Spec.Rsa

/-!
# The prime factors of a test key, from `(n, e, d)`

A test helper, not a specification: the known-answer tests of RSA's
specification (`Rsa.lean`, `RsaPss.lean`) take private keys as `(n, e, d)`
and need their factors `p` and `q` to check the CRT form. `factors` finds
them by SP 800-56B Rev. 2 Appendix C.1 with the candidates `g = 2, 3, …`,
which works for any exponent, where Appendix C.2 (`Spec.Rsa.recoverDet`)
needs a small one. The tests check what they find (`p q = n`).
-/

@[expose] public section

namespace VG.Test.Rsa

open VG.Spec.Rsa (splitTwos powMod)

/-- Steps 3.b–3.f of Appendix C.1 for the candidate `g`: `some y` if they go
to step 5 with `y`, `none` if they go to step 3.g. -/
def factorStep (n t r g : Nat) : Option Nat :=
  let y := powMod g r n
  if y = 1 ∨ y = n - 1 then none else squarings (t - 1) y
where
  squarings : Nat → Nat → Option Nat
    | 0, y => if y * y % n = 1 then some y else none
    | j + 1, y =>
      let x := y * y % n
      if x = 1 then some y else if x = n - 1 then none else squarings j x

/-- The factors `(p, q)` of `n`, `p > q`, from the candidates `g = 2` to
`101`, or `none`. -/
def factors (n e d : Nat) : Option (Nat × Nat) :=
  if d * e < 2 ∨ (d * e - 1) % 2 = 1 then none else
    let (t, r) := splitTwos (d * e - 1)
    (List.range 100).firstM fun i =>
      (factorStep n t r (i + 2)).map fun y =>
        let p := Nat.gcd (y - 1) n
        (max p (n / p), min p (n / p))

end VG.Test.Rsa
