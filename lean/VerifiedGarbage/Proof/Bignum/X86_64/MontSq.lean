module

public import VerifiedGarbage.Proof.Bignum.X86_64.Mont

/-!
# Squarings of an exponentiation's accumulator

An exponentiation by windows squares its accumulator `Y` (`aY`) between
its multiplications by the table, which take the table's entries, below
`m`, as their second operand. A squaring needs no operand below `m` if its
result need not be either: `MontS` is a squaring `[aY] := [aY]² R⁻¹` whose
results stay below a bound `bd m R` (at least `m`): `m` for a Montgomery
multiplication `Mont` (`Mont.toS`), `R` for a lazy one, whose result is any
number of `w` words congruent to it. The multiplication by the table then
brings `Y` below `m` again.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.MlKem.X86_64

/-- A squaring of `aY` in the working space of `vg_rsa_public`, whose
results stay below `bd m R`, and constant time whatever the modulus. -/
structure MontS where
  mm : Prog isa
  bd : Nat → Nat → Nat
  le : ∀ {m R : Nat}, m ≤ R → m ≤ bd m R
  ok : ∀ {t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}, Good t B Z w minv → slot w 8 ≤ Z → 2 ≤ w →
    w < 2 ^ 31 → ((word t.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0 →
    wv t.mem B (slot w aY) w < bd (wv t.mem B (slot w aN) w) (2 ^ (64 * w)) →
    WP isa mm t fun t' =>
      Good t' B Z w minv ∧
      wv t'.mem B (slot w aY) w < bd (wv t.mem B (slot w aN) w) (2 ^ (64 * w)) ∧
      wv t'.mem B (slot w aY) w * 2 ^ (64 * w) % wv t.mem B (slot w aN) w =
        wv t.mem B (slot w aY) w * wv t.mem B (slot w aY) w % wv t.mem B (slot w aN) w ∧
      Arrays B w [aAcc, aTmp, aY] t.mem t'.mem ∧ Keep mmRegs t t'
  ct : RelCT isa (Two GoodW) mm fun _ _ => True

/-- A Montgomery multiplication's squarings, whose results are below `m`. -/
def Mont.toS (M : Mont) : MontS where
  mm := M.mm aY aY aY
  bd m _ := m
  le h := Nat.le_refl _
  ok hg hZ hw hw' hinv hY := M.mm_ok hg hZ hw hw' (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) hinv hY
  ct := M.ct (.inr (.inl ⟨rfl, rfl, rfl⟩))

end VG.Proof.Bignum.X86_64
