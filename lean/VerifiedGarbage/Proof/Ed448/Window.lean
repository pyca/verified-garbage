module

public import VerifiedGarbage.Impl.Ed448.Window
public import VerifiedGarbage.Proof.X448.BaseTable

/-! The fixed table and scalar arithmetic for four-bit Ed448 verification windows. -/

@[expose] public section

namespace VG.Proof.Ed448.Window

open VG.Spec.Ed448 VG.Proof.Ed448 VG.Proof.EdwardsLaw

private def checkEntry (i : Nat) : Bool :=
  let p := pointMul i basePoint
  let q := Impl.Ed448.Window.entry i
  q.1 * p.Z == p.X && q.2 * p.Z == p.Y

private theorem entries_check : ∀ i < 16, checkEntry i = true := by decide +kernel

theorem entry_rep (i : Nat) (hi : i < 16) :
    Rep (VG.Proof.X448.basePt (Impl.Ed448.Window.entry i)) (i • baseAff) := by
  have h := entries_check i hi
  simp only [checkEntry, Bool.and_eq_true, beq_iff_eq] at h
  exact VG.Proof.X448.basePt_rep (pointMul_rep _ basePoint_rep) h.1 h.2

def digit (k t : Nat) : Nat :=
  k / 2 ^ t % 2 + k / 2 ^ (t + 1) % 2 * 2 +
  k / 2 ^ (t + 2) % 2 * 4 + k / 2 ^ (t + 3) % 2 * 8

theorem digit_eq (k t : Nat) : digit k t = k / 2 ^ t % 16 := by
  simp only [digit, Nat.pow_add, ← Nat.div_div_eq_div_mul]
  omega

theorem digit_lt (k t : Nat) : digit k t < 16 := by rw [digit_eq]; omega

theorem high_step (k n : Nat) :
    k / 2 ^ (4 * n) = 16 * (k / 2 ^ (4 * (n + 1))) + digit k (4 * n) := by
  rw [digit_eq, show 4 * (n + 1) = 4 * n + 4 by omega, Nat.pow_add, ← Nat.div_div_eq_div_mul]
  omega

/-- The runtime table, defined even for malformed points. Group representation is conditional
on valid decoding, while the machine-code proof runs unconditionally. -/
def multiples (p : Point) : Nat → Point
  | 0 => identity
  | n + 1 => pointAdd (multiples p n) p

theorem multiples_rep {p : Point} {a : EPoint dZ} (h : Rep p a) :
    ∀ n, Rep (multiples p n) (n • a)
  | 0 => by rw [multiples, zero_smul]; exact identity_rep
  | n + 1 => by rw [multiples, succ_nsmul]; exact pointAdd_rep (multiples_rep h n) h

end VG.Proof.Ed448.Window
