import VerifiedGarbage.Impl.Ed25519.BaseTable
import VerifiedGarbage.Spec.Ed25519

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.ScalarMul`. -/
section

/-!
# Scalar multiplication, from high bits to low bits

The loop accumulates the very same extended-coordinate values as `pointMul`,
rather than relying on an unproved group-law identity. At bit n its
accumulator is `[floor(s/2^(n+1))] [2^(n+1)]P`. Adding `[2^n]P` exactly when
bit n is one gives the next invariant. Powers can be computed in small batches
so the scratch space remains bounded.
-/

namespace VG.Proof.Ed25519

open VG.Spec.Ed25519

/-- Exactly n doublings, preserving the specification's coordinates. -/
def powerPoint (p : Point) : Nat → Point
  | 0 => p
  | n + 1 => pointAdd (powerPoint p n) (powerPoint p n)

theorem powerPoint_add (p : Point) (n k : Nat) :
    powerPoint p (n + k) = powerPoint (powerPoint p n) k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Nat.add_succ, powerPoint, ih, powerPoint]

theorem pointMul_zero (p : Point) : pointMul 0 p = identity := by
  rw [pointMul, ite_eq_left rfl]

theorem pointMul_step (s : Nat) (p : Point) :
    pointMul s p =
      if s % 2 = 0 then pointMul (s / 2) (pointAdd p p)
      else pointAdd (pointMul (s / 2) (pointAdd p p)) p := by
  by_cases hs : s = 0
  · subst hs
    simp only [Nat.zero_mod, Nat.zero_div, ite_true, pointMul_zero]
  · conv => lhs; rw [pointMul, ite_eq_right hs]

def after (s : Nat) (p : Point) (n : Nat) : Point :=
  pointMul (s / 2 ^ n) (powerPoint p n)

theorem after_step (s : Nat) (p : Point) (n : Nat) :
    after s p n = if (s / 2 ^ n) % 2 = 0 then after s p (n + 1)
      else pointAdd (after s p (n + 1)) (powerPoint p n) := by
  simp only [after, powerPoint, Nat.pow_succ, ← Nat.div_div_eq_div_mul]
  exact pointMul_step _ _

theorem after_zero (s : Nat) (p : Point) : after s p 0 = pointMul s p := by
  simp only [after, Nat.pow_zero, Nat.div_one, powerPoint]

theorem after_top (s n : Nat) (p : Point) (hs : s < 2 ^ n) : after s p n = identity := by
  rw [after, Nat.div_eq_of_lt hs, pointMul_zero]

end VG.Proof.Ed25519

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.BaseTable`. -/
section

/-!
# The cached base-point powers match the specification

`checkList` walks the table once, doubling a literal point with the
specification's formula as it goes, so the kernel evaluates 256 doublings and
compares 256 entries. `d` is replaced by its value first, so that the kernel
computes its inversion once.
-/

namespace VG.Proof.Ed25519

open VG.Spec.Ed25519 VG.Impl.Ed25519

/-- `[Y - X, Y + X, 2dT, 2Z]`: a point cached for addition. -/
def cache (q : Point) : Point := ⟨q.Y - q.X, q.Y + q.X, q.T * 2 * d, q.Z * 2⟩

private def dLit : Spec.X25519.Fe :=
  37095705934669439343138083508754565189542113879843219016388785533085940283555

private theorem d_eq : d = dLit := by decide +kernel

private def addLit (p q : Point) : Point :=
  let a := (p.Y - p.X) * (q.Y - q.X)
  let b := (p.Y + p.X) * (q.Y + q.X)
  let c := p.T * 2 * dLit * q.T
  let dd := p.Z * 2 * q.Z
  let e := b - a
  let f := dd - c
  let g := dd + c
  let h := b + a
  ⟨e * f, g * h, f * g, e * h⟩

private def cacheLit (q : Point) : Point := ⟨q.Y - q.X, q.Y + q.X, q.T * 2 * dLit, q.Z * 2⟩

private theorem addLit_eq (p q : Point) : addLit p q = pointAdd p q := by
  simp only [addLit, pointAdd, d_eq]

private theorem cacheLit_eq (q : Point) : cacheLit q = cache q := by
  simp only [cacheLit, cache, d_eq]

/-- Whether the entries are the cached powers of `p`, from `p` on. -/
private def checkList (p : Point) : List Point → Bool
  | [] => true
  | c :: cs => cacheLit p == c && checkList (addLit p p) cs

private theorem checkList_ok (p : Point) (cs : List Point) (h : checkList p cs = true)
    (k : Nat) (hk : k < cs.length) : cs.getD k identity = cache (powerPoint p k) := by
  induction cs generalizing p k with
  | nil => exact absurd hk (Nat.not_lt_zero _)
  | cons c cs ih =>
    simp only [checkList, Bool.and_eq_true, beq_iff_eq] at h
    cases k with
    | zero => rw [List.getD_cons_zero, ← h.1, cacheLit_eq]; rfl
    | succ k =>
      rw [List.getD_cons_succ, ih _ h.2 k (by simp only [List.length_cons] at hk; omega),
        addLit_eq, Nat.add_comm, powerPoint_add]
      rfl

private theorem table_length : baseCachedTable.length = 256 := by decide +kernel

private theorem table_check : checkList basePoint baseCachedTable = true := by decide +kernel

theorem baseCached_ok (i : Nat) (hi : i < 256) :
    baseCached i = cache (powerPoint basePoint i) :=
  checkList_ok _ _ table_check i (table_length ▸ hi)

end VG.Proof.Ed25519

end
