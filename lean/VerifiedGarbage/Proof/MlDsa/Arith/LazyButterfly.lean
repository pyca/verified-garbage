import VerifiedGarbage.Proof.MlDsa.Arith.Lazy
import VerifiedGarbage.Proof.MlDsa.Arith.Mont

/-! Range and congruence of a lazy butterfly. The twiddle is reduced, but
its input coefficient may occupy any unsigned doubleword. -/
namespace VG.Proof.MlDsa.Arith.Lazy
open VG.Spec.MlDsa (q Zq)
open VG.Proof.MlDsa.Arith

def product (y : Word) (z : Zq) : Nat := mont (y.val * (z.val * 2 ^ 32 % q))

theorem product_lt (y : Word) (z : Zq) : product y z < 2 * q := by
  apply mont_lt
  have hy : y.val < 2 ^ 32 := y.isLt
  have hz : z.val * 2 ^ 32 % q < q := Nat.mod_lt _ (by decide)
  exact Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le hy (Nat.le_of_lt hz) (by decide)) (by omega)

def op (x y : Word) (z : Zq) : Word × Word :=
  let t : Word := Fin.ofNat 4294967296 (product y z)
  (x + t, x + 16760834 - t)

def residue (x : Word) : Zq := Fin.ofNat q x.val

theorem op_values (x y : Word) (z : Zq) (hx : x.val < 15 * q) :
    (op x y z).1.val = x.val + product y z ∧
    (op x y z).2.val = x.val + 2 * q - product y z := by
  have ht := product_lt y z
  have ht32 : product y z < 4294967296 := by rw [q_eq] at ht; omega
  have hx32 : x.val + 16760834 < 4294967296 := by rw [q_eq] at hx; omega
  simp only [op, Fin.val_add, Fin.val_sub, Fin.val_ofNat, Nat.mod_eq_of_lt ht32,
    show (16760834 : Word).val = 16760834 from rfl, Nat.mod_eq_of_lt hx32]
  rw [q_eq] at hx ht ⊢
  constructor <;> omega

theorem op_bound (x y : Word) (z : Zq) {b : Nat} (hb : b ≤ 15) (hx : x.val < b * q) :
    (op x y z).1.val < (b + 2) * q ∧ (op x y z).2.val < (b + 2) * q := by
  have hv := op_values x y z (Nat.lt_of_lt_of_le hx (Nat.mul_le_mul_right q hb))
  have ht := product_lt y z
  rw [hv.1, hv.2, Nat.add_mul]
  omega

theorem op_residue (x y : Word) (z : Zq) (hx : x.val < 15 * q) :
    residue (op x y z).1 = residue x + z * residue y ∧
    residue (op x y z).2 = residue x - z * residue y := by
  have hv := op_values x y z hx
  have ht := product_lt y z
  have hm : product y z % q = y.val * z.val % q := mont_mulR _ _
  have hm' : (z * residue y).val = product y z % q := by
    rw [Fin.val_mul, residue, Fin.val_ofNat, Nat.mul_mod_mod, Nat.mul_comm, hm]
  constructor
  · apply Fin.ext
    rw [Fin.val_add, hm']
    change (op x y z).1.val % q = (x.val % q + product y z % q) % q
    rw [hv.1, Nat.add_mod]
  · apply Fin.ext
    rw [Fin.val_sub, hm']
    change (op x y z).2.val % q = (q - product y z % q + x.val % q) % q
    rw [hv.2]
    have ht' : product y z < 2 * 8380417 := ht
    change (x.val + 2 * 8380417 - product y z) % 8380417 =
      (8380417 - product y z % 8380417 + x.val % 8380417) % 8380417
    omega

/-- Folding the high nine bits back uses q = 2²³ - 2¹³ + 1. -/
theorem final_reduce {x : Nat} (hx : x < 17 * q) :
    x % 8388608 + x / 8388608 * 8191 < 2 * q ∧
    (x % 8388608 + x / 8388608 * 8191) % q = x % q := by
  rw [q_eq] at hx ⊢
  omega

end VG.Proof.MlDsa.Arith.Lazy
