module

public import VerifiedGarbage.Proof.X448.PPC64LE.Field
public import VerifiedGarbage.Proof.X25519.PPC64LE.Product
public import VerifiedGarbage.Proof.X25519.PPC64LE.Mul
import VerifiedGarbage.Proof.Framework.Omega

/-!
# X448 on PPC64LE: the fourteen doublewords of a product

`product 7 ACC x y`, X25519's product scanning for elements of seven
doublewords (`productN_ok`), stores the fourteen doublewords of `[x] · [y]`
at `ACC` (`product7_ok`), which are the product's 28 limbs (`accW_val32`), as
the reduction reads them; the columns sum to the product (`mulCols_sum7`).
-/

-- separate module: its proofs (the sum of the 49 terms) cost more than its imports, and its
-- importer's changes need not re-check them

@[expose] public section

namespace VG.Proof.X448.PPC64LE

open VG VG.PPC64LE VG.Impl.X448.PPC64LE VG.Proof.X25519.PPC64LE
open VG.Spec.X448 (P)

/-- Seven doublewords, lowest first. -/
def val7 (f : Nat → Nat) : Nat :=
  f 0 + 2 ^ 64 * (f 1 + 2 ^ 64 * (f 2 + 2 ^ 64 * (f 3 + 2 ^ 64 * (f 4 + 2 ^ 64 * (f 5 +
    2 ^ 64 * f 6)))))

theorem val7_lt {f : Nat → Nat} (h : ∀ i < 7, f i < 2 ^ 64) : val7 f < (2 ^ 64) ^ 7 := by
  have := h 0 (by decide); have := h 1 (by decide); have := h 2 (by decide)
  have := h 3 (by decide); have := h 4 (by decide); have := h 5 (by decide)
  have := h 6 (by decide)
  unfold val7; omega_arith

/-- The columns sum to the product. -/
theorem mulCols_sum7 (X Y : Nat → Nat) : colsV (mulCs 7 X Y) 14 = val7 X * val7 Y := by
  simp only [colsV, val7]
  generalize 2 ^ 64 = B
  simp only [mulCs, Impl.X25519.PPC64LE.colPairs, tsum, List.range_succ, List.range_zero,
    List.nil_append, List.cons_append, List.reverse_cons, List.reverse_nil, List.filter_cons,
    List.filter_nil, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, mulF, Nat.reduceSub,
    Nat.reduceLeDiff, Nat.reduceLT, and_self, and_true, and_false, decide_true, decide_false,
    Bool.false_eq_true, ↓reduceIte]
  grind

/-- `N` doublewords from `acc` are their `2N` words. -/
theorem accW_val32 (acc : Nat) (m : Mem) (b : Addr) :
    ∀ N, accW acc m b N = val32 (fun k => wd m b (acc + 4 * k)) (2 * N)
  | 0 => rfl
  | N + 1 => by
    rw [accW, accW_val32 acc m b N, show 2 * (N + 1) = 2 * N + 1 + 1 by omega, val32_succ, val32_succ,
      dw_split, show acc + 4 * (2 * N) = acc + 8 * N by omega,
      show acc + 4 * (2 * N + 1) = acc + 8 * N + 4 by omega,
      show 32 * (2 * N + 1) = 64 * N + 32 by omega, show 32 * (2 * N) = 64 * N by omega,
      Nat.pow_add, ← Nat.pow_mul, Nat.mul_comm 64 N]
    rw [Nat.mul_add, Nat.add_assoc, ← Nat.mul_assoc, Nat.add_assoc]

/-- An element's seven doublewords are its fourteen limbs. -/
theorem V_eq7 (m : Mem) (b : Addr) (o : Nat) : V m b o = val7 (ew m b o) := by
  have h := accW_val32 o m b 7
  simp only [accW, val7, ew, Nat.pow_zero, Nat.pow_one, Nat.zero_add, Nat.mul_zero, Nat.add_zero,
    Nat.reduceMul, Nat.reducePow, Nat.one_mul] at h ⊢
  rw [V, show (fun k => wd m b (o + 4 * k)) = limb m b o from rfl] at *
  rw [← h]; omega_arith

section
variable {b : Addr}

/-- `product 7 ACC x y`: the 28 limbs of `[x] · [y]` at `ACC`. -/
theorem product7_ok {x y : Nat} (hx : x + 56 ≤ ACC) (hy : y + 56 ≤ ACC) (hx4 : x % 4 = 0)
    (hy4 : y % 4 = 0) {s0 : State} (hc : Ctx b s0) :
    WP isa (.block (Impl.X25519.PPC64LE.product 7 ACC x y)) s0 fun s' => Ctx b s' ∧ Rest clob s0 s' ∧
      Frame [⟨b + BitVec.ofNat 64 ACC, 112⟩] s0.mem s'.mem ∧
      val32 (accw ACC s'.mem b) 28 = V s0.mem b x * V s0.mem b y := by
  have hA : ACC = 952 := rfl
  have hlt : val7 (ew s0.mem b x) * val7 (ew s0.mem b y) < (2 ^ 64) ^ (2 * 7) :=
    Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_lt (val7_lt fun i _ => dw_lt _ _ _)
      (val7_lt fun i _ => dw_lt _ _ _)) (by rw [← Nat.pow_add])
  refine WP.mono (productN_ok (n := 7) (acc := ACC) (by decide) (by decide) (by omega) (by omega)
    (by omega) (by omega) hx4 hy4 hc (by rw [mulCols_sum7]; exact hlt))
    fun s4 ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, ?_⟩
  rw [mulCols_sum7, ← V_eq7, ← V_eq7, accW_val32] at h4
  exact h4

end

end VG.Proof.X448.PPC64LE
