module

public import VerifiedGarbage.Proof.MlDsa.FusedInverseContract
import VerifiedGarbage.Proof.MlDsa.Arith.Zq
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Spec.MlDsa

/-! # ML-DSA: a coefficient of a row's sum of products

Coefficient `i` of `dotNTT f g c` is the sum `dsum` of the products of the
natural numbers that the coefficients `i` of `f j` and `g j` reduce from. -/

@[expose] public section

namespace VG.Proof.MlDsa.Arith
open VG.Spec.MlDsa

/-- `∑_{j < c} A j · B j`. -/
def dsum (A B : Nat → Nat) : Nat → Nat
  | 0 => 0
  | c + 1 => dsum A B c + A c * B c

theorem dsum_le {A B : Nat → Nat} {b : Nat} : ∀ {c}, (∀ j < c, A j * B j ≤ b) → dsum A B c ≤ c * b
  | 0, _ => by simp [dsum]
  | c + 1, h => by
    rw [Nat.succ_mul]; exact Nat.add_le_add (dsum_le fun j hj => h j (by omega)) (h c (by omega))

theorem dotNTT_succ (f g : Nat → Poly) (c : Nat) :
    dotNTT f g (c + 1) = add (dotNTT f g c) (multiplyNTT (f c) (g c)) := by
  simp only [dotNTT, List.range_succ, List.map_append, List.map_cons, List.map_nil, List.foldl_append,
    List.foldl_cons, List.foldl_nil]

theorem dotNTT_get {f g : Nat → Poly} {A B : Nat → Nat} {i : Nat} (hi : i < n) :
    ∀ {c : Nat}, (∀ j < c, (f j)[i]! = Fin.ofNat q (A j)) → (∀ j < c, (g j)[i]! = Fin.ofNat q (B j)) →
      (dotNTT f g c)[i]! = Fin.ofNat q (dsum A B c)
  | 0, _, _ => by
    show zero[i]! = _
    rw [getElem!_eq zero hi]
    simp only [zero, Vector.getElem_replicate]
    rfl
  | c + 1, hf, hg => by
    rw [dotNTT_succ, add_get _ _ hi, mul_get _ _ hi, dotNTT_get hi (fun j hj => hf j (by omega))
      (fun j hj => hg j (by omega)), hf c (by omega), hg c (by omega)]
    apply Fin.ext
    simp only [dsum, Fin.val_add, Fin.val_mul, Fin.val_ofNat, Nat.add_mod, Nat.mul_mod, Nat.mod_mod]

theorem dotNTT_congr {f g f' g' : Nat → Poly} {c : Nat} (hf : ∀ j < c, f j = f' j) (hg : ∀ j < c, g j = g' j) :
    dotNTT f g c = dotNTT f' g' c := by
  unfold dotNTT
  congr 1
  exact List.map_congr_left fun j hj => by
    rw [hf j (List.mem_range.mp hj), hg j (List.mem_range.mp hj)]

end VG.Proof.MlDsa.Arith
