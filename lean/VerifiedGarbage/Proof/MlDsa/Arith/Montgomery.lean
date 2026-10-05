import VerifiedGarbage.Proof.MlDsa.Arith.Ntt
import VerifiedGarbage.Spec.MlDsa.Montgomery

/-! # Representation identities for Montgomery-scaled ML-DSA callers -/

namespace VG.Proof.MlDsa.Arith.Montgomery

open VG.Spec.MlDsa

theorem add_mul (a b c : Zq) : (a + b) * c = a * c + b * c := by
  apply Fin.ext
  simp only [Fin.val_mul, Fin.val_add]
  rw [Nat.mod_mul_mod, Nat.add_mul, Nat.add_mod]

theorem neg_mul (a c : Zq) : (-a) * c = -(a * c) := by
  apply Fin.ext
  rw [val_mul, val_neg, val_neg, val_mul, Nat.mod_mul_mod, Nat.sub_mul]
  have h := Nat.mul_le_mul_right c.val (Nat.le_of_lt a.isLt)
  have hz : q * c.val % q = 0 := Nat.mul_mod_right _ _
  simp only [q] at h hz ⊢
  omega

theorem sub_mul (a b c : Zq) : (a - b) * c = a * c - b * c := by
  rw [Fin.sub_eq_add_neg, add_mul, neg_mul, ← Fin.sub_eq_add_neg]

def scale (c : Zq) (f : Poly) : Poly := f.map (· * c)

theorem scale_get (c : Zq) (f : Poly) (i : Nat) : (scale c f)[i]! = f[i]! * c := by
  by_cases hi : i < n
  · exact map_mul_get f c hi
  · rw [_root_.getElem!_neg (scale c f) i hi, _root_.getElem!_neg f i hi]
    change (0 : Zq) = 0 * c
    rw [Fin.zero_mul]

theorem scale_set (c : Zq) (f : Poly) (i : Nat) (x : Zq) :
    scale c (f.set! i x) = (scale c f).set! i (x * c) := by
  simp only [scale, Vector.set!_eq_setIfInBounds, Vector.map_setIfInBounds]

theorem bflyInv_scale (c : Zq) (f : Poly) (j len : Nat) (z : Zq) :
    bflyInv (scale c f) j len z = scale c (bflyInv f j len z) := by
  simp only [bflyInv, scale_get, ← add_mul, ← sub_mul, ← Fin.mul_assoc, ← scale_set]

theorem fold_scale {α : Type} (op : Poly → α → Poly)
    (h : ∀ c f a, op (scale c f) a = scale c (op f a)) (xs : List α) (c : Zq) (f : Poly) :
    xs.foldl op (scale c f) = scale c (xs.foldl op f) := by
  induction xs generalizing f with
  | nil => rfl
  | cons a xs ih => rw [List.foldl_cons, List.foldl_cons, h, ih]

theorem invLayer_scale (c : Zq) (f : Poly) (len : Nat) :
    nttInvLayer (scale c f) len = scale c (nttInvLayer f len) := by
  unfold nttInvLayer layerN
  apply fold_scale
  intro c f k
  unfold blockN
  exact fold_scale _ (fun c f j => bflyInv_scale c f j len _) _ c f

theorem scale_scale (a b : Zq) (f : Poly) : scale b (scale a f) = scale (a * b) f := by
  apply ext_getElem!
  intro i hi
  simp only [scale_get, Fin.mul_assoc]

theorem scale_one (f : Poly) : scale 1 f = f := by
  apply ext_getElem!
  intro i hi
  rw [scale_get, Fin.mul_one]

theorem inv_scale (c : Zq) (f : Poly) : nttInv (scale c f) = scale c (nttInv f) := by
  rw [nttInv_eq_layers, nttInv_eq_layers, fold_scale _ invLayer_scale]
  change scale 8347681 (scale c _) = scale c (scale 8347681 _)
  rw [scale_scale, scale_scale, Fin.mul_comm c]

theorem inv_cancel (f : Poly) : montgomeryNttInv (scale montgomeryRInv f) = nttInv f := by
  change scale montgomeryR (nttInv (scale montgomeryRInv f)) = _
  rw [inv_scale, scale_scale]
  have h : montgomeryRInv * montgomeryR = 1 := by decide +kernel
  rw [h, scale_one]

theorem scale_add (c : Zq) (f g : Poly) : scale c (add f g) = add (scale c f) (scale c g) := by
  apply ext_getElem!
  intro i hi
  rw [scale_get, add_get _ _ hi, add_get _ _ hi, scale_get, scale_get, add_mul]

theorem scale_sub (c : Zq) (f g : Poly) : scale c (sub f g) = sub (scale c f) (scale c g) := by
  apply ext_getElem!
  intro i hi
  rw [scale_get, sub_get _ _ hi, sub_get _ _ hi, scale_get, scale_get, sub_mul]

end VG.Proof.MlDsa.Arith.Montgomery
