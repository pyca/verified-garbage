import VerifiedGarbage.Proof.Ed448.Formulas

/-!
# Ed448 verification's equation: its field programs, evaluated

Target-independent and light: the doubling and the addition at the slots
verification uses them with (`doubleAt`, `addAt`, RFC 8032 §5.2.4's formulas,
as for base-point multiplication), and the steps of decoding (`decodeUV`, the
products of `x`, and `-x`), evaluated on the slots (`evalOps`).
-/

namespace VG.Proof.Ed448

open VG.Impl.Ed448 (FOp doubleAt addAt decodeUV)

theorem doubleAt_valid0 : ∀ op ∈ doubleAt 0 1 2, fopValid op := by decide
theorem doubleAt_valid8 : ∀ op ∈ doubleAt 8 9 10, fopValid op := by decide
theorem addAt_valid8 : ∀ op ∈ addAt 8 9, fopValid op := by decide
theorem addAt_valid6 : ∀ op ∈ addAt 6 7, fopValid op := by decide

theorem doubleAt_eval0 (e : Fin 22 → Spec.X448.Fe) :
    pt (evalOps (doubleAt 0 1 2) e) 0 1 2 = double (pt e 0 1 2) := rfl

theorem doubleAt_eval8 (e : Fin 22 → Spec.X448.Fe) :
    pt (evalOps (doubleAt 8 9 10) e) 8 9 10 = double (pt e 8 9 10) := rfl

theorem addAt_eval8 (e : Fin 22 → Spec.X448.Fe) :
    pt (evalOps (addAt 8 9) e) 3 4 5 = addWith (e 11) (pt e 0 1 2) (pt e 8 9 10) := rfl

theorem addAt_eval6 (e : Fin 22 → Spec.X448.Fe) :
    pt (evalOps (addAt 6 7) e) 3 4 5 = addWith (e 11) (pt e 0 1 2) (pt e 6 7 10) := rfl

theorem doubleAt_keep0 (e : Fin 22 → Spec.X448.Fe) (i : Fin 22) (hi : 3 ≤ i.val ∧ i.val < 12 ∨ i.val = 20 ∨ i.val = 21) :
    evalOps (doubleAt 0 1 2) e i = e i :=
  evalOps_keep _ _ _ fun op hop => by
    have : ∀ op ∈ doubleAt 0 1 2, fopDest op < 3 ∨ (12 ≤ fopDest op ∧ fopDest op < 20) := by decide
    have := this op hop
    omega

theorem doubleAt_keep8 (e : Fin 22 → Spec.X448.Fe) (i : Fin 22)
    (hi : i.val < 8 ∨ i.val = 11 ∨ i.val = 20 ∨ i.val = 21) :
    evalOps (doubleAt 8 9 10) e i = e i :=
  evalOps_keep _ _ _ fun op hop => by
    have : ∀ op ∈ doubleAt 8 9 10, (8 ≤ fopDest op ∧ fopDest op < 11) ∨
        (12 ≤ fopDest op ∧ fopDest op < 20) := by decide
    have := this op hop
    omega

theorem addAt_keep (x y : Nat) (e : Fin 22 → Spec.X448.Fe) (i : Fin 22)
    (hi : i.val < 3 ∨ (6 ≤ i.val ∧ i.val < 12) ∨ i.val = 21) :
    evalOps (addAt x y) e i = e i :=
  evalOps_keep _ _ _ fun op hop => by
    have : ∀ x y, ∀ op ∈ addAt x y, (3 ≤ fopDest op ∧ fopDest op < 6) ∨
        (12 ≤ fopDest op ∧ fopDest op < 21) := by
      intro x y op hop
      simp only [addAt, List.mem_cons, List.not_mem_nil, or_false] at hop
      rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl <;> simp [fopDest]
    have := this x y op hop
    omega

theorem idx_val (i : Fin 22) : idx i.val = i := Fin.ext (Nat.mod_eq_of_lt i.isLt)

theorem subNeg_eval (xo : Fin 22) (h : xo ≠ 12) (e : (Fin 22 → Spec.X448.Fe)) :
    evalOps [.sub 12 xo.val xo.val, .sub 12 12 xo.val] e 12 = (e xo - e xo) - e xo ∧
      ∀ i : Fin 22, i ≠ 12 → evalOps [.sub 12 xo.val xo.val, .sub 12 12 xo.val] e i = e i := by
  have h12 : idx 12 = 12 := rfl
  simp only [evalOps, List.foldl, evalOp, idx_val, h12]
  refine ⟨?_, fun i hi => ?_⟩
  · rw [Function.update_self, Function.update_self, Function.update_of_ne h]
  · rw [Function.update_of_ne hi, Function.update_of_ne hi]

theorem decodeUV_dest : ∀ xo yo : Nat, (xo = 6 ∧ yo = 7) ∨ (xo = 8 ∧ yo = 9) →
    ∀ op ∈ decodeUV yo xo, fopDest op % 22 = 3 ∨ fopDest op % 22 = 4 ∨ fopDest op % 22 = 5 ∨
      fopDest op % 22 = 12 ∨ fopDest op % 22 = 13 ∨ fopDest op % 22 = xo := by
  rintro xo yo (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> decide

theorem decodeUV_eval (xo yo : Fin 22) (h : (xo = 6 ∧ yo = 7) ∨ (xo = 8 ∧ yo = 9))
    (e : (Fin 22 → Spec.X448.Fe)) :
    let y := e yo
    let u := y * y - e 10
    let v := e 11 * (y * y) - e 10
    let t := u * u * u * v
    let e' := evalOps (decodeUV yo.val xo.val) e
    e' 13 = u ∧ e' 3 = v ∧ e' xo = t ∧ e' 12 = t * ((u * v) * (u * v)) ∧
      ∀ i : Fin 22, i ≠ 3 → i ≠ 4 → i ≠ 5 → i ≠ 12 → i ≠ 13 → i ≠ xo → e' i = e i := by
  have hk : ∀ i : Fin 22, i ≠ 3 → i ≠ 4 → i ≠ 5 → i ≠ 12 → i ≠ 13 → i ≠ xo →
      evalOps (decodeUV yo.val xo.val) e i = e i := fun i h3 h4 h5 h12 h13 hx =>
    evalOps_keep _ _ _ fun op hop => by
      have hd := decodeUV_dest xo.val yo.val (by rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide) op hop
      have : i.val ≠ 3 := fun h => h3 (Fin.ext h)
      have : i.val ≠ 4 := fun h => h4 (Fin.ext h)
      have : i.val ≠ 5 := fun h => h5 (Fin.ext h)
      have : i.val ≠ 12 := fun h => h12 (Fin.ext h)
      have : i.val ≠ 13 := fun h => h13 (Fin.ext h)
      have := Fin.val_ne_of_ne hx
      omega
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl, hk⟩
  · exact ⟨rfl, rfl, rfl, rfl, hk⟩

theorem decodeXOps_eval (xo : Fin 22) (h : xo = 6 ∨ xo = 8) (e : (Fin 22 → Spec.X448.Fe)) :
    let x := e xo * e 21
    let e' := evalOps [.mul xo.val xo.val 21, .sqr 12 xo.val, .mul 12 3 12] e
    e' xo = x ∧ e' 12 = e 3 * (x * x) ∧ e' 13 = e 13 ∧ ∀ i : Fin 22, i ≠ xo → i ≠ 12 → e' i = e i := by
  have hk : ∀ i : Fin 22, i ≠ xo → i ≠ 12 →
      evalOps [.mul xo.val xo.val 21, .sqr 12 xo.val, .mul 12 3 12] e i = e i := fun i hx h12 =>
    evalOps_keep _ _ _ fun op hop => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
      have := Fin.val_ne_of_ne hx
      have : i.val ≠ 12 := fun h => h12 (Fin.ext h)
      have := xo.isLt
      rcases hop with rfl | rfl | rfl <;> simp only [fopDest] <;> omega
  rcases h with rfl | rfl
  · exact ⟨rfl, rfl, rfl, hk⟩
  · exact ⟨rfl, rfl, rfl, hk⟩

theorem evalOps_append (a b : List FOp) (e : Fin 22 → Spec.X448.Fe) : evalOps (a ++ b) e = evalOps b (evalOps a e) :=
  List.foldl_append ..

end VG.Proof.Ed448
