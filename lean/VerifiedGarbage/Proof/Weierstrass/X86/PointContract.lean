import VerifiedGarbage.Proof.Weierstrass.X86.PointFn
import VerifiedGarbage.Proof.Weierstrass.X86.MontContract
import VerifiedGarbage.Proof.Weierstrass.PointFacts

/-!
# Complete point addition and doubling as functions, on x86 (32-bit): the contracts

The facts of `Spec.Weierstrass.Point.Curve.addContract` and `doubleContract`
on x86, for code whose calls use 20 bytes of stack, by name (`sumX86`: `ws`
the argument, the arguments, the return address and the 20 bytes below it
apart from it), and `fn (modP C) dbl` meets them (`sum_x86`), given that
`C.p` is odd and Fermat's little theorem holds in `Fin C.p` (`Fermat`,
`Proof/Weierstrass/PointFacts.lean`).
-/

namespace VG.Proof.Weierstrass.X86.Point

open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86.Mont VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Weierstrass VG.Impl.Weierstrass.X86.Point
open VG.Proof.Weierstrass VG.Proof.Weierstrass.X86.Mont
open VG.Proof.Weierstrass.Point (Fermat qOf rcbAdd_eq dec_eq)

/-- `vg_<curve>_point_add(ws)` (`dbl` false) or `vg_<curve>_point_double`. -/
def sumX86 (C : Spec.Weierstrass.Point.Curve) (dbl : Bool) : Contract X86.isa where
  pre s := s.rd = [⟨argAddr s 0, 4⟩] ∧ s.wr = [⟨wsOf s, 8192⟩] ∧ (arg s 0).toNat + 8192 ≤ 2 ^ 32 ∧
    20 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 8 ≤ 2 ^ 32 ∧
    Region.Disjoint ⟨argAddr s 0, 4⟩ ⟨wsOf s, 8192⟩ ∧
    Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨wsOf s, 8192⟩ ∧
    Region.Disjoint ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 20, 20⟩ ⟨wsOf s, 8192⟩ ∧
    C.Below (C.pointAt s.mem (wsOf s) (Spec.Weierstrass.Point.pAt C.k)) ∧
    C.Below (C.pointAt s.mem (wsOf s) (qOf C.k dbl)) ∧ C.ConstsBelow (wsOf s) s.mem
  post s s' :=
    C.Below (C.pointAt s'.mem (wsOf s) (Spec.Weierstrass.Point.oAt C.k)) ∧
    C.decPt (C.pointAt s'.mem (wsOf s) (Spec.Weierstrass.Point.oAt C.k)) =
      C.sum (wsOf s) s.mem (Spec.Weierstrass.Point.pAt C.k) (qOf C.k dbl) ∧
    Spec.Weierstrass.Point.Keeps C.k (wsOf s) s.mem s'.mem
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ arg s₁ 0 = arg s₂ 0

/-- The coordinate at an offset below `2³²` is the number `wordsVal` reads. -/
theorem coordAt_eq (C : Spec.Weierstrass.Point.Curve) (m : Mem) (ws : Addr) {o : Nat} (ho : o < 2 ^ 32) :
    C.coordAt m ws o = wordsVal m ws o C.k := by
  unfold Spec.Weierstrass.Point.Curve.coordAt
  rw [numAt_eq, ← wordsVal_eq_val32, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ho]

theorem keeps_of_outs {k : Nat} (hk3 : 3 ≤ k) (hk6 : k ≤ 6) {ws : Addr} {m m' : Mem}
    (h : Outs ws [(Spec.Weierstrass.Point.oAt k, 3 * Spec.Weierstrass.Point.elemBytes k),
      (Spec.Weierstrass.Point.ownAt k, 4096 - Spec.Weierstrass.Point.ownAt k), outW] m m') :
    Spec.Weierstrass.Point.Keeps k ws m m' := by
  have hl := lay_nums hk3 hk6
  intro i hi hown ho
  simp only [Spec.Weierstrass.Mont.wsBytes] at hi
  refine h _ fun r hr => ?_
  rw [ofs_off0 ws (by omega)]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> dsimp only <;> omega

/-- The precondition, as the proof has it. -/
theorem prePt_of {C : Spec.Weierstrass.Point.Curve} (hk3 : 3 ≤ C.k) (hk6 : C.k ≤ 6) {dbl : Bool} {s : State}
    (h : (sumX86 C dbl).pre s) : PrePt C.k C.p dbl s := by
  obtain ⟨hrd, hwr, hfit, h20, hsp, haw, hrw, hzw, ⟨p0, p1, p2⟩, ⟨q0, q1, q2⟩, ha, hb⟩ := h
  have hl := lay_nums hk3 hk6
  have hn : (wsOf s).toNat + 8192 ≤ 2 ^ 32 := by
    show ((arg s 0).setWidth 64).toNat + 8192 ≤ _
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]; exact hfit
  have e : ∀ x, x < 4096 → C.coordAt s.mem (wsOf s) x = wordsVal s.mem (wsOf s) x C.k :=
    fun x hx => coordAt_eq C _ _ (by omega)
  refine ⟨⟨rfl, by rw [hrd]; exact List.mem_singleton_self _, by rw [hwr]; exact List.mem_singleton_self _,
    hn, VG.Proof.Weierstrass.X86.stkOk_of (Nat.le_refl _) h20 hn (by decide) hzw, hsp, haw⟩, hrw, hk3, hk6,
    fun x hx => ?_⟩
  simp only [Spec.Weierstrass.Point.Curve.pointAt, qOf] at p0 p1 p2 q0 q1 q2
  simp only [rIds, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases dbl <;>
    simp only [enc, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, Nat.reduceSub, Nat.mul_zero, Nat.mul_one,
      Nat.add_zero, Bool.false_eq_true] at q0 q1 q2 ⊢ <;>
    first
    | (rw [← e _ (by omega)]; assumption)
    | (rw [← e _ (by omega), show Spec.Weierstrass.Point.elemBytes C.k * 2 = 2 * Spec.Weierstrass.Point.elemBytes C.k by omega]; assumption)
    | (rw [← e _ (by omega)]; exact ha)
    | (rw [← e _ (by omega)]; exact hb)

/-- `vg_<curve>_point_add` or `vg_<curve>_point_double` meets its contract,
by register. -/
theorem sum_x86 {C : Spec.Weierstrass.Point.Curve} (hF : FnOk (modP C)) (hk3 : 3 ≤ C.k) (hk6 : C.k ≤ 6)
    (hodd : C.p % 2 = 1) (h1 : (1 : Fin C.p) ≠ 0) (hFe : Fermat C.p) (dbl : Bool) (s : State)
    (hs : (sumX86 C dbl).pre s) :
    ∃ t s', Exec isa (fn (modP C) dbl) s t s' ∧ abiPreserved s s' ∧ (sumX86 C dbl).post s s' := by
  have hp := prePt_of hk3 hk6 hs
  have hl := lay_nums hk3 hk6
  obtain ⟨t, s', he, A, O, hlt, hEq⟩ := fn_ok (S := modP C) hF hodd hp
  have hu : UnitMod C.p C.R := unitMod_pow_two hodd _
  have dq := dec_eq C h1 hFe hu
  have e : ∀ (m : Mem) x, x < 4096 → C.coordAt m (wsOf s) x = wordsVal m (wsOf s) x C.k :=
    fun m x hx => coordAt_eq C _ _ (by omega)
  have e2 : Spec.Weierstrass.Point.elemBytes C.k * 2 = 2 * Spec.Weierstrass.Point.elemBytes C.k := by omega
  refine ⟨t, s', he, A, ?_, ?_, keeps_of_outs hk3 hk6 O⟩
  · have h0 := hlt 0 (by decide); have h1' := hlt 1 (by decide); have h2 := hlt 2 (by decide)
    simp only [enc, Nat.reduceLT, ↓reduceIte, Nat.mul_zero, Nat.mul_one, Nat.add_zero] at h0 h1' h2
    refine ⟨?_, ?_, ?_⟩ <;> simp only [Spec.Weierstrass.Point.Curve.pointAt]
    · rw [e _ _ (by omega)]; exact h0
    · rw [e _ _ (by omega)]; exact h1'
    · rw [e _ _ (by omega)]; rw [e2] at h2; exact h2
  · simp only [enc, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, Nat.reduceSub, Nat.mul_zero, Nat.mul_one,
      Nat.add_zero, E₀, e2] at hEq
    simp only [Spec.Weierstrass.Point.Curve.decPt, Spec.Weierstrass.Point.Curve.pointAt,
      Spec.Weierstrass.Point.Curve.sum, rcbAdd_eq, dq, qOf]
    cases dbl <;> simp only [Bool.false_eq_true, ↓reduceIte] at hEq ⊢ <;>
      (repeat rw [e _ _ (by omega)]) <;>
      exact hEq

end VG.Proof.Weierstrass.X86.Point
