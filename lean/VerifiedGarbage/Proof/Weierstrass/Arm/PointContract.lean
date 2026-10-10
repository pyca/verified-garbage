import VerifiedGarbage.Proof.Weierstrass.Arm.PointFn
import VerifiedGarbage.Proof.Weierstrass.Arm.MontContract
import VerifiedGarbage.Proof.Weierstrass.Law

/-!
# Complete point addition and doubling as functions, on 32-bit ARM: the contracts

The facts of `Spec.Weierstrass.Point.Curve.addContract` and `doubleContract` on 32-bit ARM, by
name (`sumArm`: `ws` in `r0`), and `fn (modP C) dbl` meets them (`sum_arm`),
given that `C.p` is odd and Fermat's little theorem holds in `Fin C.p`
(`Fermat`), so that `R⁻¹ = R^(p-2)` and the contract's `dec` is the
proofs' `toM`: the coordinates are what `wordsVal` reads, the
specification's `rcbAdd` is the proofs', and what the function changes is
what `Keeps` allows.
-/

namespace VG.Proof.Weierstrass.Arm.Point

open VG VG.Arm VG.Impl.Weierstrass.Arm.Mont VG.Proof.Mont
open VG.Impl.Weierstrass VG.Impl.Weierstrass.Arm.Point
open VG.Proof.Weierstrass VG.Proof.Weierstrass.Arm VG.Proof.Weierstrass.Arm.Mont

/-- Fermat's little theorem in `Fin p`. -/
def Fermat (p : Nat) [NeZero p] : Prop := ∀ z : Fin p, z ≠ 0 → z * Spec.Weierstrass.pow z (p - 2) = 1

/-- The second operand: `P` if `dbl`, else `Q`. -/
def qOf (k : Nat) (dbl : Bool) : Nat := if dbl then Spec.Weierstrass.Point.pAt k else Spec.Weierstrass.Point.qAt k

/-- `vg_<curve>_point_add(ws = r0)` (`dbl` false) or `vg_<curve>_point_double`. -/
def sumArm (C : Spec.Weierstrass.Point.Curve) (dbl : Bool) : Contract Arm.isa where
  pre s := s.rd = [] ∧ s.wr = [⟨State.addr (s.gpr .r0), 8192⟩] ∧ (s.gpr .r0).toNat + 8192 ≤ 2 ^ 32 ∧
    C.Below (C.pointAt s.mem (State.addr (s.gpr .r0)) (Spec.Weierstrass.Point.pAt C.k)) ∧
    C.Below (C.pointAt s.mem (State.addr (s.gpr .r0)) (qOf C.k dbl)) ∧ C.ConstsBelow (State.addr (s.gpr .r0)) s.mem
  post s s' :=
    C.Below (C.pointAt s'.mem (State.addr (s.gpr .r0)) (Spec.Weierstrass.Point.oAt C.k)) ∧
    C.decPt (C.pointAt s'.mem (State.addr (s.gpr .r0)) (Spec.Weierstrass.Point.oAt C.k)) =
      C.sum (State.addr (s.gpr .r0)) s.mem (Spec.Weierstrass.Point.pAt C.k) (qOf C.k dbl) ∧
    Spec.Weierstrass.Point.Keeps C.k (State.addr (s.gpr .r0)) s.mem s'.mem
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0

theorem rcbAdd_eq {p : Nat} [NeZero p] (a b3 X1 Y1 Z1 X2 Y2 Z2 : Fin p) :
    Spec.Weierstrass.Point.rcbAdd a b3 X1 Y1 Z1 X2 Y2 Z2 = VG.Proof.Weierstrass.rcbAdd a b3 X1 Y1 Z1 X2 Y2 Z2 :=
  rfl

/-- `R⁻¹` is `R^(p-2)`: the contract's `dec` is the proofs' `toM`. -/
theorem dec_eq (C : Spec.Weierstrass.Point.Curve) (h1 : (1 : Fin C.p) ≠ 0) (hF : Fermat C.p) (hu : UnitMod C.p C.R) (x : Nat) :
    C.dec x = toM C.p C.R x := by
  have hr := mul_rinv hu
  have hR : Fin.ofNat C.p C.R ≠ 0 := fun h => h1 (by rw [← hr, h]; grind)
  have hf := hF _ hR
  unfold Spec.Weierstrass.Point.Curve.dec toM
  have : Spec.Weierstrass.pow (Fin.ofNat C.p C.R) (C.p - 2) = rinv C.p C.R := by grind
  rw [this]

/-- The coordinate at an offset below `2³²` is the number `wordsVal` reads. -/
theorem coordAt_eq (C : Spec.Weierstrass.Point.Curve) (m : Mem) (ws : Addr) {o : Nat} (ho : o < 2 ^ 32) :
    C.coordAt m ws o = wordsVal m ws o C.k := by
  unfold Spec.Weierstrass.Point.Curve.coordAt
  rw [numAt_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ho]

theorem keeps_of_outs {k : Nat} (hk3 : 3 ≤ k) (hk6 : k ≤ 6) {ws : Addr} {m m' : Mem}
    (h : Outs ws [(Spec.Weierstrass.Point.oAt k, 3 * Spec.Weierstrass.Point.elemBytes k), (Spec.Weierstrass.Point.ownAt k, 4096 - Spec.Weierstrass.Point.ownAt k)] m m') :
    Spec.Weierstrass.Point.Keeps k ws m m' := by
  have hl := lay_nums hk3 hk6
  intro i hi hown ho
  simp only [Spec.Weierstrass.Mont.wsBytes] at hi
  refine h _ fun r hr => ?_
  rw [ofs_off0 ws (by omega)]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> dsimp only <;> omega

/-- The precondition, as the proof has it. -/
theorem prePt_of {C : Spec.Weierstrass.Point.Curve} (hk3 : 3 ≤ C.k) (hk6 : C.k ≤ 6) {dbl : Bool} {s : State}
    (h : (sumArm C dbl).pre s) : PrePt C.k C.p dbl s := by
  obtain ⟨hrd, hwr, hfit, ⟨p0, p1, p2⟩, ⟨q0, q1, q2⟩, ha, hb⟩ := h
  have hl := lay_nums hk3 hk6
  have e : ∀ x, x < 4096 → C.coordAt s.mem (State.addr (s.gpr .r0)) x =
      wordsVal s.mem (State.addr (s.gpr .r0)) x C.k := fun x hx => coordAt_eq C _ _ (by omega)
  refine ⟨hrd, hwr, hfit, hk3, hk6, fun x hx => ?_⟩
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
theorem sum_arm {C : Spec.Weierstrass.Point.Curve} (hM : ModOk C.k C.p) (hk6 : C.k ≤ 6) (hodd : C.p % 2 = 1)
    (h1 : (1 : Fin C.p) ≠ 0) (hF : Fermat C.p) (dbl : Bool) (s : State) (hs : (sumArm C dbl).pre s) :
    ∃ t s', Exec isa (fn (modP C) dbl) s t s' ∧ abiPreserved s s' ∧ (sumArm C dbl).post s s' := by
  have hk3 := hM.n3
  have hp := prePt_of hk3 hk6 hs
  have hl := lay_nums hk3 hk6
  obtain ⟨t, s', he, A, O, -, hlt, hEq⟩ := fn_ok (S := modP C) hM hodd hp
  have hu : UnitMod C.p C.R := unitMod_pow_two hodd _
  have dq := dec_eq C h1 hF hu
  have e : ∀ (m : Mem) x, x < 4096 → C.coordAt m (State.addr (s.gpr .r0)) x =
      wordsVal m (State.addr (s.gpr .r0)) x C.k := fun m x hx => coordAt_eq C _ _ (by omega)
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
    simp only [Spec.Weierstrass.Point.Curve.decPt, Spec.Weierstrass.Point.Curve.pointAt, Spec.Weierstrass.Point.Curve.sum, rcbAdd_eq, dq, qOf]
    cases dbl <;> simp only [Bool.false_eq_true, ↓reduceIte] at hEq ⊢ <;>
      (repeat rw [e _ _ (by omega)]) <;>
      exact hEq

end VG.Proof.Weierstrass.Arm.Point
