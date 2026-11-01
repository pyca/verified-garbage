module

public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.PointFn
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.MontContract
public import VerifiedGarbage.Proof.Weierstrass.PointContract
public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.MontFn

/-!
# Complete point addition and doubling as functions, on PPC64LE: the contracts

The facts of `Impl.Weierstrass.Point.Curve.addContract` and
`doubleContract` on PPC64LE, by register (`sumPPC`: `ws` in `r3`), and
`fn (modP C) dbl` meets them (`sum_ppc`), given that `C.p` is odd and
Fermat's little theorem holds in `Fin C.p` (`Fermat`), as on 32-bit ARM
(`Proof/Weierstrass/Arm/PointContract.lean`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.PPC64LE.Point

open VG VG.PPC64LE VG.Impl.Weierstrass.PPC64LE.Mont VG.Proof.Mont
open VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE.Point
open VG.Proof.Weierstrass VG.Proof.Weierstrass.PPC64LE.Mont
open VG.Impl.Weierstrass.Point (elemBytes ownAt aAt b3At oAt pAt qAt)

/-- Fermat's little theorem in `Fin p`. -/
def Fermat (p : Nat) [NeZero p] : Prop := ∀ z : Fin p, z ≠ 0 → z * Spec.Weierstrass.pow z (p - 2) = 1

/-- The second operand: `P` if `dbl`, else `Q`. -/
def qOf (k : Nat) (dbl : Bool) : Nat := if dbl then pAt k else qAt k

/-- `vg_<curve>_point_add(ws = r3)` (`dbl` false) or `vg_<curve>_point_double`. -/
def sumPPC (C : Impl.Weierstrass.Point.Curve) (dbl : Bool) : Contract PPC64LE.isa where
  pre s := s.rd = [] ∧ s.wr = [⟨s.gpr .r3, 8192⟩] ∧ (s.gpr .r3).toNat + 8192 ≤ 2 ^ 64 ∧
    C.Below (C.pointAt s.mem (s.gpr .r3) (pAt C.k)) ∧
    C.Below (C.pointAt s.mem (s.gpr .r3) (qOf C.k dbl)) ∧ C.ConstsBelow (s.gpr .r3) s.mem
  post s s' :=
    C.Below (C.pointAt s'.mem (s.gpr .r3) (oAt C.k)) ∧
    C.decPt (C.pointAt s'.mem (s.gpr .r3) (oAt C.k)) = C.sum (s.gpr .r3) s.mem (pAt C.k) (qOf C.k dbl) ∧
    Impl.Weierstrass.Point.Keeps C.k (s.gpr .r3) s.mem s'.mem
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r3 = s₂.gpr .r3

theorem rcbAdd_eq {p : Nat} [NeZero p] (a b3 X1 Y1 Z1 X2 Y2 Z2 : Fin p) :
    Impl.Weierstrass.Point.rcbAdd a b3 X1 Y1 Z1 X2 Y2 Z2 = VG.Proof.Weierstrass.rcbAdd a b3 X1 Y1 Z1 X2 Y2 Z2 :=
  rfl

/-- `R⁻¹` is `R^(p-2)`: the contract's `dec` is the proofs' `toM`. -/
theorem dec_eq (C : Impl.Weierstrass.Point.Curve) (h1 : (1 : Fin C.p) ≠ 0) (hF : Fermat C.p) (hu : UnitMod C.p C.R)
    (x : Nat) : C.dec x = toM C.p C.R x := by
  have hr := mul_rinv hu
  have hR : Fin.ofNat C.p C.R ≠ 0 := fun h => h1 (by rw [← hr, h]; grind)
  have hf := hF _ hR
  unfold Impl.Weierstrass.Point.Curve.dec toM
  have : Spec.Weierstrass.pow (Fin.ofNat C.p C.R) (C.p - 2) = rinv C.p C.R := by grind
  rw [this]

/-- The coordinate at an offset below `2³²` is the number `wordsVal` reads. -/
theorem coordAt_eq (C : Impl.Weierstrass.Point.Curve) (m : Mem) (ws : Addr) {o : Nat} (ho : o < 2 ^ 32) :
    C.coordAt m ws o = wordsVal m ws o C.k := by
  unfold Impl.Weierstrass.Point.Curve.coordAt
  rw [numAt_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ho]

theorem keeps_of_outs {k : Nat} (hk3 : 3 ≤ k) (hk6 : k ≤ 6) {ws : Addr} {m m' : Mem}
    (h : Outs ws [(oAt k, 3 * elemBytes k), (ownAt k, 4096 - ownAt k)] m m') :
    Impl.Weierstrass.Point.Keeps k ws m m' := by
  have hl := lay_nums hk3 hk6
  intro i hi hown ho
  simp only [Impl.Weierstrass.Mont.wsBytes] at hi
  refine h _ fun r hr => ?_
  rw [ofs_off0 ws (by omega)]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> dsimp only <;> omega

/-- The precondition, as the proof has it. -/
theorem prePt_of {C : Impl.Weierstrass.Point.Curve} (hk3 : 3 ≤ C.k) (hk6 : C.k ≤ 6) {dbl : Bool} {s : State}
    (h : (sumPPC C dbl).pre s) : PrePt C.k C.p dbl s := by
  obtain ⟨-, hwr, hfit, ⟨p0, p1, p2⟩, ⟨q0, q1, q2⟩, ha, hb⟩ := h
  have hl := lay_nums hk3 hk6
  have e : ∀ x, x < 4096 → C.coordAt s.mem (s.gpr .r3) x = wordsVal s.mem (s.gpr .r3) x C.k :=
    fun x hx => coordAt_eq C _ _ (by omega)
  refine ⟨hwr, hfit, hk3, hk6, fun x hx => ?_⟩
  have hx' := enc_rIds hk3 hk6 dbl x hx
  rw [← e _ (by omega)]
  simp only [Impl.Weierstrass.Point.Curve.pointAt, qOf] at p0 p1 p2 q0 q1 q2
  simp only [rIds, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases dbl <;>
    simp only [enc, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, Nat.reduceSub, Nat.mul_zero, Nat.mul_one,
      Nat.add_zero, Bool.false_eq_true, Nat.mul_comm (elemBytes C.k) 2] at q0 q1 q2 ⊢ <;>
    with_reducible assumption

/-- `vg_<curve>_point_add` or `vg_<curve>_point_double` meets its contract,
by register. -/
theorem sum_ppc {C : Impl.Weierstrass.Point.Curve} (hM : ModOk C.k C.p) (hk3 : 3 ≤ C.k) (hk6 : C.k ≤ 6)
    (hodd : C.p % 2 = 1) (h1 : (1 : Fin C.p) ≠ 0) (hF : Fermat C.p) (dbl : Bool) (s : State)
    (hs : (sumPPC C dbl).pre s) :
    ∃ t s', Exec isa (VG.Impl.Weierstrass.PPC64LE.Point.fn (modP C) dbl) s t s' ∧ abiPreserved s s' ∧ (sumPPC C dbl).post s s' := by
  have hp := prePt_of hk3 hk6 hs
  have hl := lay_nums hk3 hk6
  obtain ⟨t, s', he, A, -, O, hlt, hEq⟩ := fn_ok (S := modP C) hM hodd hp
  have hu : UnitMod C.p C.R := unitMod_pow_two hodd _
  have dq := dec_eq C h1 hF hu
  have e : ∀ (m : Mem) x, x < 4096 → C.coordAt m (s.gpr .r3) x = wordsVal m (s.gpr .r3) x C.k :=
    fun m x hx => coordAt_eq C _ _ (by omega)
  have e2 : elemBytes C.k * 2 = 2 * elemBytes C.k := Nat.mul_comm _ _
  refine ⟨t, s', he, A, ?_, ?_, keeps_of_outs hk3 hk6 O⟩
  · have h0 := hlt 0 (by decide); have h1' := hlt 1 (by decide); have h2 := hlt 2 (by decide)
    simp only [enc, Nat.reduceLT, ↓reduceIte, Nat.mul_zero, Nat.mul_one, Nat.add_zero] at h0 h1' h2
    refine ⟨?_, ?_, ?_⟩ <;> simp only [Impl.Weierstrass.Point.Curve.pointAt]
    · rw [e _ _ (by omega)]; exact h0
    · rw [e _ _ (by omega)]; exact h1'
    · rw [e _ _ (by omega)]; rw [e2] at h2; exact h2
  · simp only [enc, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, Nat.reduceSub, Nat.mul_zero, Nat.mul_one,
      Nat.add_zero, E₀, e2] at hEq
    simp only [Impl.Weierstrass.Point.Curve.decPt, Impl.Weierstrass.Point.Curve.pointAt,
      Impl.Weierstrass.Point.Curve.sum, rcbAdd_eq, dq, qOf]
    cases dbl <;> simp only [Bool.false_eq_true, ↓reduceIte] at hEq ⊢ <;>
      (repeat rw [e _ _ (by omega)]) <;>
      exact hEq

end VG.Proof.Weierstrass.PPC64LE.Point
