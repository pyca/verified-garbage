module

public import VerifiedGarbage.Proof.X25519.Montgomery
public import VerifiedGarbage.Proof.X25519.Ladder
import VerifiedGarbage.Proof.X25519.Edwards.Ladder
import VerifiedGarbage.Proof.Ed25519.Group.Extended
public import VerifiedGarbage.Proof.X25519.Bytes
public import VerifiedGarbage.Impl.X25519.Model
public import VerifiedGarbage.Spec.X25519.Contract
import Mathlib.Tactic.Ring

/-! # The RFC ladder computes Wychelean's group scalar multiplication -/

@[expose] public section

namespace VG.Proof.X25519.Wychelean

open VG.Spec.X25519
open VG.X25519Model
open Montgomery
open _root_.X25519 (BaseField)
def toField (a : Fe) : BaseField := a

theorem toField_add (a b : Fe) : toField (a + b) = toField a + toField b := rfl
theorem toField_sub (a b : Fe) : toField (a - b) = toField a - toField b := rfl
theorem toField_mul (a b : Fe) : toField (a * b) = toField a * toField b := rfl
theorem toField_one : toField 1 = 1 := rfl
theorem toField_zero : toField 0 = 0 := rfl

abbrev U (d : BaseField) (a : Fe × Fe) (P : Montgomery.Point d) : Prop :=
  Rep d (toField a.1) (toField a.2) P

def Inv (d : BaseField) (B : Montgomery.Point d) (k n : Nat) (st : Ladder) : Prop :=
  U d ((cswap st.swap st.x2 st.x3).1, (cswap st.swap st.z2 st.z3).1) ((k >>> n) • B) ∧
    U d ((cswap st.swap st.x2 st.x3).2, (cswap st.swap st.z2 st.z3).2) ((k >>> n + 1) • B)

variable {d : BaseField} {u : Fe} {B : Montgomery.Point d}

theorem dbl {x z : Fe} {P : Montgomery.Point d} (hd : d ≠ 0) (h : U d (x, z) P) :
    U d ((x + z) * (x + z) * ((x - z) * (x - z)),
      ((x + z) * (x + z) - (x - z) * (x - z)) *
        ((x + z) * (x + z) + a24 * ((x + z) * (x + z) - (x - z) * (x - z)))) (P + P) := by
  have hh := h.double hd
  simp only [U, toField_mul, toField_add, toField_sub]
  have ha : toField a24 = 121665 := rfl
  rw [ha]
  convert hh using 1 <;> dsimp [doubleX, doubleZ] <;> ring

theorem dadd {x2 z2 x3 z3 : Fe} {P Q : Montgomery.Point d}
    (hd : d ≠ 0) (hu : toField u ≠ 0) (hB : Rep d (toField u) 1 B)
    (h2 : U d (x2, z2) P) (h3 : U d (x3, z3) Q)
    (hb : Q - P = B ∨ P - Q = B) :
    U d (((x3 - z3) * (x2 + z2) + (x3 + z3) * (x2 - z2)) *
        ((x3 - z3) * (x2 + z2) + (x3 + z3) * (x2 - z2)),
      u * (((x3 - z3) * (x2 + z2) - (x3 + z3) * (x2 - z2)) *
        ((x3 - z3) * (x2 + z2) - (x3 + z3) * (x2 - z2)))) (P + Q) := by
  have hdiff : Rep d (toField u) 1 (Q - P) := by
    rcases hb with hb | hb
    · rw [hb]; exact hB
    · have hn := hB.neg
      rw [← hb, neg_sub] at hn
      exact hn
  have hh := (h2.add hd hu h3 hdiff).scale (by decide : (4 : BaseField) ≠ 0)
  simp only [U, toField_mul, toField_add, toField_sub]
  convert hh using 1 <;> dsimp [addX, addZ] <;> ring

/-- One iteration keeps `Inv`, for bit `n` of the scalar. -/
theorem inv_step (hd : d ≠ 0) (hu : toField u ≠ 0) (hB : Rep d (toField u) 1 B) (k n : Nat) (st : Ladder) (hs : st.swap ≤ 1) (h : Inv d B k (n + 1) st) :
    Inv d B k n (ladderStep k u st n) := by
  have hm : k >>> n = 2 * (k >>> (n + 1)) + bit k n := by
    simp only [bit, Nat.shiftRight_succ, Nat.and_one_is_mod]; omega
  set m := k >>> (n + 1)
  obtain ⟨h0, h1⟩ := h
  rw [ladderStep_eq]
  have hb := bit_le k n
  -- The swap applied in the step is the stored one, then the bit's.
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hs with hs0 | hs1 <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with hb0 | hb1
  · simp only [hs0, hb0, cswap, Nat.xor_self, Nat.reduceEqDiff, ↓reduceIte] at h0 h1 ⊢
    refine ⟨?_, ?_⟩
    · rw [hm, hb0, Nat.add_zero, two_mul, add_nsmul]; exact dbl hd h0
    · rw [hm, hb0, Nat.add_zero, show 2 * m + 1 = m + (m + 1) by omega, add_nsmul]
      exact dadd hd hu hB h0 h1 (Or.inl (by rw [add_nsmul, one_nsmul, add_sub_cancel_left]))
  · simp only [hs0, hb1, cswap, Nat.zero_xor, ↓reduceIte] at h0 h1 ⊢
    refine ⟨?_, ?_⟩
    · rw [hm, hb1, show 2 * m + 1 = (m + 1) + m by omega, add_nsmul]
      exact dadd hd hu hB h1 h0 (Or.inr (by rw [add_nsmul, one_nsmul, add_sub_cancel_left]))
    · rw [hm, hb1, show 2 * m + 1 + 1 = (m + 1) + (m + 1) by omega, add_nsmul]; exact dbl hd h1
  · simp only [hs1, hb0, cswap, Nat.xor_zero, ↓reduceIte] at h0 h1 ⊢
    refine ⟨?_, ?_⟩
    · rw [hm, hb0, Nat.add_zero, two_mul, add_nsmul]; exact dbl hd h0
    · rw [hm, hb0, Nat.add_zero, show 2 * m + 1 = m + (m + 1) by omega, add_nsmul]
      exact dadd hd hu hB h0 h1 (Or.inl (by rw [add_nsmul, one_nsmul, add_sub_cancel_left]))
  · simp only [hs1, hb1, cswap, Nat.xor_self, ↓reduceIte] at h0 h1 ⊢
    refine ⟨?_, ?_⟩
    · rw [hm, hb1, show 2 * m + 1 = (m + 1) + m by omega, add_nsmul]
      exact dadd hd hu hB h1 h0 (Or.inr (by rw [add_nsmul, one_nsmul, add_sub_cancel_left]))
    · rw [hm, hb1, show 2 * m + 1 + 1 = (m + 1) + (m + 1) by omega, add_nsmul]; exact dbl hd h1

theorem inv_init (hB : Rep d (toField u) 1 B) (k : Nat) (h0 : k >>> 255 = 0) :
    Inv d B k 255 (VG.Proof.X25519.init u) := by
  simp only [Inv, U, VG.Proof.X25519.init, cswap, h0, zero_nsmul, zero_add, one_nsmul,
    Nat.reduceEqDiff, ↓reduceIte, toField_one, toField_zero]
  exact ⟨⟨rfl, one_ne_zero⟩, hB⟩

theorem inv_after (hd : d ≠ 0) (hu : toField u ≠ 0) (hB : Rep d (toField u) 1 B) (k : Nat) (hk : k >>> 255 = 0) :
    ∀ j ≤ 255, Inv d B k (255 - j) (ladderAfter k u (255 - j)) := by
  intro j
  induction j with
  | zero => intro _; rw [ladderAfter_255]; exact inv_init hB k hk
  | succ j ih =>
    intro hj
    have hn : 255 - (j + 1) < 255 := by omega
    rw [ladderAfter_step k u hn]
    have e : 255 - (j + 1) + 1 = 255 - j := by omega
    refine inv_step hd hu hB k _ _ ?_ ?_
    · rw [e]; exact ladderAfter_swap_le k u (by omega)
    · rw [e]; exact ih (by omega)


/-- The ladder's field result before encoding. -/
def result (k : Nat) (u : Fe) : Fe :=
  let st := ladderAfter k u 0
  (cswap st.swap st.x2 st.x3).1 * pow (cswap st.swap st.z2 st.z3).1 (P - 2)

theorem toField_pow (a : Fe) (e : Nat) : toField (pow a e) = toField a ^ e := by
  exact Ed25519.toZ_pow a e

theorem group_result (hd : d ≠ 0) (hu : toField u ≠ 0) (hB : Rep d (toField u) 1 B)
    (k : Nat) (hk : k >>> 255 = 0) :
    toField (result k u) = _root_.X25519.uCoord (k • B) / d := by
  have h := (inv_after hd hu hB k hk 255 le_rfl).1
  rw [Nat.sub_self, Nat.shiftRight_zero] at h
  have ho := h.out hd
  simp only [result, toField_mul, toField_pow]
  rw [show (toField (cswap (ladderAfter k u 0).swap (ladderAfter k u 0).z2
      (ladderAfter k u 0).z3).1) ^ (P - 2) =
      (toField (cswap (ladderAfter k u 0).swap (ladderAfter k u 0).z2
        (ladderAfter k u 0).z3).1)⁻¹ from Edwards.pow_P_sub_two _]
  exact ho

/-- The curve is the scaling parameter one of the same family as the twist. -/
theorem curve_eq_twist_one : _root_.X25519.Curve = _root_.X25519.Twist 1 := by
  simp only [_root_.X25519.Curve, _root_.X25519.Twist, one_mul, one_pow]

theorem curve_result (u : Fe) (hu : toField u ≠ 0) (k : Nat) (hk : k >>> 255 = 0) :
    ∀ (x y : BaseField) (hp : _root_.X25519.Curve.toAffine.Nonsingular x y),
      x = toField u → toField (result k u) =
        _root_.X25519.uCoord (k • WeierstrassCurve.Affine.Point.some x y hp) := by
  rw [curve_eq_twist_one]
  intro x y hp hx
  have hB : Rep 1 (toField u) 1 (WeierstrassCurve.Affine.Point.some x y hp) := by
    exact ⟨by rw [hx, one_mul, mul_one], one_ne_zero⟩
  simpa only [div_one] using group_result (by decide : (1 : BaseField) ≠ 0) hu hB k hk

theorem zero_step (k n : Nat) (st : Ladder) (h2 : st.z2 = 0) (h3 : st.z3 = 0) :
    (ladderStep k 0 st n).z2 = 0 ∧ (ladderStep k 0 st n).z3 = 0 := by
  simp [ladderStep, cswap, h2, h3]

theorem zero_first (k : Nat) :
    (ladderAfter k 0 254).z2 = 0 ∧ (ladderAfter k 0 254).z3 = 0 := by
  rw [ladderAfter_step k 0 (by decide), show 254 + 1 = 255 from rfl, ladderAfter_255, ladderStep_eq]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (bit_le k 254) with hb | hb <;>
    simp only [init, hb, cswap, Nat.zero_xor, Nat.reduceEqDiff, ↓reduceIte] <;> decide

theorem zero_after (k : Nat) : ∀ j ≤ 254,
    (ladderAfter k 0 (254 - j)).z2 = 0 ∧ (ladderAfter k 0 (254 - j)).z3 = 0 := by
  intro j
  induction j with
  | zero => intro _; exact zero_first k
  | succ j ih =>
    intro hj
    have e : 254 - (j + 1) + 1 = 254 - j := by omega
    rw [ladderAfter_step k 0 (by omega)]
    obtain ⟨h2, h3⟩ := ih (by omega)
    apply zero_step <;> rwa [e]

theorem result_zero (k : Nat) : toField (result k 0) = 0 := by
  obtain ⟨h2, h3⟩ := zero_after k 254 le_rfl
  simp only [Nat.sub_self] at h2 h3
  simp only [result, h2, h3, cswap]
  split <;> simp only [toField_mul, toField_pow, toField_zero,
    zero_pow (by decide : P - 2 ≠ 0), mul_zero]

theorem torsion_zero_result (k : Nat) (y : BaseField)
    (hp : _root_.X25519.Curve.toAffine.Nonsingular 0 y) :
    _root_.X25519.uCoord (k • WeierstrassCurve.Affine.Point.some 0 y hp) = 0 := by
  have he := (WeierstrassCurve.Affine.equation_iff' ..).mp hp.1
  have hy : y = 0 := by
    simpa [_root_.X25519.Curve] using he
  let B := WeierstrassCurve.Affine.Point.some 0 y hp
  have hdouble : B + B = 0 := by
    apply WeierstrassCurve.Affine.Point.add_self_of_Y_eq
    simp only [WeierstrassCurve.Affine.negY, _root_.X25519.Curve, zero_mul, sub_zero, hy, neg_zero]
  have h : ∀ n : Nat, n • B = 0 ∨ n • B = B := by
    intro n
    induction n with
    | zero => exact Or.inl (zero_nsmul B)
    | succ n ih =>
      rw [succ_nsmul]
      rcases ih with ih | ih
      · exact Or.inr (by rw [ih, zero_add])
      · exact Or.inl (by rw [ih, hdouble])
  rcases h k with h | h <;> rw [h] <;> rfl

open VG.Spec.X25519 (outputBytes inputAt)

theorem leNum_uint8 (bs : List UInt8) :
    leNum (bs.map UInt8.toBitVec) = _root_.X25519.decodeLittleEndian bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.map_cons, leNum, _root_.X25519.decodeLittleEndian, List.foldr_cons,
      UInt8.toNat_toBitVec, Nat.shiftLeft_eq] at ih ⊢
    rw [ih]
    omega

theorem decodeLE_bytes (v : Vector UInt8 32) :
    decodeLittleEndian (outputBytes v) = _root_.X25519.decodeLittleEndian v.toList := by
  rw [decodeLittleEndian_eq, List.take_of_length_le (by simp [outputBytes])]
  exact leNum_uint8 v.toList

theorem outputBytes_set (v : Vector UInt8 32) (i : Nat) (hi : i < 32) (b : UInt8) :
    outputBytes (v.set i b) = (outputBytes v).set i b.toBitVec := by
  simp only [outputBytes, Vector.toList_set hi, List.map_set]

theorem outputBytes_getD (v : Vector UInt8 32) (i : Nat) (hi : i < 32) :
    (outputBytes v).getD i 0 = v[i].toBitVec := by
  simp [outputBytes, List.getD_eq_getElem?_getD, hi]

theorem decodeU_bytes (v : Vector UInt8 32) :
    decodeUCoordinate (outputBytes v) = _root_.X25519.decodeUCoordinate v := by
  simp only [decodeUCoordinate, _root_.X25519.decodeUCoordinate, ← decodeLE_bytes,
    outputBytes_set, outputBytes_getD v 31 (by decide)]
  rfl

theorem decodeScalar_bytes (v : Vector UInt8 32) :
    decodeScalar25519 (outputBytes v) = _root_.X25519.decodeScalar v := by
  simp only [decodeScalar25519, _root_.X25519.decodeScalar, ← decodeLE_bytes, outputBytes_set,
    outputBytes_getD v 0 (by decide)]
  rw [getD_set (outputBytes v) (i := 0) 31 _ (by simp [outputBytes])]
  simp only [show ¬ (0 : Nat) = 31 by decide, ↓reduceIte, outputBytes_getD v 31 (by decide)]
  rfl

theorem encode_bytes (a : Fe) : encodeUCoordinate a =
    outputBytes (_root_.X25519.encodeUCoordinate (toField a)) := by
  apply List.ext_getElem
  · simp [encodeUCoordinate, outputBytes]
  · intro i hi hj
    simp only [encodeUCoordinate, List.getElem_map, List.getElem_range,
      outputBytes, Vector.getElem_toList, _root_.X25519.encodeUCoordinate, Vector.getElem_ofFn]
    rfl

theorem curvePoint_result (u : Fe) (k : Nat) (hk : k >>> 255 = 0)
    (B : _root_.X25519.Curve.toAffine.Point)
    (hb : _root_.X25519.mkCurvePoint (toField u) = some B) :
    toField (result k u) = _root_.X25519.uCoord (k • B) := by
  unfold _root_.X25519.mkCurvePoint at hb
  dsimp only at hb
  split at hb
  next hs =>
    simp only [Option.some.injEq] at hb
    subst B
    by_cases hu : toField u = 0
    · have huz : u = 0 := hu
      subst u
      rw [result_zero]
      exact (torsion_zero_result k _ _).symm
    · exact curve_result u hu k hk _ _ _ rfl
  next => cases hb

theorem twistPoint_result (u : Fe) (hu : toField u ≠ 0) (k : Nat) (hk : k >>> 255 = 0)
    (B : (_root_.X25519.Twist 2).toAffine.Point)
    (hb : _root_.X25519.mkTwistPoint 2 (by decide) (toField u) = some B) :
    toField (result k u) = _root_.X25519.uCoord (k • B) / 2 := by
  unfold _root_.X25519.mkTwistPoint at hb
  dsimp only at hb
  split at hb
  next hs =>
    simp only [Option.some.injEq] at hb
    subst B
    refine group_result (d := 2) (by decide) hu ?_ k hk
    exact ⟨by rw [mul_one], one_ne_zero⟩
  next => cases hb

theorem missing_curve_nonzero (u : BaseField) (h : _root_.X25519.mkCurvePoint u = none) : u ≠ 0 := by
  intro hu
  subst u
  have hs : IsSquare (_root_.X25519.curveRhs 0) := by
    simp [_root_.X25519.curveRhs]
  have hi := _root_.X25519.mkCurvePoint_isSome hs
  rw [h] at hi
  exact Bool.noConfusion hi

/-- Agreement of the complete byte-to-byte functions, including zero and
noncanonical inputs. No restriction is placed on the peer's u-coordinate. -/
theorem x25519_eq_wychelean (scalar point : Vector UInt8 32) :
    x25519 (outputBytes scalar) (outputBytes point) =
      outputBytes (_root_.X25519.x25519 scalar point) := by
  have hk := Edwards.decodeScalar25519_shift (kb := outputBytes scalar) (by simp [outputBytes])
  rw [decodeScalar_bytes] at hk
  rw [x25519_eq]
  simp only [invert_eq]
  change encodeUCoordinate (result (decodeScalar25519 (outputBytes scalar))
    (toFe (decodeUCoordinate (outputBytes point)))) = _
  rw [encode_bytes, decodeScalar_bytes, decodeU_bytes]
  apply congrArg outputBytes
  unfold _root_.X25519.x25519 _root_.X25519.scalarMulGeneric
  apply congrArg _root_.X25519.encodeUCoordinate
  let u := toFe (_root_.X25519.decodeUCoordinate point)
  change toField (result (_root_.X25519.decodeScalar scalar) u) = _
  have hu : toField u = (_root_.X25519.decodeUCoordinate point : BaseField) := rfl
  rw [← hu]
  split
  next hb =>
    exact curvePoint_result u _ hk _ (Option.some_get hb).symm
  next hb =>
    have hn := Option.not_isSome_iff_eq_none.mp hb
    exact twistPoint_result u (missing_curve_nonzero _ hn) _ hk _ (Option.some_get _).symm

theorem outputBytes_inputAt (m : Mem) (p : Addr) : outputBytes (inputAt m p) = bytesAt m p 32 := by
  apply List.ext_getElem
  · simp [outputBytes, bytesAt]
  · intro i hi hj
    simp [outputBytes, inputAt, bytesAt] at hi hj ⊢

theorem outputBytes_basePoint :
    outputBytes (_root_.X25519.encodeUCoordinate _root_.X25519.BasePointU) = basePoint := by
  decide

/-- The public exchange contract follows from the internal ladder contract.
This is a theorem, not a trusted definition or an extra precondition. -/
theorem exchangeContract_ladder {M : ISA} (A : Abi M) (stack : Nat) :
    Spec.X25519.exchangeContract A stack =
      exchangeSig.contract A (post := fun out scalar point _scratch m m' r =>
        let z := x25519 (bytesAt m scalar 32) (bytesAt m point 32)
        bytesAt m' out 32 = z ∧ r = if z = List.replicate 32 0 then 0 else 1)
        (stack := stack) := by
  unfold Spec.X25519.exchangeContract
  apply congrArg (fun post => exchangeSig.contract A (post := post) (stack := stack))
  funext out scalar point scratch m m' r
  rw [← x25519_eq_wychelean, outputBytes_inputAt, outputBytes_inputAt]

theorem baseContract_ladder {M : ISA} (A : Abi M) (stack : Nat) :
    Spec.X25519.x25519BaseContract A stack =
      x25519BaseSig.contract A (post := fun out scalar _scratch m m' _ =>
        bytesAt m' out 32 = x25519 (bytesAt m scalar 32) basePoint)
        (stack := stack) := by
  unfold Spec.X25519.x25519BaseContract
  apply congrArg (fun post => x25519BaseSig.contract A (post := post) (stack := stack))
  funext out scalar scratch m m' r
  rw [_root_.X25519.basepointMul, ← x25519_eq_wychelean, outputBytes_inputAt, outputBytes_basePoint]

end VG.Proof.X25519.Wychelean
