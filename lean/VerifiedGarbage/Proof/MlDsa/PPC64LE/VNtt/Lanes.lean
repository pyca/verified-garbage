module

public import VerifiedGarbage.Proof.Framework.PPC64LE.Vector
public import VerifiedGarbage.Proof.MlDsa.Arith.Zq

/-!
# ML-DSA's vector NTT on PPC64LE: lanes

The word lanes of vectors (`ofVWords`, `vword`), the lanes `vperm` and the
even and odd products give, and the arithmetic of one lane of the
butterfly (`bfly_lane`): Shoup's product (`shoup_lane`) and the reductions
by `vminuw` (`minu_sub`, `minu_add_lane`, `minu_sub_lane`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.VNtt

open VG VG.PPC64LE

/-! ## Word lanes -/

theorem wordTerm_bit (f : Nat → BitVec 32) {k j r : Nat} (hk : k < 4) (hj : j < 4) (hr : r < 32) :
    ((f k).setWidth 128 <<< (32 * (3-k))).getLsbD (32*j+r) =
      if j = 3-k then (f k).getLsbD r else false := by
  simp only [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
  by_cases h : j = 3-k
  · subst j
    simp only [show ¬32*(3-k)+r < 32*(3-k) by omega, decide_false,
      Bool.not_false, Nat.add_sub_cancel_left, show 32*(3-k)+r < 128 by omega,
      show r < 128 by omega, decide_true, Bool.true_and, ite_true]
  · have h' : 32*j+r < 32*(3-k) ∨ 32 ≤ 32*j+r-32*(3-k) := by omega
    rcases h' with h' | h' <;> simp [h, h']

theorem word_bit (f : Nat → BitVec 32) {j r : Nat} (hj : j < 4) (hr : r < 32) :
    ∀ k, k ≤ 4 →
    ((List.range k).foldl (fun x i => x ||| ((f i).setWidth 128 <<< (32*(3-i)))) (0#128)).getLsbD (32*j+r) =
      if 3-j < k then (f (3-j)).getLsbD r else false
  | 0, _ => by simp
  | k+1, hk => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      BitVec.getLsbD_or, word_bit f hj hr k (by omega), wordTerm_bit f (by omega) hj hr]
    by_cases h : 3-j < k
    · simp [h, show 3-j < k+1 by omega, show j ≠ 3-k by omega]
    · by_cases e : j = 3-k
      · rw [ite_eq_right h, ite_eq_left e, ite_eq_left (show 3-j < k+1 by omega), Bool.false_or]
        exact congrArg (fun i => (f i).getLsbD r) (by omega)
      · simp [h, e, show ¬3-j < k+1 by omega]

theorem vword_ofVWords (f : Nat → BitVec 32) {i : Nat} (hi : i < 4) : vword (ofVWords f) i = f i := by
  apply BitVec.eq_of_getLsbD_eq
  intro r hr
  simp only [vword, BitVec.getLsbD_extractLsb', hr, decide_true, Bool.true_and]
  have := word_bit f (j := 3-i) (by omega) hr 4 (by omega)
  simp only [show 3-(3-i) = i by omega, hi, ite_true] at this
  exact this

theorem ext_vword {a b : BitVec 128} (h : ∀ i < 4, vword a i = vword b i) : a = b := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have he := congrArg (BitVec.getLsbD · (j % 32)) (h (3-j/32) (by omega))
  simp only [vword, BitVec.getLsbD_extractLsb', show j % 32 < 32 by omega,
    decide_true, Bool.true_and] at he
  rwa [show 32*(3-(3-j/32)) + j%32 = j by omega] at he


/-- `vperm`'s result. -/
def permV (n m c : BitVec 128) : BitVec 128 := ofVBytes fun i =>
  let j := (vbyte c i).toNat % 32
  if j < 16 then vbyte n j else vbyte m (j - 16)

/-- Lane `i` of `vperm` is word `k` of `VA || VB` when the control's bytes
`4i … 4i+3` select its bytes. -/
theorem vword_permV (n m c : BitVec 128) {i k : Nat} (hi : i < 4) (hk : k < 8)
    (hc : ∀ t < 4, (vbyte c (4*i+t)).toNat % 32 = 4*k+t) :
    vword (permV n m c) i = if k < 4 then vword n k else vword m (k-4) := by
  apply BitVec.eq_of_getLsbD_eq
  intro r hr
  simp only [vword, BitVec.getLsbD_extractLsb', hr, decide_true, Bool.true_and]
  have e : 32*(3-i)+r = 8*(15-(4*i+(3-r/8)))+r%8 := by omega
  rw [e, permV, getLsbD_packed _ (by omega) (by omega), show 15-(15-(4*i+(3-r/8))) = 4*i+(3-r/8) by omega]
  simp only [hc _ (by omega : 3 - r/8 < 4)]
  split <;> split
  · simp only [vbyte, BitVec.getLsbD_extractLsb', show r % 8 < 8 by omega, hr, decide_true, Bool.true_and]
    exact congrArg _ (by omega)
  · omega
  · omega
  · simp only [vbyte, BitVec.getLsbD_extractLsb', show r % 8 < 8 by omega, hr, decide_true, Bool.true_and]
    exact congrArg _ (by omega)

/-- The high words of two doublewords. -/
theorem vword_dw_hi (a b : BitVec 64) :
    (vword (a ++ b) 0).toNat = a.toNat / 2^32 ∧ (vword (a ++ b) 2).toNat = b.toNat / 2^32 := by
  constructor <;>
  · simp only [vword, BitVec.extractLsb'_toNat, BitVec.toNat_append, Nat.shiftRight_eq_div_pow]
    have := a.isLt; have := b.isLt
    rw [← Nat.shiftLeft_add_eq_or_of_lt b.isLt, Nat.shiftLeft_eq]
    omega

/-! ## Shoup's product -/

/-- Shoup: `hi = ⌊b·⌊z·2³²/q⌋/2³²⌋` gives `0 ≤ b·z − hi·q < 2q`. -/
theorem shoup_bounds {q b z : Nat} (hq : 0 < q) (hb : b < 2^32) :
    (b * (z * 2^32 / q) / 2^32) * q ≤ b * z ∧
    b * z < (b * (z * 2^32 / q) / 2^32) * q + 2 * q := by
  have e1 : z * 2^32 / q * q ≤ z * 2^32 := Nat.div_mul_le_self _ _
  have e2 : z * 2^32 < z * 2^32 / q * q + q := Nat.lt_div_mul_add hq
  have h1 : b * (z * 2^32 / q) / 2^32 * 2^32 ≤ b * (z * 2^32 / q) := Nat.div_mul_le_self _ _
  have h2 : b * (z * 2^32 / q) < b * (z * 2^32 / q) / 2^32 * 2^32 + 2^32 := Nat.lt_div_mul_add (by decide)
  generalize z * 2^32 / q = z' at *
  generalize b * z' / 2^32 = hi at *
  constructor
  · apply Nat.le_of_mul_le_mul_right (c := 2^32) _ (by decide)
    calc hi * q * 2^32 = hi * 2^32 * q := Nat.mul_right_comm _ _ _
      _ ≤ b * z' * q := Nat.mul_le_mul_right _ h1
      _ = b * (z' * q) := Nat.mul_assoc _ _ _
      _ ≤ b * (z * 2^32) := Nat.mul_le_mul_left _ e1
      _ = b * z * 2^32 := (Nat.mul_assoc _ _ _).symm
  · apply Nat.lt_of_mul_lt_mul_right (a := 2^32)
    have m1 : b * z' * q < (hi * 2^32 + 2^32) * q := Nat.mul_lt_mul_of_pos_right h2 hq
    have m2 : b * q < 2^32 * q := Nat.mul_lt_mul_of_pos_right hb hq
    calc b * z * 2^32 = b * (z * 2^32) := Nat.mul_assoc _ _ _
      _ ≤ b * (z' * q + q) := Nat.mul_le_mul_left _ (Nat.le_of_lt e2)
      _ = b * z' * q + b * q := by rw [Nat.mul_add, Nat.mul_assoc]
      _ < (hi * 2^32 + 2^32) * q + 2^32 * q := Nat.add_lt_add m1 m2
      _ = (hi * q + 2 * q) * 2^32 := by
        rw [Nat.add_mul, Nat.add_mul, Nat.mul_right_comm hi (2^32) q, Nat.mul_assoc 2 q,
          Nat.mul_comm q (2^32)]; omega


/-- `vminuw`'s lane. -/
def minu32 (x y : BitVec 32) : BitVec 32 := if x.toNat < y.toNat then x else y

/-- Reduce `r < 2q` to `r mod q`: `min(r, r − q)`. -/
theorem minu_sub {r qv : BitVec 32} (hq : 0 < qv.toNat) (hr : r.toNat < 2 * qv.toNat) (h2 : 2 * qv.toNat ≤ 2^32) :
    (minu32 r (r - qv)).toNat = r.toNat % qv.toNat := by
  unfold minu32
  have := r.isLt
  have hs := BitVec.toNat_sub r qv
  by_cases h : r.toNat < qv.toNat
  · rw [Nat.mod_eq_of_lt h, ite_eq_left (by omega)]
  · rw [ite_eq_right (by omega), hs, show r.toNat % qv.toNat = r.toNat - qv.toNat from by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]]
    omega

/-- The Shoup product of one word lane: with `hi` the high word of `b·z'`,
`b·z − hi·q` modulo 2³², then `min` with that minus `q`. -/
theorem shoup_lane (b hi qv zv zpv : BitVec 32) (hq : 0 < qv.toNat) (hq2 : 2 * qv.toNat ≤ 2^32)
    (hzp : zpv.toNat = zv.toNat * 2^32 / qv.toNat) (hhi : hi.toNat = b.toNat * zpv.toNat / 2^32) :
    (minu32 (b * zv - hi * qv) (b * zv - hi * qv - qv)).toNat = b.toNat * zv.toNat % qv.toNat := by
  obtain ⟨l, u⟩ := shoup_bounds (q := qv.toNat) (z := zv.toNat) hq b.isLt
  rw [hzp] at hhi
  generalize b.toNat * (zv.toNat * 2^32 / qv.toNat) / 2^32 = h0 at l u hhi
  have hr : (b * zv - hi * qv).toNat = b.toNat * zv.toNat - h0 * qv.toNat := by
    rw [BitVec.toNat_sub, BitVec.toNat_mul, BitVec.toNat_mul, hhi]
    generalize b.toNat * zv.toNat = x at l u ⊢
    generalize h0 * qv.toNat = y at l u ⊢
    omega
  rw [minu_sub hq (by omega) hq2, hr,
    show b.toNat * zv.toNat = (b.toNat * zv.toNat - h0 * qv.toNat) + h0 * qv.toNat by omega,
    Nat.add_mul_mod_self_right, Nat.add_sub_cancel]

/-- `a + t` reduced: `min(s, s − q)`. -/
theorem minu_add_lane {a t qv : BitVec 32} (hq : 0 < qv.toNat) (hq2 : 2 * qv.toNat ≤ 2^32)
    (ha : a.toNat < qv.toNat) (ht : t.toNat < qv.toNat) :
    (minu32 (a + t) (a + t - qv)).toNat = (a.toNat + t.toNat) % qv.toNat := by
  have hs : (a + t).toNat = a.toNat + t.toNat := by rw [BitVec.toNat_add]; omega
  rw [minu_sub hq (by omega) hq2, hs]

/-- `a − t` reduced: `min(d, d + q)`. -/
theorem minu_sub_lane {a t qv : BitVec 32} (hq2 : 2 * qv.toNat ≤ 2^32)
    (ha : a.toNat < qv.toNat) (ht : t.toNat < qv.toNat) :
    (minu32 (a - t) (a - t + qv)).toNat = (a.toNat + (qv.toNat - t.toNat)) % qv.toNat := by
  unfold minu32
  have hd := BitVec.toNat_sub a t
  have hd2 := BitVec.toNat_add (a - t) qv
  by_cases h : t.toNat ≤ a.toNat
  · rw [ite_eq_left (by omega), hd]
    rw [show (a.toNat + (qv.toNat - t.toNat)) % qv.toNat = a.toNat - t.toNat from by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega]
    omega
  · rw [ite_eq_right (by omega), hd2, hd, Nat.mod_eq_of_lt (by omega : a.toNat + (qv.toNat - t.toNat) < qv.toNat)]
    omega


open VG.Spec.MlDsa (q Zq)
open VG.Proof.MlDsa.Arith (val_add' val_sub' val_mul val_lt)

/-- One lane of the butterfly: `(a + z·b, a − z·b)`, with `hi` the high word
of `b·z'`. -/
theorem bfly_lane (a b hi qv zv zpv : BitVec 32) (x y z : Zq) (hqv : qv.toNat = q)
    (hzv : zv.toNat = z.val) (hzp : zpv.toNat = z.val * 2^32 / q) (ha : a.toNat = x.val) (hb : b.toNat = y.val)
    (hhi : hi.toNat = b.toNat * zpv.toNat / 2^32) :
    let t := minu32 (b * zv - hi * qv) (b * zv - hi * qv - qv)
    (minu32 (a + t) (a + t - qv)).toNat = (x + z * y).val ∧
    (minu32 (a - t) (a - t + qv)).toNat = (x - z * y).val := by
  intro t
  have hq : 0 < qv.toNat := by rw [hqv]; decide
  have hq2 : 2 * qv.toNat ≤ 2^32 := by rw [hqv]; decide
  have ht : t.toNat = (z * y).val := by
    rw [shoup_lane b hi qv zv zpv hq hq2 (by rw [hzp, hzv, hqv]) hhi, val_mul, hb, hzv, hqv, Nat.mul_comm]
  have hax : a.toNat < qv.toNat := by rw [ha, hqv]; exact x.isLt
  have htx : t.toNat < qv.toNat := by rw [ht, hqv]; exact (z * y).isLt
  constructor
  · rw [minu_add_lane hq hq2 hax htx, val_add', ha, ht, hqv]
  · rw [minu_sub_lane hq2 hax htx, val_sub', ha, ht, hqv]

/-- One lane of the inverse butterfly: `a + b`, and `z·(b − a)` with
`d = b − a` reduced first. -/
theorem ibfly_lane (a b hi qv zv zpv : BitVec 32) (x y z : Zq) (hqv : qv.toNat = q)
    (hzv : zv.toNat = z.val) (hzp : zpv.toNat = z.val * 2^32 / q) (ha : a.toNat = x.val) (hb : b.toNat = y.val)
    (hhi : hi.toNat = (minu32 (b - a) (b - a + qv)).toNat * zpv.toNat / 2^32) :
    (minu32 (a + b) (a + b - qv)).toNat = (x + y).val ∧
    (minu32 (minu32 (b - a) (b - a + qv) * zv - hi * qv) (minu32 (b - a) (b - a + qv) * zv - hi * qv - qv)).toNat =
      (z * (y - x)).val := by
  have hq : 0 < qv.toNat := by rw [hqv]; decide
  have hq2 : 2 * qv.toNat ≤ 2^32 := by rw [hqv]; decide
  have hax : a.toNat < qv.toNat := by rw [ha, hqv]; exact x.isLt
  have hbx : b.toNat < qv.toNat := by rw [hb, hqv]; exact y.isLt
  have hd : (minu32 (b - a) (b - a + qv)).toNat = (y - x).val := by
    rw [minu_sub_lane hq2 hbx hax, val_sub', ha, hb, hqv]
  constructor
  · rw [minu_add_lane hq hq2 hax hbx, val_add', ha, hb, hqv]
  · rw [shoup_lane _ hi qv zv zpv hq hq2 (by rw [hzp, hzv, hqv]) hhi, val_mul, hd, hzv, hqv, Nat.mul_comm]

/-- One lane of a product by `z`: Shoup's, reduced. -/
theorem smul_lane (a hi qv zv zpv : BitVec 32) (x z : Zq) (hqv : qv.toNat = q)
    (hzv : zv.toNat = z.val) (hzp : zpv.toNat = z.val * 2^32 / q) (ha : a.toNat = x.val)
    (hhi : hi.toNat = a.toNat * zpv.toNat / 2^32) :
    (minu32 (a * zv - hi * qv) (a * zv - hi * qv - qv)).toNat = (z * x).val := by
  have hq : 0 < qv.toNat := by rw [hqv]; decide
  have hq2 : 2 * qv.toNat ≤ 2^32 := by rw [hqv]; decide
  rw [shoup_lane _ hi qv zv zpv hq hq2 (by rw [hzp, hzv, hqv]) hhi, val_mul, ha, hzv, hqv, Nat.mul_comm]

end VG.Proof.MlDsa.PPC64LE.VNtt
