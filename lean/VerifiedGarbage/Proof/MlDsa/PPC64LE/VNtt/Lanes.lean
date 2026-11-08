module

public import VerifiedGarbage.Proof.Framework.PPC64LE.VWords
public import VerifiedGarbage.Proof.MlDsa.Arith.Zq

/-!
# ML-DSA's vector NTT on PPC64LE: lanes

The arithmetic of one lane of the butterfly (`bfly_lane`), on the words of
vectors of `Proof/Framework/PPC64LE/VWords.lean`: Shoup's product
(`shoup_lane`) and the reductions by `vminuw` (`minu_sub`, `minu_add_lane`,
`minu_sub_lane`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.VNtt

open VG VG.PPC64LE

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
