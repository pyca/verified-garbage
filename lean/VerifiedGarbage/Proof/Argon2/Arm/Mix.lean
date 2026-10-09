import VerifiedGarbage.Proof.Blake2.Arm.BlockB
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Argon2.Spec
import VerifiedGarbage.Impl.Argon2.Arm.Compress

/-!
# Argon2 on ARMv7: the products and GB

`mulHi_ok`: the high half of a 32 × 32-bit product, from four products of
16-bit halves (`VG.Impl.Argon2.Arm.mulHi`); `addMul_ok`: `addMul` on a pair of
registers; and `wp_gb`: GB on four words of `scratch` (at `r3`), computed in
registers as BLAKE2b's `G` is (`Proof/Blake2/Arm/BlockB.lean`), leaves the
memory `gbMem`, with the words of `Proof.Argon2.mix` stored.
-/

namespace VG.Proof.Argon2.Arm

open VG VG.Arm
open VG.Impl.Sha512.Arm (lo hi ld st add64)
open VG.Impl.Blake2.Arm.B (xor64 rotr rotr')
open VG.Impl.Argon2.Arm (mulHi addMul gb)
open VG.Proof.Sha512.Arm (Only Pair rd64 write64 A Reg64 Wrote wp_st wp_add64 mem_rd lo_toNat hi_toNat
  eq_of_lo_hi)
open VG.Proof.MdStream.Arm (Upd Mupd WP.cons wp_mov wp_add op2_reg op2_lsr op2_lsl)
open VG.Proof.Blake2.ArmB (wp_ld64 wp_xor64 wp_rotr wp_rotr' pair_swap Rd64)

/-! ## Products of halves -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_mul {d n m : Reg} (k : ∀ s', Upd s s' d (s.gpr n * s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.mul d n m :: is)) s Q :=
  WP.cons rfl (k _ (Upd.setReg _ _ _))

end

/-- The value `mulHi` leaves in `t2`. -/
def mulHiV (x y : BitVec 32) : BitVec 32 :=
  let x0 := x <<< 16 >>> 16
  let y0 := y <<< 16 >>> 16
  let y1 := y >>> 16
  let x1 := x >>> 16
  let p00 := x0 * y0
  let p01 := x0 * y1
  let p10 := x1 * y0
  let p11 := x1 * y1
  let m := (p01 <<< 16 >>> 16) + (p00 >>> 16) + ((p10 <<< 16) >>> 16)
  p11 + (p01 >>> 16) + (p10 >>> 16) + (m >>> 16)

theorem toNat_lo16 (z : BitVec 32) : (z <<< 16 >>> 16).toNat = z.toNat % 2 ^ 16 := by
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  omega

theorem toNat_hi16 (z : BitVec 32) : (z >>> 16).toNat = z.toNat / 2 ^ 16 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem toNat_mul16 {a b : BitVec 32} (ha : a.toNat < 2 ^ 16) (hb : b.toNat < 2 ^ 16) :
    (a * b).toNat = a.toNat * b.toNat := by
  rw [BitVec.toNat_mul]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le ha (Nat.le_of_lt hb) (by omega))
    (by decide))

theorem toNat_add_lt {a b : BitVec 32} (h : a.toNat + b.toNat < 2 ^ 32) :
    (a + b).toNat = a.toNat + b.toNat := by
  rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt h

theorem mul_split (X Y : Nat) :
    X * Y = (X / 2 ^ 16 * (Y / 2 ^ 16)) * 2 ^ 32 +
      (X % 2 ^ 16 * (Y / 2 ^ 16) + X / 2 ^ 16 * (Y % 2 ^ 16)) * 2 ^ 16 + X % 2 ^ 16 * (Y % 2 ^ 16) := by
  have hX := Nat.div_add_mod X (2 ^ 16)
  have hY := Nat.div_add_mod Y (2 ^ 16)
  generalize X / 2 ^ 16 = a at hX ⊢
  generalize X % 2 ^ 16 = b at hX ⊢
  generalize Y / 2 ^ 16 = c at hY ⊢
  generalize Y % 2 ^ 16 = d at hY ⊢
  subst hX hY
  grind

theorem mul16_lt {a b : Nat} (ha : a < 2 ^ 16) (hb : b < 2 ^ 16) : a * b < 2 ^ 32 :=
  Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le ha (Nat.le_of_lt hb) (by omega)) (by decide)

theorem mul16_le {a b : Nat} (ha : a < 2 ^ 16) (hb : b < 2 ^ 16) : a * b ≤ (2 ^ 16 - 1) * (2 ^ 16 - 1) :=
  Nat.mul_le_mul (by omega) (by omega)

theorem mulHiV_eq (x y : BitVec 32) : mulHiV x y = BitVec.ofNat 32 (x.toNat * y.toNat / 2 ^ 32) := by
  have hx := x.isLt
  have hy := y.isLt
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat]
  simp only [mulHiV]
  have ex0 := toNat_lo16 x
  have ey0 := toNat_lo16 y
  have ex1 := toNat_hi16 x
  have ey1 := toNat_hi16 y
  have bx0 : (x <<< 16 >>> 16).toNat < 2 ^ 16 := by rw [ex0]; omega
  have by0 : (y <<< 16 >>> 16).toNat < 2 ^ 16 := by rw [ey0]; omega
  have bx1 : (x >>> 16).toNat < 2 ^ 16 := by rw [ex1]; omega
  have by1 : (y >>> 16).toNat < 2 ^ 16 := by rw [ey1]; omega
  have e00 := toNat_mul16 bx0 by0
  have e01 := toNat_mul16 bx0 by1
  have e10 := toNat_mul16 bx1 by0
  have e11 := toNat_mul16 bx1 by1
  have l00 := mul16_le bx0 by0
  have l01 := mul16_le bx0 by1
  have l10 := mul16_le bx1 by0
  have l11 := mul16_le bx1 by1
  have split := mul_split x.toNat y.toNat
  rw [← ex0, ← ey0, ← ex1, ← ey1] at split
  generalize (x <<< 16 >>> 16) * (y <<< 16 >>> 16) = p00 at e00 l00 ⊢
  generalize (x <<< 16 >>> 16) * (y >>> 16) = p01 at e01 l01 ⊢
  generalize (x >>> 16) * (y <<< 16 >>> 16) = p10 at e10 l10 ⊢
  generalize (x >>> 16) * (y >>> 16) = p11 at e11 l11 ⊢
  rw [← e00, ← e01, ← e10, ← e11] at split
  rw [← e00] at l00
  rw [← e01] at l01
  rw [← e10] at l10
  rw [← e11] at l11
  have q01 := toNat_lo16 p01
  have q10 := toNat_lo16 p10
  have r00 := toNat_hi16 p00
  have r01 := toNat_hi16 p01
  have r10 := toNat_hi16 p10
  have m1 : ((p01 <<< 16 >>> 16) + (p00 >>> 16)).toNat = p01.toNat % 2 ^ 16 + p00.toNat / 2 ^ 16 := by
    rw [toNat_add_lt (by rw [q01, r00]; omega_using [l00]), q01, r00]
  have m2 : ((p01 <<< 16 >>> 16) + (p00 >>> 16) + (p10 <<< 16 >>> 16)).toNat =
      p01.toNat % 2 ^ 16 + p00.toNat / 2 ^ 16 + p10.toNat % 2 ^ 16 := by
    rw [toNat_add_lt (by rw [m1, q10]; omega_using [l00]), m1, q10]
  generalize (p01 <<< 16 >>> 16) + (p00 >>> 16) + (p10 <<< 16 >>> 16) = m at m2 ⊢
  have rm := toNat_hi16 m
  have a1 : (p11 + (p01 >>> 16)).toNat = p11.toNat + p01.toNat / 2 ^ 16 := by
    rw [toNat_add_lt (by rw [r01]; omega_using [l11, l01]), r01]
  have a2 : (p11 + (p01 >>> 16) + (p10 >>> 16)).toNat = p11.toNat + p01.toNat / 2 ^ 16 + p10.toNat / 2 ^ 16 := by
    rw [toNat_add_lt (by rw [a1, r10]; omega_using [l11, l01, l10]), a1, r10]
  rw [toNat_add_lt (by rw [a2, rm, m2]; omega_using [l11, l01, l10, l00]), a2, rm, m2]
  generalize x.toNat * y.toNat = P at split ⊢
  generalize p00.toNat = c at split l00 ⊢
  generalize p01.toNat = a at split l01 ⊢
  generalize p10.toNat = b at split l10 ⊢
  generalize p11.toNat = d at split l11 ⊢
  have ha := Nat.div_add_mod a (2 ^ 16)
  have hb := Nat.div_add_mod b (2 ^ 16)
  have hc := Nat.div_add_mod c (2 ^ 16)
  have ha' := Nat.mod_lt a (show 2 ^ 16 > 0 by decide)
  have hb' := Nat.mod_lt b (show 2 ^ 16 > 0 by decide)
  have hc' := Nat.mod_lt c (show 2 ^ 16 > 0 by decide)
  generalize a / 2 ^ 16 = a1 at ha ⊢
  generalize a % 2 ^ 16 = a0 at ha ha' ⊢
  generalize b / 2 ^ 16 = b1 at hb ⊢
  generalize b % 2 ^ 16 = b0 at hb hb' ⊢
  generalize c / 2 ^ 16 = c1 at hc ⊢
  generalize c % 2 ^ 16 = c0 at hc hc' ⊢
  subst ha hb hc split
  omega

/-- Two distinct registers, from the hypotheses, in either order. -/
macro "ne" : tactic => `(tactic| first | with_reducible assumption | exact Ne.symm (by with_reducible assumption))

theorem mulHi_ok {x y t0 t1 t2 t3 t4 : Reg} {rest : List Instr} {s : State} {Q : State → Prop}
    (hd : [t0, t1, t2, t3, t4].Nodup) (hx : x ∉ [t0, t1, t2, t3, t4]) (hy : y ∉ [t0, t1, t2, t3, t4])
    (k : ∀ s', Only [t0, t1, t2, t3, t4] s s' → s'.gpr t2 = mulHiV (s.gpr x) (s.gpr y) →
      WP isa (.block rest) s' Q) :
    WP isa (.block (mulHi x y t0 t1 t2 t3 t4 ++ rest)) s Q := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil,
    and_true, not_false_eq_true] at hd hx hy
  obtain ⟨⟨n01, n02, n03, n04⟩, ⟨n12, n13, n14⟩, ⟨n23, n24⟩, n34⟩ := hd
  obtain ⟨x0, x1, x2, x3, x4⟩ := hx
  obtain ⟨y0, y1, y2, y3, y4⟩ := hy
  simp only [mulHi, List.cons_append, List.nil_append]
  have l1 : (1 : Nat) ≤ 16 ∧ 16 ≤ 31 := by decide
  refine wp_mov (op2_lsl l1) fun s₁ u₁ => wp_mov (op2_lsr l1) fun s₂ u₂ => ?_
  refine wp_mov (op2_lsl l1) fun s₃ u₃ => wp_mov (op2_lsr l1) fun s₄ u₄ => ?_
  refine wp_mov (op2_lsr l1) fun s₅ u₅ => wp_mov (op2_lsr l1) fun s₆ u₆ => ?_
  refine wp_mul fun s₇ u₇ => wp_mul fun s₈ u₈ => wp_mul fun s₉ u₉ => wp_mul fun s₁₀ u₁₀ => ?_
  refine wp_mov (op2_lsl l1) fun s₁₁ u₁₁ => wp_mov (op2_lsr l1) fun s₁₂ u₁₂ => ?_
  refine wp_add (op2_lsr l1) fun s₁₃ u₁₃ => wp_mov (op2_lsl l1) fun s₁₄ u₁₄ => ?_
  refine wp_add (op2_lsr l1) fun s₁₅ u₁₅ => wp_add (op2_lsr l1) fun s₁₆ u₁₆ => ?_
  refine wp_add (op2_lsr l1) fun s₁₇ u₁₇ => wp_add (op2_lsr l1) fun s₁₈ u₁₈ => ?_
  have O := (((((((((((((((((Only.of_upd u₁).trans (Only.of_upd u₂)).trans (Only.of_upd u₃)).trans
    (Only.of_upd u₄)).trans (Only.of_upd u₅)).trans (Only.of_upd u₆)).trans (Only.of_upd u₇)).trans
    (Only.of_upd u₈)).trans (Only.of_upd u₉)).trans (Only.of_upd u₁₀)).trans (Only.of_upd u₁₁)).trans
    (Only.of_upd u₁₂)).trans (Only.of_upd u₁₃)).trans (Only.of_upd u₁₄)).trans (Only.of_upd u₁₅)).trans
    (Only.of_upd u₁₆)).trans (Only.of_upd u₁₇)).trans (Only.of_upd u₁₈)
  refine k s₁₈ (O.mono (by simp)) ?_
  -- The values, one step at a time.
  have v2 : s₂.gpr t0 = s.gpr x <<< 16 >>> 16 := by rw [u₂.gpr, u₁.gpr]
  have v4 : s₄.gpr t1 = s.gpr y <<< 16 >>> 16 := by
    rw [u₄.gpr, u₃.gpr, u₂.other _ (by ne), u₁.other _ (by ne)]
  have v5 : s₅.gpr t2 = s.gpr y >>> 16 := by
    rw [u₅.gpr, u₄.other _ (by ne), u₃.other _ (by ne), u₂.other _ (by ne), u₁.other _ (by ne)]
  have v6 : s₆.gpr t3 = s.gpr x >>> 16 := by
    rw [u₆.gpr, u₅.other _ (by ne), u₄.other _ (by ne), u₃.other _ (by ne), u₂.other _ (by ne), u₁.other _ (by ne)]
  have w6₀ : s₆.gpr t0 = s.gpr x <<< 16 >>> 16 := by
    rw [u₆.other _ (by ne), u₅.other _ (by ne), u₄.other _ (by ne), u₃.other _ (by ne), v2]
  have w6₁ : s₆.gpr t1 = s.gpr y <<< 16 >>> 16 := by
    rw [u₆.other _ (by ne), u₅.other _ (by ne), v4]
  have w6₂ : s₆.gpr t2 = s.gpr y >>> 16 := by rw [u₆.other _ (by ne), v5]
  have v7 : s₇.gpr t4 = (s.gpr x <<< 16 >>> 16) * (s.gpr y <<< 16 >>> 16) := by rw [u₇.gpr, w6₀, w6₁]
  have v8 : s₈.gpr t0 = (s.gpr x <<< 16 >>> 16) * (s.gpr y >>> 16) := by
    rw [u₈.gpr, u₇.other _ (by ne), u₇.other _ (by ne), w6₀, w6₂]
  have v9 : s₉.gpr t1 = (s.gpr x >>> 16) * (s.gpr y <<< 16 >>> 16) := by
    rw [u₉.gpr, u₈.other _ (by ne), u₈.other _ (by ne), u₇.other _ (by ne),
      u₇.other _ (by ne), v6, w6₁]
  have v10 : s₁₀.gpr t2 = (s.gpr x >>> 16) * (s.gpr y >>> 16) := by
    rw [u₁₀.gpr, u₉.other _ (by ne), u₉.other _ (by ne), u₈.other _ (by ne),
      u₈.other _ (by ne), u₇.other _ (by ne), u₇.other _ (by ne), v6, w6₂]
  have w10₀ : s₁₀.gpr t0 = (s.gpr x <<< 16 >>> 16) * (s.gpr y >>> 16) := by
    rw [u₁₀.other _ (by ne), u₉.other _ (by ne), v8]
  have w10₁ : s₁₀.gpr t1 = (s.gpr x >>> 16) * (s.gpr y <<< 16 >>> 16) := by rw [u₁₀.other _ (by ne), v9]
  have w10₄ : s₁₀.gpr t4 = (s.gpr x <<< 16 >>> 16) * (s.gpr y <<< 16 >>> 16) := by
    rw [u₁₀.other _ (by ne), u₉.other _ (by ne), u₈.other _ (by ne), v7]
  have v12 : s₁₂.gpr t3 = ((s.gpr x <<< 16 >>> 16) * (s.gpr y >>> 16)) <<< 16 >>> 16 := by
    rw [u₁₂.gpr, u₁₁.gpr, w10₀]
  have v13 : s₁₃.gpr t3 = (((s.gpr x <<< 16 >>> 16) * (s.gpr y >>> 16)) <<< 16 >>> 16) +
      (((s.gpr x <<< 16 >>> 16) * (s.gpr y <<< 16 >>> 16)) >>> 16) := by
    rw [u₁₃.gpr, v12, u₁₂.other _ (by ne), u₁₁.other _ (by ne), w10₄]
  have v14 : s₁₄.gpr t4 = ((s.gpr x >>> 16) * (s.gpr y <<< 16 >>> 16)) <<< 16 := by
    rw [u₁₄.gpr, u₁₃.other _ (by ne), u₁₂.other _ (by ne), u₁₁.other _ (by ne), w10₁]
  have v15 : s₁₅.gpr t3 = (((s.gpr x <<< 16 >>> 16) * (s.gpr y >>> 16)) <<< 16 >>> 16) +
      (((s.gpr x <<< 16 >>> 16) * (s.gpr y <<< 16 >>> 16)) >>> 16) +
      (((s.gpr x >>> 16) * (s.gpr y <<< 16 >>> 16)) <<< 16 >>> 16) := by
    rw [u₁₅.gpr, u₁₄.other _ (by ne), v13, v14]
  have w15₀ : s₁₅.gpr t0 = (s.gpr x <<< 16 >>> 16) * (s.gpr y >>> 16) := by
    rw [u₁₅.other _ (by ne), u₁₄.other _ (by ne), u₁₃.other _ (by ne), u₁₂.other _ (by ne), u₁₁.other _ (by ne), w10₀]
  have w15₁ : s₁₅.gpr t1 = (s.gpr x >>> 16) * (s.gpr y <<< 16 >>> 16) := by
    rw [u₁₅.other _ (by ne), u₁₄.other _ (by ne), u₁₃.other _ (by ne), u₁₂.other _ (by ne), u₁₁.other _ (by ne), w10₁]
  have w15₂ : s₁₅.gpr t2 = (s.gpr x >>> 16) * (s.gpr y >>> 16) := by
    rw [u₁₅.other _ (by ne), u₁₄.other _ (by ne), u₁₃.other _ (by ne), u₁₂.other _ (by ne), u₁₁.other _ (by ne), v10]
  have v16 : s₁₆.gpr t2 = (s.gpr x >>> 16) * (s.gpr y >>> 16) +
      (((s.gpr x <<< 16 >>> 16) * (s.gpr y >>> 16)) >>> 16) := by
    rw [u₁₆.gpr, w15₂, w15₀]
  have v17 : s₁₇.gpr t2 = (s.gpr x >>> 16) * (s.gpr y >>> 16) +
      (((s.gpr x <<< 16 >>> 16) * (s.gpr y >>> 16)) >>> 16) +
      (((s.gpr x >>> 16) * (s.gpr y <<< 16 >>> 16)) >>> 16) := by
    rw [u₁₇.gpr, v16, u₁₆.other _ (by ne), w15₁]
  rw [u₁₈.gpr, v17, u₁₇.other _ (by ne), u₁₆.other _ (by ne), v15]
  rfl

/-! ## `addMul` -/

theorem lo_ofNat (p : Nat) : lo (BitVec.ofNat 64 p) = BitVec.ofNat 32 p := by
  apply BitVec.eq_of_toNat_eq
  rw [lo_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_mod_of_dvd _ (by decide : 2 ^ 32 ∣ 2 ^ 64)]

theorem hi_ofNat {p : Nat} (h : p < 2 ^ 64) : hi (BitVec.ofNat 64 p) = BitVec.ofNat 32 (p / 2 ^ 32) := by
  apply BitVec.eq_of_toNat_eq
  rw [hi_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (by omega)]

theorem mul_lt (a b : BitVec 32) : a.toNat * b.toNat < 2 ^ 64 :=
  Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le a.isLt (Nat.le_of_lt b.isLt) (by decide)) (by decide)

theorem mul_ofNat (a b : BitVec 32) : a * b = BitVec.ofNat 32 (a.toNat * b.toNat) := by
  apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_mul, BitVec.toNat_ofNat]

theorem and_low (x : BitVec 64) : x &&& 0xffffffff = BitVec.ofNat 64 (lo x).toNat := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, lo_toNat,
    show (0xffffffff : BitVec 64).toNat = 2 ^ 32 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide))]

theorem addMul_eq (a b : BitVec 64) :
    a + (BitVec.ofNat 64 ((lo a).toNat * (lo b).toNat) + BitVec.ofNat 64 ((lo a).toNat * (lo b).toNat)) + b =
      Spec.Argon2.addMul a b := by
  have hp : BitVec.ofNat 64 ((lo a).toNat * (lo b).toNat) = (a &&& 0xffffffff) * (b &&& 0xffffffff) := by
    rw [and_low, and_low, BitVec.ofNat_mul]
  rw [hp, Spec.Argon2.addMul, BitVec.mul_assoc]
  generalize (a &&& 0xffffffff) * (b &&& 0xffffffff) = x
  have two : (2 : BitVec 64) * x = x + x := by bv_omega
  rw [two]
  ac_rfl

theorem addMul_ok {al ah bl bh t0 t1 t2 t3 t4 : Reg} {rest : List Instr} {s : State} {Q : State → Prop}
    {a b : BitVec 64} (hd : [al, ah, bl, bh, t0, t1, t2, t3, t4].Nodup)
    (pa : Pair s al ah a) (pb : Pair s bl bh b)
    (k : ∀ s', Only [al, ah, t0, t1, t2, t3, t4] s s' → Pair s' al ah (Spec.Argon2.addMul a b) →
      WP isa (.block rest) s' Q) :
    WP isa (.block (addMul al ah bl bh t0 t1 t2 t3 t4 ++ rest)) s Q := by
  have hd' := hd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil,
    and_true] at hd'
  obtain ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8⟩, ⟨b2, b3, b4, b5, b6, b7, b8⟩, ⟨c3, c4, c5, c6, c7, c8⟩,
    ⟨d4, d5, d6, d7, d8⟩, ⟨e5, e6, e7, e8⟩, ⟨f6, f7, f8⟩, ⟨g7, g8⟩, h8⟩ := hd'
  have ht : [t0, t1, t2, t3, t4].Nodup := (List.nodup_cons.mp (List.nodup_cons.mp
    (List.nodup_cons.mp (List.nodup_cons.mp hd).2).2).2).2
  unfold addMul
  simp only [List.append_assoc, List.cons_append]
  refine mulHi_ok ht (by simp [a4, a5, a6, a7, a8]) (by simp [c4, c5, c6, c7, c8]) fun s₁ o₁ v₁ => ?_
  have pa₁ := pa.of_only o₁ (by simp [a4, a5, a6, a7, a8]) (by simp [b4, b5, b6, b7, b8])
  have pb₁ := pb.of_only o₁ (by simp [c4, c5, c6, c7, c8]) (by simp [d4, d5, d6, d7, d8])
  refine wp_mul fun s₂ u₂ => ?_
  have pp : Pair s₂ t0 t2 (BitVec.ofNat 64 ((lo a).toNat * (lo b).toNat)) := by
    refine ⟨?_, ?_⟩
    · rw [u₂.gpr, pa₁.1, pb₁.1, lo_ofNat, mul_ofNat]
    · rw [u₂.other _ (Ne.symm e6), v₁, mulHiV_eq, hi_ofNat (mul_lt _ _), pa.1, pb.1]
  refine wp_add64 e6 e6 pp pp fun s₃ o₃ p₃ => ?_
  have O₃ := (Only.of_upd u₂).trans o₃
  refine wp_add64 a1 a6 (pa₁.of_only O₃ (by simp [a4, a6]) (by simp [b4, b6])) p₃ fun s₄ o₄ p₄ => ?_
  refine wp_add64 a1 a3 p₄ (pb₁.of_only (O₃.trans o₄) (by simp [c4, c6, Ne.symm a2, Ne.symm b2])
    (by simp [d4, d6, Ne.symm a3, Ne.symm b3])) fun s₅ o₅ p₅ => ?_
  refine k s₅ ((((o₁.trans (Only.of_upd u₂)).trans o₃).trans o₄).trans o₅ |>.mono (by simp)) ?_
  rwa [addMul_eq] at p₅

end VG.Proof.Argon2.Arm
