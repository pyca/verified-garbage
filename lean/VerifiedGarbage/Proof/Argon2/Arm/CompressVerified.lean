import VerifiedGarbage.Proof.Blake2.Arm.Blake2b
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Argon2.PermuteRows
import VerifiedGarbage.Impl.Argon2.Arm.Compress
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Spec.Argon2.Contract
import VerifiedGarbage.Proof.Framework.Arm.Spill
import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.Arm.Mix`. -/
section

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
variable {is : List Instr} {s : VG.Arm.State} {Q : VG.Arm.State → Prop}

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

theorem mulHiV_eq (x y : BitVec 32) : VG.Proof.Argon2.Arm.mulHiV x y = BitVec.ofNat 32 (x.toNat * y.toNat / 2 ^ 32) := by
  have hx := x.isLt
  have hy := y.isLt
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat]
  simp only [VG.Proof.Argon2.Arm.mulHiV]
  have ex0 := VG.Proof.Argon2.Arm.toNat_lo16 x
  have ey0 := VG.Proof.Argon2.Arm.toNat_lo16 y
  have ex1 := VG.Proof.Argon2.Arm.toNat_hi16 x
  have ey1 := VG.Proof.Argon2.Arm.toNat_hi16 y
  have bx0 : (x <<< 16 >>> 16).toNat < 2 ^ 16 := by rw [ex0]; omega
  have by0 : (y <<< 16 >>> 16).toNat < 2 ^ 16 := by rw [ey0]; omega
  have bx1 : (x >>> 16).toNat < 2 ^ 16 := by rw [ex1]; omega
  have by1 : (y >>> 16).toNat < 2 ^ 16 := by rw [ey1]; omega
  have e00 := VG.Proof.Argon2.Arm.toNat_mul16 bx0 by0
  have e01 := VG.Proof.Argon2.Arm.toNat_mul16 bx0 by1
  have e10 := VG.Proof.Argon2.Arm.toNat_mul16 bx1 by0
  have e11 := VG.Proof.Argon2.Arm.toNat_mul16 bx1 by1
  have l00 := VG.Proof.Argon2.Arm.mul16_le bx0 by0
  have l01 := VG.Proof.Argon2.Arm.mul16_le bx0 by1
  have l10 := VG.Proof.Argon2.Arm.mul16_le bx1 by0
  have l11 := VG.Proof.Argon2.Arm.mul16_le bx1 by1
  have split := VG.Proof.Argon2.Arm.mul_split x.toNat y.toNat
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
  have q01 := VG.Proof.Argon2.Arm.toNat_lo16 p01
  have q10 := VG.Proof.Argon2.Arm.toNat_lo16 p10
  have r00 := VG.Proof.Argon2.Arm.toNat_hi16 p00
  have r01 := VG.Proof.Argon2.Arm.toNat_hi16 p01
  have r10 := VG.Proof.Argon2.Arm.toNat_hi16 p10
  have m1 : ((p01 <<< 16 >>> 16) + (p00 >>> 16)).toNat = p01.toNat % 2 ^ 16 + p00.toNat / 2 ^ 16 := by
    rw [VG.Proof.Argon2.Arm.toNat_add_lt (by rw [q01, r00]; omega), q01, r00]
  have m2 : ((p01 <<< 16 >>> 16) + (p00 >>> 16) + (p10 <<< 16 >>> 16)).toNat =
      p01.toNat % 2 ^ 16 + p00.toNat / 2 ^ 16 + p10.toNat % 2 ^ 16 := by
    rw [VG.Proof.Argon2.Arm.toNat_add_lt (by rw [m1, q10]; omega), m1, q10]
  generalize (p01 <<< 16 >>> 16) + (p00 >>> 16) + (p10 <<< 16 >>> 16) = m at m2 ⊢
  have rm := VG.Proof.Argon2.Arm.toNat_hi16 m
  have a1 : (p11 + (p01 >>> 16)).toNat = p11.toNat + p01.toNat / 2 ^ 16 := by
    rw [VG.Proof.Argon2.Arm.toNat_add_lt (by rw [r01]; omega), r01]
  have a2 : (p11 + (p01 >>> 16) + (p10 >>> 16)).toNat = p11.toNat + p01.toNat / 2 ^ 16 + p10.toNat / 2 ^ 16 := by
    rw [VG.Proof.Argon2.Arm.toNat_add_lt (by rw [a1, r10]; omega), a1, r10]
  rw [VG.Proof.Argon2.Arm.toNat_add_lt (by rw [a2, rm, m2]; omega), a2, rm, m2]
  generalize x.toNat * y.toNat = P at split ⊢
  omega

/-- Two distinct registers, from the hypotheses, in either order. -/
macro "ne" : tactic => `(tactic| first | with_reducible assumption | exact Ne.symm (by with_reducible assumption))

theorem mulHi_ok {x y t0 t1 t2 t3 t4 : Reg} {rest : List Instr} {s : VG.Arm.State} {Q : VG.Arm.State → Prop}
    (hd : [t0, t1, t2, t3, t4].Nodup) (hx : x ∉ [t0, t1, t2, t3, t4]) (hy : y ∉ [t0, t1, t2, t3, t4])
    (k : ∀ s', Only [t0, t1, t2, t3, t4] s s' → s'.gpr t2 = VG.Proof.Argon2.Arm.mulHiV (s.gpr x) (s.gpr y) →
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
  refine VG.Proof.Argon2.Arm.wp_mul fun s₇ u₇ => VG.Proof.Argon2.Arm.wp_mul fun s₈ u₈ => VG.Proof.Argon2.Arm.wp_mul fun s₉ u₉ => VG.Proof.Argon2.Arm.wp_mul fun s₁₀ u₁₀ => ?_
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
    rw [VG.Proof.Argon2.Arm.and_low, VG.Proof.Argon2.Arm.and_low, BitVec.ofNat_mul]
  rw [hp, Spec.Argon2.addMul, BitVec.mul_assoc]
  generalize (a &&& 0xffffffff) * (b &&& 0xffffffff) = x
  have two : (2 : BitVec 64) * x = x + x := by bv_omega
  rw [two]
  ac_rfl

theorem addMul_ok {al ah bl bh t0 t1 t2 t3 t4 : Reg} {rest : List Instr} {s : VG.Arm.State} {Q : VG.Arm.State → Prop}
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
  refine VG.Proof.Argon2.Arm.mulHi_ok ht (by simp [a4, a5, a6, a7, a8]) (by simp [c4, c5, c6, c7, c8]) fun s₁ o₁ v₁ => ?_
  have pa₁ := pa.of_only o₁ (by simp [a4, a5, a6, a7, a8]) (by simp [b4, b5, b6, b7, b8])
  have pb₁ := pb.of_only o₁ (by simp [c4, c5, c6, c7, c8]) (by simp [d4, d5, d6, d7, d8])
  refine VG.Proof.Argon2.Arm.wp_mul fun s₂ u₂ => ?_
  have pp : Pair s₂ t0 t2 (BitVec.ofNat 64 ((lo a).toNat * (lo b).toNat)) := by
    refine ⟨?_, ?_⟩
    · rw [u₂.gpr, pa₁.1, pb₁.1, VG.Proof.Argon2.Arm.lo_ofNat, VG.Proof.Argon2.Arm.mul_ofNat]
    · rw [u₂.other _ (Ne.symm e6), v₁, VG.Proof.Argon2.Arm.mulHiV_eq, VG.Proof.Argon2.Arm.hi_ofNat (VG.Proof.Argon2.Arm.mul_lt _ _), pa.1, pb.1]
  refine wp_add64 e6 e6 pp pp fun s₃ o₃ p₃ => ?_
  have O₃ := (Only.of_upd u₂).trans o₃
  refine wp_add64 a1 a6 (pa₁.of_only O₃ (by simp [a4, a6]) (by simp [b4, b6])) p₃ fun s₄ o₄ p₄ => ?_
  refine wp_add64 a1 a3 p₄ (pb₁.of_only (O₃.trans o₄) (by simp [c4, c6, Ne.symm a2, Ne.symm b2])
    (by simp [d4, d6, Ne.symm a3, Ne.symm b3])) fun s₅ o₅ p₅ => ?_
  refine k s₅ ((((o₁.trans (Only.of_upd u₂)).trans o₃).trans o₄).trans o₅ |>.mono (by simp)) ?_
  rwa [VG.Proof.Argon2.Arm.addMul_eq] at p₅

end VG.Proof.Argon2.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.Arm.Gb`. -/
section

/-!
# Argon2 on ARMv7: GB on the permuted block

`wp_gb`: GB on the words at `[r3, #a]`, …, `[r3, #d]` stores the words of
`Proof.Argon2.mix` (`gbMem`), with the registers of `gbRegs` written. The
permuted block in `scratch[1024, 2048)` as a vector of words (`working`), and
`gbAt_ok`: one GB updates it as `Proof.Argon2.mixWords`, and writes nothing
else.
-/

namespace VG.Proof.Argon2.Arm

open VG VG.Arm VG.Spec.Argon2
open VG.Impl.Sha512.Arm (lo hi ld st)
open VG.Impl.Blake2.Arm.B (xor64 rotr rotr')
open VG.Impl.Argon2.Arm (gb gbAt wOff)
open VG.Proof.Sha512.Arm (Only Pair rd64 write64 A Reg64 Wrote wp_st mem_rd rd64_write64_self
  rd64_write64_ne frame_write64)
open VG.Proof.Blake2.ArmB (wp_ld64 wp_xor64 wp_rotr wp_rotr' pair_swap)

/-- The registers GB writes. -/
def gbRegs : List Reg := [.r0, .r1, .r2, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr]

/-- The memory after GB on the words at `V + a`, …, `V + d`. -/
def gbMem (m : Mem) (V : BitVec 32) (a b c d : Nat) : Mem :=
  let r := Proof.Argon2.mix (rd64 m V a) (rd64 m V b) (rd64 m V c) (rd64 m V d)
  write64 (write64 (write64 (write64 m V a r.1) V b r.2.1) V c r.2.2.1) V d r.2.2.2

section
variable {rest : List Instr} {s : VG.Arm.State} {Q : VG.Arm.State → Prop}

theorem wp_gb {a b c d : Nat} {V : BitVec 32} {N : Nat} (hN : N ≤ 4092)
    (ha : a + 8 ≤ N) (hb : b + 8 ≤ N) (hc : c + 8 ≤ N) (hd : d + 8 ≤ N)
    (hRV : Reg64 s.wr V N) (h3 : s.gpr .r3 = V)
    (K : ∀ s', Wrote VG.Proof.Argon2.Arm.gbRegs s s' (VG.Proof.Argon2.Arm.gbMem s.mem V a b c d) → WP isa (.block rest) s' Q) :
    WP isa (.block (gb a b c d ++ rest)) s Q := by
  unfold gb
  simp only [List.append_assoc]
  have iV : ∀ o, o + 8 ≤ N → InRegions (s.rd ++ s.wr) (A V o) 4 ∧
      InRegions (s.rd ++ s.wr) (A V (o + 4)) 4 := fun o ho => ⟨mem_rd (hRV o ho).1, mem_rd (hRV o ho).2⟩
  -- Load the four words.
  refine wp_ld64 (by decide) (by decide) (by omega) h3 rfl (iV a ha).1 (iV a ha).2
    fun s₁ o₁ pa => ?_
  refine wp_ld64 (by decide) (by decide) (by omega) (by rw [o₁.gpr _ (by decide), h3]) o₁.mem
    (by rw [o₁.rd, o₁.wr]; exact (iV b hb).1) (by rw [o₁.rd, o₁.wr]; exact (iV b hb).2)
    fun s₂ o₂ pb => ?_
  have O₂ := o₁.trans o₂
  refine wp_ld64 (by decide) (by decide) (by omega) (by rw [O₂.gpr _ (by decide), h3]) O₂.mem
    (by rw [O₂.rd, O₂.wr]; exact (iV c hc).1) (by rw [O₂.rd, O₂.wr]; exact (iV c hc).2)
    fun s₃ o₃ pc => ?_
  have O₃ := O₂.trans o₃
  refine wp_ld64 (by decide) (by decide) (by omega) (by rw [O₃.gpr _ (by decide), h3]) O₃.mem
    (by rw [O₃.rd, O₃.wr]; exact (iV d hd).1) (by rw [O₃.rd, O₃.wr]; exact (iV d hd).2)
    fun s₄ o₄ pd => ?_
  have O₄ := O₃.trans o₄
  -- a := addMul(a, b)
  refine VG.Proof.Argon2.Arm.addMul_ok (by decide) (pa.of_only ((o₂.trans o₃).trans o₄) (by decide) (by decide))
    (pb.of_only (o₃.trans o₄) (by decide) (by decide)) fun s₅ o₅ pa₁ => ?_
  -- d := (d ⊕ a) >>> 32
  refine wp_xor64 (by decide) (by decide) (pd.of_only o₅ (by decide) (by decide)) pa₁
    fun s₆ o₆ p₆ => ?_
  have pd₁ := pair_swap p₆
  -- c := addMul(c, d)
  refine VG.Proof.Argon2.Arm.addMul_ok (by decide) (pc.of_only ((o₄.trans o₅).trans o₆) (by decide) (by decide)) pd₁
    fun s₇ o₇ pc₁ => ?_
  -- b := (b ⊕ c) >>> 24
  refine wp_xor64 (by decide) (by decide)
    (pb.of_only ((((o₃.trans o₄).trans o₅).trans o₆).trans o₇) (by decide) (by decide)) pc₁
    fun s₈ o₈ p₈ => ?_
  refine wp_rotr (n := 24) (by decide) (by decide) (by decide) (by decide) (by decide) p₈
    fun s₉ o₉ pb₁ => ?_
  -- a := addMul(a, b)
  refine VG.Proof.Argon2.Arm.addMul_ok (by decide) (pa₁.of_only ((((o₆.trans o₇).trans o₈).trans o₉)) (by decide) (by decide))
    pb₁ fun s₁₀ o₁₀ pa₂ => ?_
  -- d := (d ⊕ a) >>> 16
  refine wp_xor64 (by decide) (by decide)
    (pd₁.of_only ((((o₇.trans o₈).trans o₉).trans o₁₀)) (by decide) (by decide)) pa₂
    fun s₁₁ o₁₁ p₁₁ => ?_
  refine wp_rotr (n := 16) (by decide) (by decide) (by decide) (by decide) (by decide) p₁₁
    fun s₁₂ o₁₂ pd₂ => ?_
  -- c := addMul(c, d)
  refine VG.Proof.Argon2.Arm.addMul_ok (by decide)
    (pc₁.of_only (((((o₈.trans o₉).trans o₁₀).trans o₁₁).trans o₁₂)) (by decide) (by decide)) pd₂
    fun s₁₃ o₁₃ pc₂ => ?_
  -- b := (b ⊕ c) >>> 63
  refine wp_xor64 (by decide) (by decide)
    (pb₁.of_only ((((o₁₀.trans o₁₁).trans o₁₂).trans o₁₃)) (by decide) (by decide)) pc₂
    fun s₁₄ o₁₄ p₁₄ => ?_
  refine wp_rotr' (n := 63) (by decide) (by decide) (by decide) (by decide) (by decide) p₁₄
    fun s₁₅ o₁₅ pb₂ => ?_
  have O₁₅ := ((((((((((O₄.trans o₅).trans o₆).trans o₇).trans o₈).trans o₉).trans o₁₀).trans
    o₁₁).trans o₁₂).trans o₁₃).trans o₁₄).trans o₁₅
  have pa₂' := pa₂.of_only ((((o₁₁.trans o₁₂).trans o₁₃).trans o₁₄).trans o₁₅) (by decide) (by decide)
  have pc₂' := pc₂.of_only (o₁₄.trans o₁₅) (by decide) (by decide)
  have pd₂' := pd₂.of_only ((o₁₃.trans o₁₄).trans o₁₅) (by decide) (by decide)
  -- Store them.
  have w : Reg64 s₁₅.wr V N := by rw [O₁₅.wr]; exact hRV
  have r3 : s₁₅.gpr .r3 = V := by rw [O₁₅.gpr _ (by decide), h3]
  refine wp_st (by omega) r3 pa₂' (w a ha).1 (w a ha).2 fun s₁₆ u₁₆ => ?_
  refine wp_st (by omega) (by rw [u₁₆.gpr, r3]) (by rw [Pair, u₁₆.gpr]; exact pb₂)
    (by rw [u₁₆.wr]; exact (w b hb).1) (by rw [u₁₆.wr]; exact (w b hb).2) fun s₁₇ u₁₇ => ?_
  refine wp_st (by omega) (by rw [u₁₇.gpr, u₁₆.gpr, r3]) (by rw [Pair, u₁₇.gpr, u₁₆.gpr]; exact pc₂')
    (by rw [u₁₇.wr, u₁₆.wr]; exact (w c hc).1) (by rw [u₁₇.wr, u₁₆.wr]; exact (w c hc).2)
    fun s₁₈ u₁₈ => ?_
  refine wp_st (by omega) (by rw [u₁₈.gpr, u₁₇.gpr, u₁₆.gpr, r3])
    (by rw [Pair, u₁₈.gpr, u₁₇.gpr, u₁₆.gpr]; exact pd₂')
    (by rw [u₁₈.wr, u₁₇.wr, u₁₆.wr]; exact (w d hd).1)
    (by rw [u₁₈.wr, u₁₇.wr, u₁₆.wr]; exact (w d hd).2) fun s₁₉ u₁₉ => K s₁₉ ⟨fun r hr => ?_, ?_,
      by rw [u₁₉.rd, u₁₈.rd, u₁₇.rd, u₁₆.rd, O₁₅.rd], by rw [u₁₉.wr, u₁₈.wr, u₁₇.wr, u₁₆.wr, O₁₅.wr],
      by rw [u₁₉.sp, u₁₈.sp, u₁₇.sp, u₁₆.sp, O₁₅.sp]⟩
  · rw [u₁₉.gpr, u₁₈.gpr, u₁₇.gpr, u₁₆.gpr]
    exact (O₁₅.mono (by decide)).gpr r hr
  · rw [u₁₉.mem, u₁₈.mem, u₁₇.mem, u₁₆.mem, O₁₅.mem]
    rfl

end

/-! ## The permuted block -/

/-- The permuted block, at `B + 1024`. -/
def working (m : Mem) (B : BitVec 32) : VG.Spec.Argon2.Block := Vector.ofFn fun i => rd64 m B (wOff i.val)

theorem working_get (m : Mem) (B : BitVec 32) (i : Fin 128) :
    (VG.Proof.Argon2.Arm.working m B)[i] = rd64 m B (wOff i.val) := by
  simp only [VG.Proof.Argon2.Arm.working, Fin.getElem_fin, Vector.getElem_ofFn]

/-- The permuted block's region. -/
abbrev permR (B : BitVec 32) : Region := ⟨State.addr B + BitVec.ofNat 64 1024, 1024⟩

theorem wOff_lt (i : Fin 128) : wOff i.val + 8 ≤ 2048 := by have := i.isLt; simp only [wOff]; omega

section
variable {B : BitVec 32} (hfit : B.toNat + 4096 ≤ 2 ^ 32)
include hfit

theorem working_write (m : Mem) (i : Fin 128) (v : VG.Spec.Argon2.Word) :
    VG.Proof.Argon2.Arm.working (write64 m B (wOff i.val) v) B = (VG.Proof.Argon2.Arm.working m B).set i v := by
  apply Vector.ext
  intro j hj
  simp only [VG.Proof.Argon2.Arm.working, Vector.getElem_ofFn, Vector.getElem_set]
  by_cases h : i.val = j
  · subst j
    simp only [ite_true]
    exact rd64_write64_self m v (by have := VG.Proof.Argon2.Arm.wOff_lt i; omega)
  · simp only [h, ite_false]
    exact rd64_write64_ne m v (by have := VG.Proof.Argon2.Arm.wOff_lt i; omega) (by simp only [wOff]; omega)
      (by simp only [wOff]; omega)

/-- A write to a word of the permuted block stays in its region. -/
theorem frame_write (m m' : Mem) (hf : Frame [VG.Proof.Argon2.Arm.permR B] m m') (i : Fin 128) (v : VG.Spec.Argon2.Word) :
    Frame [VG.Proof.Argon2.Arm.permR B] m (write64 m' B (wOff i.val) v) := by
  have c : ∀ e, e + 4 ≤ 1024 → (VG.Proof.Argon2.Arm.permR B).Contains (A B (1024 + e)) 4 := fun e he => by
    rw [VG.Proof.Sha512.Arm.A_eq (by omega), ← Offset.add_ofNat_add_ofNat]
    exact Offset.contains_base _ he (by omega)
  have m₁ := List.mem_singleton_self (VG.Proof.Argon2.Arm.permR B)
  have := i.isLt
  simp only [write64]
  exact (hf.writeW m₁ _ (c (8 * i.val) (by omega))).writeW m₁ _
    (by rw [show wOff i.val + 4 = 1024 + (8 * i.val + 4) by simp only [wOff]; omega]
        exact c _ (by omega))

end

/-! ## GB -/

/-- `s'` is `s` but for the registers GB writes and memory. -/
structure Keep (s s' : VG.Arm.State) : Prop where
  gpr : ∀ r, r ∉ VG.Proof.Argon2.Arm.gbRegs → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem Keep.refl (s : VG.Arm.State) : VG.Proof.Argon2.Arm.Keep s s := ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem Keep.trans {s s₁ s₂ : VG.Arm.State} (k₁ : VG.Proof.Argon2.Arm.Keep s s₁) (k₂ : VG.Proof.Argon2.Arm.Keep s₁ s₂) : VG.Proof.Argon2.Arm.Keep s s₂ :=
  ⟨fun r hr => by rw [k₂.gpr r hr, k₁.gpr r hr], k₂.rd.trans k₁.rd, k₂.wr.trans k₁.wr, k₂.sp.trans k₁.sp⟩

theorem Keep.r3 {s s' : VG.Arm.State} (k : VG.Proof.Argon2.Arm.Keep s s') : s'.gpr .r3 = s.gpr .r3 := k.gpr _ (by decide)

/-- What a step of GB leaves: the registers but GB's, and the memory at `B`
with the permuted block `v` in place of the old one, `Frame [permR B]`. -/
structure Step (B : BitVec 32) (s : VG.Arm.State) (v : VG.Spec.Argon2.Block) (t : VG.Arm.State) : Prop where
  keep : VG.Proof.Argon2.Arm.Keep s t
  working : VG.Proof.Argon2.Arm.working t.mem B = v
  frame : Frame [VG.Proof.Argon2.Arm.permR B] s.mem t.mem

theorem Step.trans {B : BitVec 32} {s t u : VG.Arm.State} {v w : VG.Spec.Argon2.Block} (h : VG.Proof.Argon2.Arm.Step B s v t) (h' : VG.Proof.Argon2.Arm.Step B t w u) :
    VG.Proof.Argon2.Arm.Step B s w u := ⟨h.keep.trans h'.keep, h'.working, h.frame.trans h'.frame⟩

theorem gbAt_ok {B : BitVec 32} (hfit : B.toNat + 4096 ≤ 2 ^ 32) {s : VG.Arm.State} (h3 : s.gpr .r3 = B)
    (hA : Reg64 s.wr B 2048) (a b c d : Fin 128) :
    WP isa (gbAt a.val b.val c.val d.val) s
      (VG.Proof.Argon2.Arm.Step B s (Proof.Argon2.mixWords (VG.Proof.Argon2.Arm.working s.mem B) a b c d)) := by
  unfold gbAt
  rw [← List.append_nil (gb _ _ _ _)]
  refine VG.Proof.Argon2.Arm.wp_gb (N := 2048) (by decide) (VG.Proof.Argon2.Arm.wOff_lt a) (VG.Proof.Argon2.Arm.wOff_lt b) (VG.Proof.Argon2.Arm.wOff_lt c) (VG.Proof.Argon2.Arm.wOff_lt d) hA h3
    fun t w => WP.block_nil ⟨⟨w.gpr, w.rd, w.wr, w.sp⟩, ?_, ?_⟩
  · rw [w.mem, VG.Proof.Argon2.Arm.gbMem]
    simp only [VG.Proof.Argon2.Arm.working_write hfit, ← VG.Proof.Argon2.Arm.working_get]
    rfl
  · rw [w.mem, VG.Proof.Argon2.Arm.gbMem]
    exact VG.Proof.Argon2.Arm.frame_write hfit _ _ (VG.Proof.Argon2.Arm.frame_write hfit _ _ (VG.Proof.Argon2.Arm.frame_write hfit _ _ (VG.Proof.Argon2.Arm.frame_write hfit _ _
      (Frame.refl _ _) _ _) _ _) _ _) _ _

end VG.Proof.Argon2.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.Arm.Rounds`. -/
section

/-!
# Argon2 on ARMv7: the row and column permutations

As on x86 (`Proof/Argon2/X86/Rounds.lean`): P on any injectively selected
row or column (`permuteAt_ok`), and the rows and columns (`rounds_ok`).
-/

namespace VG.Proof.Argon2.Arm

open VG VG.Arm VG.Spec.Argon2
open VG.Proof.Argon2
open VG.Proof.Sha512.Arm (Reg64)

/-- The selected sixteen words and the unchanged words outside them. -/
def Holds (index : Fin 16 → Fin 128) (b : VG.Spec.Argon2.Block) (v : Vector VG.Spec.Argon2.Word 16) (m : Mem)
    (B : BitVec 32) : Prop :=
  gather index (VG.Proof.Argon2.Arm.working m B) = v ∧ ∀ k : Fin 128, (∀ j, index j ≠ k) → (VG.Proof.Argon2.Arm.working m B)[k] = b[k]

/-- The base and the permissions of `scratch`. -/
def At (B : BitVec 32) (s : VG.Arm.State) : Prop := s.gpr .r3 = B ∧ Reg64 s.wr B 2048

theorem At.of_step {B : BitVec 32} {s t : VG.Arm.State} {v : VG.Spec.Argon2.Block} (h : VG.Proof.Argon2.Arm.At B s) (st : VG.Proof.Argon2.Arm.Step B s v t) : VG.Proof.Argon2.Arm.At B t :=
  ⟨st.keep.r3.trans h.1, st.keep.wr ▸ h.2⟩

section
variable {B : BitVec 32} (hfit : B.toNat + 4096 ≤ 2 ^ 32)

include hfit

/-- One GB advances the selected row or column and preserves its complement. -/
theorem step_ok (index : Fin 16 → Fin 128) (hi : Function.Injective index) {s : VG.Arm.State}
    (hs : VG.Proof.Argon2.Arm.At B s) (base : VG.Spec.Argon2.Block) (v : Vector VG.Spec.Argon2.Word 16) (hv : VG.Proof.Argon2.Arm.Holds index base v s.mem B)
    (a b c d : Fin 16) (hab : a.val ≠ b.val) (hac : a.val ≠ c.val) (had : a.val ≠ d.val)
    (hbc : b.val ≠ c.val) (hbd : b.val ≠ d.val) (hcd : c.val ≠ d.val) :
    WP isa (Impl.Argon2.Arm.gbAt (index a).val (index b).val (index c).val (index d).val) s
      fun t => VG.Proof.Argon2.Arm.Holds index base (GB v a b c d) t.mem B ∧ ∃ w, VG.Proof.Argon2.Arm.Step B s w t := by
  refine (VG.Proof.Argon2.Arm.gbAt_ok hfit hs.1 hs.2 (index a) (index b) (index c) (index d)).mono fun t st => ?_
  refine ⟨⟨?_, ?_⟩, _, st⟩
  · rw [st.working, gather_mixWords index hi, hv.1, GB_eq_mixWords v hab hac had hbc hbd hcd]
  · intro k hn
    rw [st.working]
    have ne' (j : Fin 16) : (index j).val ≠ k.val := fun h => hn j (Fin.ext h)
    simp only [mixWords, Fin.getElem_fin, Vector.getElem_set, ne', ite_false]
    exact hv.2 k hn

/-- P on any injectively selected row or column. -/
theorem permuteAt_holds (index : Fin 16 → Fin 128) (hi : Function.Injective index) {s : VG.Arm.State}
    (hs : VG.Proof.Argon2.Arm.At B s) (base : VG.Spec.Argon2.Block) (v : Vector VG.Spec.Argon2.Word 16) (hv : VG.Proof.Argon2.Arm.Holds index base v s.mem B) :
    WP isa (Impl.Argon2.Arm.permuteAt index) s fun t =>
      VG.Proof.Argon2.Arm.Holds index base (permute v) t.mem B ∧ ∃ w, VG.Proof.Argon2.Arm.Step B s w t := by
  have advance (t : VG.Arm.State) (v' : Vector VG.Spec.Argon2.Word 16)
      (h : VG.Proof.Argon2.Arm.Holds index base v' t.mem B ∧ ∃ w, VG.Proof.Argon2.Arm.Step B s w t)
      (a b c d : Fin 16)
      (hab : a.val ≠ b.val) (hac : a.val ≠ c.val) (had : a.val ≠ d.val)
      (hbc : b.val ≠ c.val) (hbd : b.val ≠ d.val) (hcd : c.val ≠ d.val) :
      WP isa (Impl.Argon2.Arm.gbAt (index a).val (index b).val (index c).val (index d).val)
        t fun u => VG.Proof.Argon2.Arm.Holds index base (GB v' a b c d) u.mem B ∧ ∃ w, VG.Proof.Argon2.Arm.Step B s w u := by
    obtain ⟨hh, w, st⟩ := h
    refine (VG.Proof.Argon2.Arm.step_ok hfit index hi (hs.of_step st) base v' hh a b c d
      hab hac had hbc hbd hcd).mono ?_
    rintro u ⟨hu, w', st'⟩
    exact ⟨hu, w', st.trans st'⟩
  unfold Impl.Argon2.Arm.permuteAt
  apply WP.seq
  refine (advance s _ ⟨hv, _, ⟨.refl s, rfl, Frame.refl _ _⟩⟩ 0 4 8 12
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).mono ?_
  intro s1 h1
  apply WP.seq
  refine (advance s1 _ h1 1 5 9 13
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).mono ?_
  intro s2 h2
  apply WP.seq
  refine (advance s2 _ h2 2 6 10 14
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).mono ?_
  intro s3 h3
  apply WP.seq
  refine (advance s3 _ h3 3 7 11 15
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).mono ?_
  intro s4 h4
  apply WP.seq
  refine (advance s4 _ h4 0 5 10 15
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).mono ?_
  intro s5 h5
  apply WP.seq
  refine (advance s5 _ h5 1 6 11 12
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).mono ?_
  intro s6 h6
  apply WP.seq
  refine (advance s6 _ h6 2 7 8 13
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).mono ?_
  intro s7 h7
  exact advance s7 _ h7 3 4 9 14
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The row/column code meets the specification's gather, P, scatter definition. -/
theorem permuteAt_ok (index : Fin 16 → Fin 128) (hi : Function.Injective index) {s : VG.Arm.State}
    (hs : VG.Proof.Argon2.Arm.At B s) :
    WP isa (Impl.Argon2.Arm.permuteAt index) s
      (VG.Proof.Argon2.Arm.Step B s (Spec.Argon2.permuteAt index (VG.Proof.Argon2.Arm.working s.mem B))) := by
  refine (VG.Proof.Argon2.Arm.permuteAt_holds hfit index hi hs (VG.Proof.Argon2.Arm.working s.mem B)
    (gather index (VG.Proof.Argon2.Arm.working s.mem B)) ⟨rfl, fun _ _ => rfl⟩).mono ?_
  rintro t ⟨ht, w, st⟩
  exact ⟨st.keep, eq_scatter index hi _ _ _ ht.1 ht.2, st.frame⟩

/-- A list of row or column permutations. -/
theorem rounds_ok (index : Fin 8 → Fin 16 → Fin 128)
    (hi : ∀ i, Function.Injective (index i)) (is : List (Fin 8)) {s : VG.Arm.State} (hs : VG.Proof.Argon2.Arm.At B s) :
    WP isa (is.foldr (fun i rest => .seq (Impl.Argon2.Arm.permuteAt (index i)) rest)
      (.block [])) s
      (VG.Proof.Argon2.Arm.Step B s (is.foldl (fun b i => Spec.Argon2.permuteAt (index i) b) (VG.Proof.Argon2.Arm.working s.mem B))) := by
  induction is generalizing s with
  | nil => exact WP.block_nil ⟨.refl s, rfl, Frame.refl _ _⟩
  | cons i is ih =>
    apply WP.seq
    refine (VG.Proof.Argon2.Arm.permuteAt_ok hfit (index i) (hi i) hs).mono ?_
    intro t st
    refine (ih (hs.of_step st)).mono ?_
    intro u st'
    refine st.trans ?_
    rw [List.foldl_cons, ← st.working]
    exact st'

end

end VG.Proof.Argon2.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.Arm.Words`. -/
section

/-!
# Argon2 on ARMv7: blocks as 32-bit words

A block at `B + o` (`blk m B o`) as 64-bit words, each the pair of 32-bit words
the code copies: `blk_of_words` builds it from them, `blockAt_eq` relates it to
the contract's `Spec.Argon2.blockAt`, and `xor_words` XORs two blocks word by
word.
-/

namespace VG.Proof.Argon2.Arm

open VG VG.Arm VG.Spec.Argon2
open VG.Impl.Sha512.Arm (lo hi)
open VG.Proof.Sha512.Arm (rd64 A A_eq readW64 lo_xor hi_xor lo_append hi_append eq_of_lo_hi)

/-- The block at `B + o`, as pairs of 32-bit words. -/
def blk (m : Mem) (B : BitVec 32) (o : Nat) : VG.Spec.Argon2.Block := Vector.ofFn fun j => rd64 m B (o + 8 * j.val)

/-- The block made of the 32-bit words `f 0, f 1, …` (two per 64-bit word, the low one first). -/
def ofWords (f : Nat → BitVec 32) : VG.Spec.Argon2.Block := Vector.ofFn fun j => f (2 * j.val + 1) ++ f (2 * j.val)

theorem blk_of_words {m : Mem} {B : BitVec 32} {o : Nat} {f : Nat → BitVec 32}
    (h : ∀ i < 256, m.readW (A B (o + 4 * i)) 32 = f i) : VG.Proof.Argon2.Arm.blk m B o = VG.Proof.Argon2.Arm.ofWords f := by
  apply Vector.ext
  intro j hj
  simp only [VG.Proof.Argon2.Arm.blk, VG.Proof.Argon2.Arm.ofWords, Vector.getElem_ofFn, rd64]
  rw [show o + 8 * j + 4 = o + 4 * (2 * j + 1) by omega, show o + 8 * j = o + 4 * (2 * j) by omega,
    h _ (by omega), h _ (by omega)]

theorem working_eq (m : Mem) (B : BitVec 32) : VG.Proof.Argon2.Arm.working m B = VG.Proof.Argon2.Arm.blk m B 1024 := by
  apply Vector.ext
  intro j hj
  simp only [VG.Proof.Argon2.Arm.working, VG.Proof.Argon2.Arm.blk, Vector.getElem_ofFn, Impl.Argon2.Arm.wOff]

theorem blockAt_eq {m : Mem} {B : BitVec 32} (hfit : B.toNat + 1024 ≤ 2 ^ 32) :
    VG.Spec.Argon2.blockAt m (State.addr B) = VG.Proof.Argon2.Arm.blk m B 0 := by
  apply Vector.ext
  intro j hj
  simp only [VG.Spec.Argon2.blockAt, VG.Proof.Argon2.Arm.blk, Vector.getElem_ofFn, Nat.zero_add, rd64]
  rw [A_eq (by omega), A_eq (by omega), ← Offset.add_ofNat_add_ofNat _ _ 4,
    show BitVec.ofNat 64 4 = (4 : Addr) from rfl, ← readW64]
  simp only [Mem.readW, BitVec.setWidth_eq]

theorem append_xor (a b c d : BitVec 32) : (a ++ b) ^^^ (c ++ d) = (a ^^^ c) ++ (b ^^^ d) :=
  eq_of_lo_hi (by rw [lo_xor, lo_append, lo_append, lo_append])
    (by rw [hi_xor, hi_append, hi_append, hi_append])

theorem xor_words (f g : Nat → BitVec 32) :
    VG.Spec.Argon2.xorBlock (VG.Proof.Argon2.Arm.ofWords f) (VG.Proof.Argon2.Arm.ofWords g) = VG.Proof.Argon2.Arm.ofWords fun i => f i ^^^ g i := by
  apply Vector.ext
  intro j hj
  simp only [VG.Spec.Argon2.xorBlock, VG.Proof.Argon2.Arm.ofWords, Vector.getElem_zipWith, Vector.getElem_ofFn, VG.Proof.Argon2.Arm.append_xor]

/-- A prefix of `n` 32-bit words at `B + o` holds `f`. -/
def Words (m : Mem) (B : BitVec 32) (o : Nat) (f : Nat → BitVec 32) (n : Nat) : Prop :=
  ∀ i < n, m.readW (A B (o + 4 * i)) 32 = f i

end VG.Proof.Argon2.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.Arm.CompressContract`. -/
section

/-!
# Argon2 compression on ARMv7: the contract of the proof

`compressArm`: the contract the proof is written against (and the derivation
uses for its calls); `Spec.Argon2.compressContract` implies it
(`Proof/Argon2/Arm/CompressVerified.lean`). `Pre` names the facts of its
precondition.
-/

namespace VG.Proof.Argon2.Arm

open VG VG.Arm VG.Spec.Argon2
open VG.Proof.Sha512.Arm (A A_eq contains_A)

/-- `vg_argon2_compress(x = r0, y = r1, out = r2, scratch = r3)`: reads the two
input blocks, writes the output block and 4096 bytes of scratch. -/
def compressArm : Contract Arm.isa where
  pre s :=
    let x : Region := ⟨State.addr (s.gpr .r0), 1024⟩
    let y : Region := ⟨State.addr (s.gpr .r1), 1024⟩
    let out : Region := ⟨State.addr (s.gpr .r2), 1024⟩
    let scratch : Region := ⟨State.addr (s.gpr .r3), 4096⟩
    s.rd = [x, y] ∧ s.wr = [out, scratch] ∧
    out.Disjoint scratch ∧ x.Disjoint out ∧ x.Disjoint scratch ∧ y.Disjoint out ∧ y.Disjoint scratch ∧
    (s.gpr .r0).toNat + 1024 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 1024 ≤ 2 ^ 32 ∧
    (s.gpr .r2).toNat + 1024 ≤ 2 ^ 32 ∧ (s.gpr .r3).toNat + 4096 ≤ 2 ^ 32
  post s s' := VG.Spec.Argon2.blockAt s'.mem (State.addr (s.gpr .r2)) =
    compress (VG.Spec.Argon2.blockAt s.mem (State.addr (s.gpr .r0))) (VG.Spec.Argon2.blockAt s.mem (State.addr (s.gpr .r1)))
  pub s₁ s₂ := s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
    s₁.gpr .r3 = s₂.gpr .r3

section
variable (s₀ : VG.Arm.State)

abbrev xp : BitVec 32 := s₀.gpr .r0
abbrev yp : BitVec 32 := s₀.gpr .r1
abbrev op : BitVec 32 := s₀.gpr .r2
abbrev scr : BitVec 32 := s₀.gpr .r3
abbrev xR : Region := ⟨State.addr (VG.Proof.Argon2.Arm.xp s₀), 1024⟩
abbrev yR : Region := ⟨State.addr (VG.Proof.Argon2.Arm.yp s₀), 1024⟩
abbrev outR : Region := ⟨State.addr (VG.Proof.Argon2.Arm.op s₀), 1024⟩
abbrev scrR : Region := ⟨State.addr (VG.Proof.Argon2.Arm.scr s₀), 4096⟩

end

structure Pre (s₀ : VG.Arm.State) : Prop where
  rd : s₀.rd = [VG.Proof.Argon2.Arm.xR s₀, VG.Proof.Argon2.Arm.yR s₀]
  wr : s₀.wr = [VG.Proof.Argon2.Arm.outR s₀, VG.Proof.Argon2.Arm.scrR s₀]
  out_scr : (VG.Proof.Argon2.Arm.outR s₀).Disjoint (VG.Proof.Argon2.Arm.scrR s₀)
  x_out : (VG.Proof.Argon2.Arm.xR s₀).Disjoint (VG.Proof.Argon2.Arm.outR s₀)
  x_scr : (VG.Proof.Argon2.Arm.xR s₀).Disjoint (VG.Proof.Argon2.Arm.scrR s₀)
  y_out : (VG.Proof.Argon2.Arm.yR s₀).Disjoint (VG.Proof.Argon2.Arm.outR s₀)
  y_scr : (VG.Proof.Argon2.Arm.yR s₀).Disjoint (VG.Proof.Argon2.Arm.scrR s₀)
  x_fits : (VG.Proof.Argon2.Arm.xp s₀).toNat + 1024 ≤ 2 ^ 32
  y_fits : (VG.Proof.Argon2.Arm.yp s₀).toNat + 1024 ≤ 2 ^ 32
  out_fits : (VG.Proof.Argon2.Arm.op s₀).toNat + 1024 ≤ 2 ^ 32
  scr_fits : (VG.Proof.Argon2.Arm.scr s₀).toNat + 4096 ≤ 2 ^ 32

theorem pre_of (s₀ : VG.Arm.State) (h : compressArm.pre s₀) : VG.Proof.Argon2.Arm.Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

namespace Pre
variable {s₀ : VG.Arm.State} (hp : VG.Proof.Argon2.Arm.Pre s₀)
include hp

theorem scr_contains {d : Nat} (hd : d + 4 ≤ 4096) : (VG.Proof.Argon2.Arm.scrR s₀).Contains (A (VG.Proof.Argon2.Arm.scr s₀) d) 4 :=
  contains_A hp.scr_fits hd

theorem out_wr {s : VG.Arm.State} (hw : s.wr = s₀.wr) {d : Nat} (hd : d + 4 ≤ 1024) :
    InRegions s.wr (A (VG.Proof.Argon2.Arm.op s₀) d) 4 :=
  ⟨VG.Proof.Argon2.Arm.outR s₀, by simp [hw, hp.wr], contains_A hp.out_fits hd⟩

theorem scr_wr {s : VG.Arm.State} (hw : s.wr = s₀.wr) {d : Nat} (hd : d + 4 ≤ 4096) :
    InRegions s.wr (A (VG.Proof.Argon2.Arm.scr s₀) d) 4 :=
  ⟨VG.Proof.Argon2.Arm.scrR s₀, by simp [hw, hp.wr], contains_A hp.scr_fits hd⟩

theorem in_scr {s : VG.Arm.State} (hw : s.wr = s₀.wr) {d : Nat} (hd : d + 4 ≤ 4096) :
    InRegions (s.rd ++ s.wr) (A (VG.Proof.Argon2.Arm.scr s₀) d) 4 :=
  VG.Proof.Sha512.Arm.mem_rd (hp.scr_wr hw hd)

theorem in_x {s : VG.Arm.State} (hrd : s.rd = s₀.rd) {d : Nat} (hd : d + 4 ≤ 1024) :
    InRegions (s.rd ++ s.wr) (A (VG.Proof.Argon2.Arm.xp s₀) d) 4 :=
  ⟨VG.Proof.Argon2.Arm.xR s₀, by simp [hrd, hp.rd], contains_A hp.x_fits hd⟩

theorem in_y {s : VG.Arm.State} (hrd : s.rd = s₀.rd) {d : Nat} (hd : d + 4 ≤ 1024) :
    InRegions (s.rd ++ s.wr) (A (VG.Proof.Argon2.Arm.yp s₀) d) 4 :=
  ⟨VG.Proof.Argon2.Arm.yR s₀, by simp [hrd, hp.rd], contains_A hp.y_fits hd⟩

/-- A word of `x` is unchanged while only `out` and `scratch` are written. -/
theorem x_frame {m : Mem} (hf : Frame [VG.Proof.Argon2.Arm.outR s₀, VG.Proof.Argon2.Arm.scrR s₀] s₀.mem m) {d : Nat} (hd : d + 4 ≤ 1024) :
    m.readW (A (VG.Proof.Argon2.Arm.xp s₀) d) 32 = s₀.mem.readW (A (VG.Proof.Argon2.Arm.xp s₀) d) 32 := by
  refine hf.readW (r := VG.Proof.Argon2.Arm.xR s₀) (contains_A hp.x_fits hd) ?_ (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨hp.x_out, hp.x_scr⟩

theorem y_frame {m : Mem} (hf : Frame [VG.Proof.Argon2.Arm.outR s₀, VG.Proof.Argon2.Arm.scrR s₀] s₀.mem m) {d : Nat} (hd : d + 4 ≤ 1024) :
    m.readW (A (VG.Proof.Argon2.Arm.yp s₀) d) 32 = s₀.mem.readW (A (VG.Proof.Argon2.Arm.yp s₀) d) 32 := by
  refine hf.readW (r := VG.Proof.Argon2.Arm.yR s₀) (contains_A hp.y_fits hd) ?_ (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨hp.y_out, hp.y_scr⟩

/-- A word of `scratch` is unchanged while only `out` is written. -/
theorem scr_frame {m m' : Mem} (hf : Frame [VG.Proof.Argon2.Arm.outR s₀] m m') {d : Nat} (hd : d + 4 ≤ 4096) :
    m'.readW (A (VG.Proof.Argon2.Arm.scr s₀) d) 32 = m.readW (A (VG.Proof.Argon2.Arm.scr s₀) d) 32 := by
  refine hf.readW (r := VG.Proof.Argon2.Arm.scrR s₀) (contains_A hp.scr_fits hd) ?_ (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]
  exact hp.out_scr.symm

end Pre

end VG.Proof.Argon2.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.Arm.Compress`. -/
section

/-!
# Argon2 compression on ARMv7: correctness

The prologue saving the caller's registers and `out` (`prologue_ok`), the
initialization of both halves of scratch with X XOR Y (`init_ok`, one word at
a time), the rows and columns (`Proof/Argon2/Arm/Rounds.lean`), and the
epilogue writing the output and restoring the registers: `correct`.
-/

namespace VG.Proof.Argon2.Arm

open VG VG.Arm VG.Spec.Argon2
open VG.Impl.Argon2.Arm (prologue initWord finishWord epilogue saved spill outOff)
open VG.Proof.Sha512.Arm (A A_eq Reg64 rd64 mem_rd contains_A)
open VG.Proof.MdStream.Arm (Upd Mupd wp_ldr wp_str op2_reg readW_writeW_save)
open VG.Proof.Sha512.Arm (wp_eor)

/-- A word of `B + d` after a store at `B + e`, separate from it. -/
theorem readW_writeW_A (m : Mem) (v : BitVec 32) {B : BitVec 32} {d e : Nat}
    (hd : B.toNat + d + 4 ≤ 2 ^ 32) (he : B.toNat + e + 4 ≤ 2 ^ 32) (h : d + 4 ≤ e ∨ e + 4 ≤ d) :
    (m.writeW (A B e) v).readW (A B d) 32 = m.readW (A B d) 32 := by
  rw [A_eq (by omega), A_eq (by omega)]
  exact readW_writeW_save m _ v (by omega) (by omega) h

theorem spill_slots : Spill.Slots 2048 2088 spill := by decide

theorem saved_slots : Spill.Slots 2048 2084 VG.Impl.Argon2.Arm.saved := by decide

theorem saved_restorable : Spill.Restorable .r3 VG.Impl.Argon2.Arm.saved := by decide

/-- 32-bit word `i` of X XOR Y. -/
def xy (s₀ : VG.Arm.State) (i : Nat) : BitVec 32 :=
  s₀.mem.readW (A (VG.Proof.Argon2.Arm.xp s₀) (4 * i)) 32 ^^^ s₀.mem.readW (A (VG.Proof.Argon2.Arm.yp s₀) (4 * i)) 32

/-- After the prologue and the first `n` words of the initialization. -/
structure InitInv (s₀ s : VG.Arm.State) (n : Nat) : Prop where
  regs : ∀ r, r ≠ .r4 → r ≠ .r5 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [VG.Proof.Argon2.Arm.scrR s₀] s₀.mem s.mem
  saved : Spill.Saved s.mem (State.addr (VG.Proof.Argon2.Arm.scr s₀)) s₀.gpr spill
  low : VG.Proof.Argon2.Arm.Words s.mem (VG.Proof.Argon2.Arm.scr s₀) 0 (VG.Proof.Argon2.Arm.xy s₀) n
  high : VG.Proof.Argon2.Arm.Words s.mem (VG.Proof.Argon2.Arm.scr s₀) 1024 (VG.Proof.Argon2.Arm.xy s₀) n

section
variable {s₀ : VG.Arm.State} (hp : VG.Proof.Argon2.Arm.Pre s₀)
include hp

theorem prologue_ok {rest : List Instr} {Q : VG.Arm.State → Prop} (k : ∀ s, VG.Proof.Argon2.Arm.InitInv s₀ s 0 → WP isa (.block rest) s Q) :
    WP isa (.block (VG.Impl.Argon2.Arm.prologue ++ rest)) s₀ Q := by
  have fits := hp.scr_fits
  unfold VG.Impl.Argon2.Arm.prologue
  refine Spill.save_slots_ok VG.Proof.Argon2.Arm.spill_slots (by show (VG.Proof.Argon2.Arm.scr s₀).toNat + 2088 ≤ _; omega) (fun d h₁ h₂ => ?_) (k _ ⟨fun _ _ _ => rfl, rfl, rfl, rfl,
    ?_, Spill.saveMem_saved _ _ _ _ VG.Proof.Argon2.Arm.spill_slots, fun i hi => absurd hi (Nat.not_lt_zero _),
    fun i hi => absurd hi (Nat.not_lt_zero _)⟩)
  · exact ⟨VG.Proof.Argon2.Arm.scrR s₀, by simp [hp.wr], Offset.contains_base _ (by omega) (by omega)⟩
  · exact Spill.saveMem_frame_of _ _ (List.mem_singleton_self _) _ _ fun p hpm => by
      have := spill_slots.bound hpm
      exact Offset.contains_base _ (by omega) (by omega)

/-- One word of the initialization. -/
theorem initWord_ok {s : VG.Arm.State} {n : Nat} (hn : n < 256) (h : VG.Proof.Argon2.Arm.InitInv s₀ s n) :
    WP isa (.block (initWord n)) s (VG.Proof.Argon2.Arm.InitInv s₀ · (n + 1)) := by
  have hm : VG.Proof.Argon2.Arm.scrR s₀ ∈ [VG.Proof.Argon2.Arm.scrR s₀] := List.mem_singleton_self _
  have fits := hp.scr_fits
  unfold initWord
  refine wp_ldr (by omega) (by rw [h.regs _ (by decide) (by decide)]) (hp.in_x h.rd (by omega)) fun s₁ u₁ => ?_
  refine wp_ldr (by omega) (by rw [u₁.other _ (by decide), h.regs _ (by decide) (by decide)])
    (by rw [u₁.rd, u₁.wr]; exact hp.in_y h.rd (by omega)) fun s₂ u₂ => ?_
  refine VG.Proof.Sha512.Arm.wp_eor (op2_reg _ _) fun s₃ u₃ => ?_
  have v₃ : s₃.gpr .r4 = VG.Proof.Argon2.Arm.xy s₀ n := by
    rw [u₃.gpr, u₂.other _ (by decide), u₁.gpr, u₂.gpr, u₁.mem,
      hp.x_frame (h.frame.mono (by simp)) (by omega), hp.y_frame (h.frame.mono (by simp)) (by omega)]; rfl
  have r3 : s₃.gpr .r3 = VG.Proof.Argon2.Arm.scr s₀ := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.regs _ (by decide) (by decide)]
  refine wp_str (by omega) (by rw [r3]) (by rw [u₃.wr, u₂.wr, u₁.wr, h.wr]; exact hp.scr_wr rfl (by omega))
    fun s₄ u₄ => ?_
  refine wp_str (by omega) (by rw [u₄.gpr, r3])
    (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr]; exact hp.scr_wr rfl (by omega)) fun s₅ u₅ => WP.block_nil ?_
  have m₅ : s₅.mem = (s.mem.writeW (A (VG.Proof.Argon2.Arm.scr s₀) (4 * n)) (VG.Proof.Argon2.Arm.xy s₀ n)).writeW (A (VG.Proof.Argon2.Arm.scr s₀) (1024 + 4 * n)) (VG.Proof.Argon2.Arm.xy s₀ n) := by
    rw [u₅.mem, u₄.gpr, u₄.mem, u₃.mem, u₂.mem, u₁.mem, v₃]
  have r₅ : ∀ e, e + 4 ≤ 4096 → (e + 4 ≤ 4 * n ∨ 4 * n + 4 ≤ e) →
      (e + 4 ≤ 1024 + 4 * n ∨ 1024 + 4 * n + 4 ≤ e) →
      s₅.mem.readW (A (VG.Proof.Argon2.Arm.scr s₀) e) 32 = s.mem.readW (A (VG.Proof.Argon2.Arm.scr s₀) e) 32 := by
    intro e he h1 h2
    rw [m₅, VG.Proof.Argon2.Arm.readW_writeW_A _ _ (by omega) (by omega) h2, VG.Proof.Argon2.Arm.readW_writeW_A _ _ (by omega) (by omega) h1]
  refine ⟨fun r h4 h5 => ?_, ?_, ?_, ?_, ?_, fun p hpm => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · rw [u₅.gpr, u₄.gpr, u₃.other _ h4, u₂.other _ h5, u₁.other _ h4, h.regs r h4 h5]
  · rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd]
  · rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr]
  · rw [u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, h.sp]
  · rw [m₅]
    exact (h.frame.writeW hm _ (hp.scr_contains (by omega))).writeW hm _ (hp.scr_contains (by omega))
  · have := spill_slots.bound hpm
    have e := r₅ p.2 (by omega) (by omega) (by omega)
    rw [A_eq (by omega)] at e
    rw [e]; exact h.saved p hpm
  · by_cases e : i = n
    · subst e
      rw [m₅, VG.Proof.Argon2.Arm.readW_writeW_A _ _ (by omega) (by omega) (by omega), Nat.zero_add, Mem.readW_writeW_self32]
    · rw [r₅ _ (by omega) (by omega) (by omega)]; exact h.low i (by omega)
  · by_cases e : i = n
    · subst e; rw [m₅, Mem.readW_writeW_self32]
    · rw [r₅ _ (by omega) (by omega) (by omega)]; exact h.high i (by omega)

theorem init_ok {s : VG.Arm.State} (h : VG.Proof.Argon2.Arm.InitInv s₀ s 0) (n : Nat) (hn : n ≤ 256) :
    WP isa (.block ((List.range n).flatMap initWord)) s (VG.Proof.Argon2.Arm.InitInv s₀ · n) := by
  induction n with
  | zero => exact WP.block_nil h
  | succ n ih =>
    simp only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
    exact WP.block_append ((ih (by omega)).mono fun t ht => VG.Proof.Argon2.Arm.initWord_ok hp (by omega) ht)

end

/-! ## The epilogue -/

/-- Word `i` of the output: the permuted block XOR R, in memory `m`. -/
def outWord (B : BitVec 32) (m : Mem) (i : Nat) : BitVec 32 :=
  m.readW (A B (1024 + 4 * i)) 32 ^^^ m.readW (A B (4 * i)) 32

/-- After the first `n` words of the output, from the state `s₄` after the rounds. -/
structure FinInv (s₀ s₄ s : VG.Arm.State) (n : Nat) : Prop where
  r3 : s.gpr .r3 = VG.Proof.Argon2.Arm.scr s₀
  r2 : s.gpr .r2 = VG.Proof.Argon2.Arm.op s₀
  regs : ∀ r, r ≠ .r4 → r ≠ .r5 → r ≠ .r2 → s.gpr r = s₄.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [VG.Proof.Argon2.Arm.outR s₀] s₄.mem s.mem
  out : VG.Proof.Argon2.Arm.Words s.mem (VG.Proof.Argon2.Arm.op s₀) 0 (VG.Proof.Argon2.Arm.outWord (VG.Proof.Argon2.Arm.scr s₀) s₄.mem) n

section
variable {s₀ : VG.Arm.State} (hp : VG.Proof.Argon2.Arm.Pre s₀)
include hp

theorem finishWord_ok {s₄ s : VG.Arm.State} {n : Nat} (hn : n < 256) (h : VG.Proof.Argon2.Arm.FinInv s₀ s₄ s n) :
    WP isa (.block (finishWord n)) s (VG.Proof.Argon2.Arm.FinInv s₀ s₄ · (n + 1)) := by
  have hm : VG.Proof.Argon2.Arm.outR s₀ ∈ [VG.Proof.Argon2.Arm.outR s₀] := List.mem_singleton_self _
  have fits := hp.out_fits
  have sfits := hp.scr_fits
  unfold finishWord
  refine wp_ldr (by omega) (by rw [h.r3]) (hp.in_scr h.wr (by omega)) fun s₁ u₁ => ?_
  refine wp_ldr (by omega) (by rw [u₁.other .r3 (by decide), h.r3])
    (by rw [u₁.rd, u₁.wr]; exact hp.in_scr h.wr (by omega)) fun s₂ u₂ => ?_
  refine VG.Proof.Sha512.Arm.wp_eor (op2_reg _ _) fun s₃ u₃ => ?_
  have v₃ : s₃.gpr .r4 = VG.Proof.Argon2.Arm.outWord (VG.Proof.Argon2.Arm.scr s₀) s₄.mem n := by
    rw [u₃.gpr, u₂.other _ (by decide), u₁.gpr, u₂.gpr, u₁.mem, hp.scr_frame h.frame (by omega),
      hp.scr_frame h.frame (by omega)]; rfl
  refine wp_str (by omega) (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.r2])
    (by rw [u₃.wr, u₂.wr, u₁.wr]; exact hp.out_wr h.wr (by omega)) fun s₄' u₄ => WP.block_nil ?_
  have m₄ : s₄'.mem = s.mem.writeW (A (VG.Proof.Argon2.Arm.op s₀) (4 * n)) (VG.Proof.Argon2.Arm.outWord (VG.Proof.Argon2.Arm.scr s₀) s₄.mem n) := by
    rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem, v₃]
  refine ⟨?_, ?_, fun r h4 h5 h2 => ?_, ?_, ?_, ?_, ?_, fun i hi => ?_⟩
  · rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.r3]
  · rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.r2]
  · rw [u₄.gpr, u₃.other _ h4, u₂.other _ h5, u₁.other _ h4, h.regs r h4 h5 h2]
  · rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd]
  · rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr]
  · rw [u₄.sp, u₃.sp, u₂.sp, u₁.sp, h.sp]
  · rw [m₄]; exact h.frame.writeW hm _ (contains_A fits (by omega))
  · rw [m₄]
    by_cases e : i = n
    · subst e; rw [Nat.zero_add, Mem.readW_writeW_self32]
    · rw [VG.Proof.Argon2.Arm.readW_writeW_A _ _ (by omega) (by omega) (by omega)]
      exact h.out i (by omega)

theorem finish_ok {s₄ s : VG.Arm.State} (h : VG.Proof.Argon2.Arm.FinInv s₀ s₄ s 0) (n : Nat) (hn : n ≤ 256) :
    WP isa (.block ((List.range n).flatMap finishWord)) s (VG.Proof.Argon2.Arm.FinInv s₀ s₄ · n) := by
  induction n with
  | zero => exact WP.block_nil h
  | succ n ih =>
    simp only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
    exact WP.block_append ((ih (by omega)).mono fun t ht => VG.Proof.Argon2.Arm.finishWord_ok hp (by omega) ht)

end

/-! ## The whole function -/

theorem permR_sub {B : BitVec 32} : Region.Sub (VG.Proof.Argon2.Arm.permR B) ⟨State.addr B, 4096⟩ := Offset.sub_base _ (by decide)

section
variable {B : BitVec 32} (hfit : B.toNat + 4096 ≤ 2 ^ 32)
include hfit

/-- A word of `scratch` outside the permuted block is unchanged by its writes. -/
theorem outside_perm {m m' : Mem} (hf : Frame [VG.Proof.Argon2.Arm.permR B] m m') {d : Nat} (hd : d + 4 ≤ 4096)
    (ho : d + 4 ≤ 1024 ∨ 2048 ≤ d) : m'.readW (A B d) 32 = m.readW (A B d) 32 := by
  refine hf.readW (r := ⟨A B d, 4⟩) (Region.contains_self _ _) ?_ (by decide)
  simp only [List.mem_singleton, forall_eq]
  rw [A_eq (by omega)]
  exact Offset.disjoint _ (by omega) (by omega) (by omega)

theorem low_perm {m m' : Mem} (hf : Frame [VG.Proof.Argon2.Arm.permR B] m m') :
    VG.Proof.Argon2.Arm.blk m' B 0 = VG.Proof.Argon2.Arm.blk m B 0 := by
  apply Vector.ext
  intro j hj
  simp only [VG.Proof.Argon2.Arm.blk, Vector.getElem_ofFn, rd64]
  rw [VG.Proof.Argon2.Arm.outside_perm hfit hf (by omega) (by omega), VG.Proof.Argon2.Arm.outside_perm hfit hf (by omega) (by omega)]

end

theorem words_zero {m : Mem} {B : BitVec 32} {f : Nat → BitVec 32} (h : VG.Proof.Argon2.Arm.Words m B 0 f 256) :
    VG.Proof.Argon2.Arm.blk m B 0 = VG.Proof.Argon2.Arm.ofWords f := VG.Proof.Argon2.Arm.blk_of_words fun i hi => h i hi

theorem correct {s₀ : VG.Arm.State} (hp : VG.Proof.Argon2.Arm.Pre s₀) :
    WP isa Impl.Argon2.Arm.compress s₀ fun t =>
      (∀ r ∈ preserved, t.gpr r = s₀.gpr r) ∧ compressArm.post s₀ t := by
  have fits := hp.scr_fits
  unfold Impl.Argon2.Arm.compress Impl.Argon2.Arm.rounds
  refine WP.seq (VG.Proof.Argon2.Arm.prologue_ok hp fun s₁ h₁ => (VG.Proof.Argon2.Arm.init_ok hp h₁ 256 (Nat.le_refl _)).mono fun s₂ h₂ => ?_)
  have A₂ : VG.Proof.Argon2.Arm.At (VG.Proof.Argon2.Arm.scr s₀) s₂ := ⟨by rw [h₂.regs _ (by decide) (by decide)], fun o ho => by
    rw [h₂.wr]; exact ⟨hp.scr_wr rfl (by omega), hp.scr_wr rfl (by omega)⟩⟩
  refine WP.seq (WP.seq ((VG.Proof.Argon2.Arm.rounds_ok fits rowIndex Proof.Argon2.rowIndex_injective (List.finRange 8)
    A₂).mono fun s₃ st₃ => (VG.Proof.Argon2.Arm.rounds_ok fits colIndex Proof.Argon2.colIndex_injective
      (List.finRange 8) (A₂.of_step st₃)).mono fun s₄ st₄ => ?_))
  have k₄ := st₃.keep.trans st₄.keep
  have pf : Frame [VG.Proof.Argon2.Arm.permR (VG.Proof.Argon2.Arm.scr s₀)] s₂.mem s₄.mem := st₃.frame.trans st₄.frame
  have r3₄ : s₄.gpr .r3 = VG.Proof.Argon2.Arm.scr s₀ := by rw [k₄.r3, h₂.regs _ (by decide) (by decide)]
  have sv₄ : Spill.Saved s₄.mem (State.addr (VG.Proof.Argon2.Arm.scr s₀)) s₀.gpr spill :=
    h₂.saved.frame VG.Proof.Argon2.Arm.spill_slots pf fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (by omega) (by omega) (by omega)
  unfold Impl.Argon2.Arm.epilogue
  simp only [List.cons_append]
  have i₄ : InRegions (s₄.rd ++ s₄.wr) (A (VG.Proof.Argon2.Arm.scr s₀) outOff) 4 := by
    rw [k₄.rd, k₄.wr, h₂.rd, h₂.wr]; exact hp.in_scr rfl (by decide)
  refine wp_ldr (by decide) (by rw [r3₄]) i₄ fun s₅ u₅ => ?_
  have e₅ : s₅.gpr .r2 = VG.Proof.Argon2.Arm.op s₀ := by
    rw [u₅.gpr]
    have := sv₄ (.r2, outOff) (by decide)
    rw [A_eq (by simp only [outOff]; omega)]; exact this
  have h₅ : VG.Proof.Argon2.Arm.FinInv s₀ s₄ s₅ 0 :=
    ⟨by rw [u₅.other _ (by decide), r3₄], e₅, fun r _ _ h2 => u₅.other r h2,
      by rw [u₅.rd, k₄.rd, h₂.rd], by rw [u₅.wr, k₄.wr, h₂.wr], by rw [u₅.sp, k₄.sp, h₂.sp],
      by rw [u₅.mem]; exact Frame.refl _ _, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  refine WP.block_append ((VG.Proof.Argon2.Arm.finish_ok hp h₅ 256 (Nat.le_refl _)).mono fun s₆ h₆ => ?_)
  have sv₆ : Spill.Saved s₆.mem (State.addr (VG.Proof.Argon2.Arm.scr s₀)) s₀.gpr VG.Impl.Argon2.Arm.saved := fun p hpm =>
    h₆.frame.readW (r := ⟨State.addr (VG.Proof.Argon2.Arm.scr s₀) + BitVec.ofNat 64 p.2, 4⟩) (Region.contains_self _ _) (by
      have := saved_slots.bound hpm
      simp only [List.mem_singleton, forall_eq]
      exact (hp.out_scr.sub_right (Offset.sub_base _ (by omega))).symm) (by decide) |>.trans
      (sv₄ p (List.mem_append_left _ hpm))
  rw [← List.append_nil (List.map _ VG.Impl.Argon2.Arm.saved)]
  refine Spill.restore_slots_ok VG.Proof.Argon2.Arm.saved_slots VG.Proof.Argon2.Arm.saved_restorable (g := s₀.gpr) (by rw [h₆.r3]; omega)
    (fun d h₁ h₂ => by rw [h₆.r3, h₆.rd, h₆.wr, ← A_eq (by omega)]; exact hp.in_scr rfl (by omega))
    (by rw [h₆.r3]; exact sv₆) fun t ht ho hm hrd hwr hsp => WP.block_nil ⟨?_, ?_⟩
  · intro r hr
    exact Spill.restored_of ht (by decide) r hr
  · -- The output.
    have R₂ : VG.Proof.Argon2.Arm.blk s₂.mem (VG.Proof.Argon2.Arm.scr s₀) 0 = VG.Proof.Argon2.Arm.ofWords (VG.Proof.Argon2.Arm.xy s₀) := VG.Proof.Argon2.Arm.words_zero h₂.low
    have W₂ : VG.Proof.Argon2.Arm.working s₂.mem (VG.Proof.Argon2.Arm.scr s₀) = VG.Proof.Argon2.Arm.ofWords (VG.Proof.Argon2.Arm.xy s₀) := by
      rw [VG.Proof.Argon2.Arm.working_eq]; exact VG.Proof.Argon2.Arm.blk_of_words fun i hi => h₂.high i hi
    have X : VG.Spec.Argon2.xorBlock (VG.Spec.Argon2.blockAt s₀.mem (State.addr (VG.Proof.Argon2.Arm.xp s₀))) (VG.Spec.Argon2.blockAt s₀.mem (State.addr (VG.Proof.Argon2.Arm.yp s₀))) =
        VG.Proof.Argon2.Arm.ofWords (VG.Proof.Argon2.Arm.xy s₀) := by
      rw [VG.Proof.Argon2.Arm.blockAt_eq hp.x_fits, VG.Proof.Argon2.Arm.blockAt_eq hp.y_fits,
        VG.Proof.Argon2.Arm.blk_of_words (f := fun i => s₀.mem.readW (A (VG.Proof.Argon2.Arm.xp s₀) (4 * i)) 32)
          (fun i _ => by rw [Nat.zero_add]),
        VG.Proof.Argon2.Arm.blk_of_words (f := fun i => s₀.mem.readW (A (VG.Proof.Argon2.Arm.yp s₀) (4 * i)) 32)
          (fun i _ => by rw [Nat.zero_add]), VG.Proof.Argon2.Arm.xor_words]
      rfl
    have O : VG.Proof.Argon2.Arm.blk t.mem (VG.Proof.Argon2.Arm.op s₀) 0 = VG.Spec.Argon2.xorBlock (VG.Proof.Argon2.Arm.working s₄.mem (VG.Proof.Argon2.Arm.scr s₀)) (VG.Proof.Argon2.Arm.blk s₄.mem (VG.Proof.Argon2.Arm.scr s₀) 0) := by
      rw [hm, VG.Proof.Argon2.Arm.words_zero h₆.out, VG.Proof.Argon2.Arm.working_eq,
        VG.Proof.Argon2.Arm.blk_of_words (f := fun i => s₄.mem.readW (A (VG.Proof.Argon2.Arm.scr s₀) (1024 + 4 * i)) 32) (fun _ _ => rfl),
        VG.Proof.Argon2.Arm.blk_of_words (f := fun i => s₄.mem.readW (A (VG.Proof.Argon2.Arm.scr s₀) (4 * i)) 32)
          (fun i _ => by rw [Nat.zero_add]), VG.Proof.Argon2.Arm.xor_words]
      rfl
    show VG.Spec.Argon2.blockAt t.mem (State.addr (VG.Proof.Argon2.Arm.op s₀)) = _
    rw [VG.Proof.Argon2.Arm.blockAt_eq hp.out_fits, O, VG.Proof.Argon2.Arm.low_perm fits pf, R₂, st₄.working, st₃.working, W₂, ← X]
    simp only [compress]

end VG.Proof.Argon2.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.Arm.CompressLit`. -/
section

/-!
# Argon2 compression on ARMv7: the code as a literal

The compression function is fully unrolled: its literal (`materialize_code`)
spares the kernel building the instructions in every check that evaluates
the code (constant time, `spSafe`), and its callers call it.
-/

namespace VG.Impl.Argon2.Arm

materialize_code VG.Impl.Argon2.Arm.compress

end VG.Impl.Argon2.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.Arm.CompressVerified`. -/
section

/-!
# Argon2 compression on ARMv7: verified

Constant time is the taint analysis on the literal code: the pointers are
public, and `out`, kept in `scratch` across the rounds, is a public slot of
it. `compress_verified'` is the proof against `compressArm`, which the
derivation uses for its calls; the shared contract
`Spec.Argon2.compressContract` implies it (`compress_verified`).
-/

namespace VG.Proof.Argon2.Arm

open VG VG.Arm VG.Spec.Argon2

/-- The pointers are public, and they are the bases of `out` and `scratch`. -/
def τ₀ : VG.Arm.Taint.T :=
  { regs := .ofList [.r0, .r1, .r2, .r3], flags := false, lens := [1024, 4096],
    bases := [(.r2, 0), (.r3, 1)] }

theorem wf₀ {s : VG.Arm.State} (hp : VG.Proof.Argon2.Arm.Pre s) : VG.Arm.Taint.Wf VG.Proof.Argon2.Arm.τ₀ s := by
  have ho := hp.out_fits; have hsc := hp.scr_fits
  refine ⟨fun _ => ⟨?_, ?_, ?_⟩, fun p hp' => ?_, fun h => absurd h (Nat.lt_irrefl 0),
    fun _ h => (List.not_mem_nil h).elim⟩
  · simp only [hp.wr, VG.Proof.Argon2.Arm.τ₀]
    exact .cons (by simp) (.cons (by simp) .nil)
  · simp only [hp.wr]
    exact .cons (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hp.out_scr)
      (.cons (fun _ h => (List.not_mem_nil h).elim) .nil)
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [MdStream.Arm.addr_toNat] <;> omega
  · simp only [VG.Proof.Argon2.Arm.τ₀, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl <;> simp [VG.Arm.Taint.region, hp.wr]

theorem agree₀ {s₁ s₂ : VG.Arm.State} (h₁ : compressArm.pre s₁) (h₂ : compressArm.pre s₂)
    (hpub : compressArm.pub s₁ s₂) : VG.Arm.Taint.Agree VG.Proof.Argon2.Arm.τ₀ s₁ s₂ := by
  obtain ⟨p0, p1, p2, p3⟩ := hpub
  have hp₁ := VG.Proof.Argon2.Arm.pre_of _ h₁; have hp₂ := VG.Proof.Argon2.Arm.pre_of _ h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, VG.Proof.Argon2.Arm.wf₀ hp₁, VG.Proof.Argon2.Arm.wf₀ hp₂,
    fun sl h => by simp [VG.Proof.Argon2.Arm.τ₀] at h, fun _ h => (List.not_mem_nil h).elim,
    fun h => absurd h (Nat.lt_irrefl 0), fun _ h => absurd h (Nat.not_lt_zero _)⟩
  · simp only [VG.Proof.Argon2.Arm.τ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption
  · rw [hp₁.wr, hp₂.wr]; simp only [VG.Proof.Argon2.Arm.outR, VG.Proof.Argon2.Arm.scrR, VG.Proof.Argon2.Arm.op, VG.Proof.Argon2.Arm.scr, p2, p3]

theorem compress_ct : ConstantTime isa compressArm.pre compressArm.pub Impl.Argon2.Arm.compress :=
  VG.Taint.constantTime (A := VG.Arm.taint) VG.Proof.Argon2.Arm.τ₀ (fun _ _ h₁ h₂ hpub => VG.Proof.Argon2.Arm.agree₀ h₁ h₂ hpub) (by taint_decide)

/-- A state satisfying the precondition. -/
def satState : VG.Arm.State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x1400 | .r2 => 0x2000 | .r3 => 0x3000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 1024⟩, ⟨0x1400, 1024⟩]
  wr := [⟨0x2000, 1024⟩, ⟨0x3000, 4096⟩]

theorem sat_pre : compressArm.pre VG.Proof.Argon2.Arm.satState := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, by decide, by decide, by decide, by decide⟩ <;>
  exact Region.disjoint_of_sep (by decide)

/-- The proof, against the contract the derivation's calls use. -/
theorem compress_verified' : Verified Arm.target Impl.Argon2.Arm.compress VG.Proof.Argon2.Arm.compressArm := by
  refine ⟨fun s hs => ?_, VG.Proof.Argon2.Arm.compress_ct, ⟨VG.Proof.Argon2.Arm.satState, VG.Proof.Argon2.Arm.sat_pre⟩⟩
  obtain ⟨t, s', he, h₁, h₂⟩ := VG.Proof.Argon2.Arm.correct (VG.Proof.Argon2.Arm.pre_of s hs)
  exact ⟨t, s', he, ⟨h₁, Exec.sp he⟩, h₂⟩

theorem compress_implies : compressArm.Implies (Spec.Argon2.compressContract Arm.abi) := by
  sig_implies [Spec.Argon2.compressContract, Spec.Argon2.compressSig, VG.Proof.Argon2.Arm.compressArm, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [satState, Mem.readW, Mem.read] using VG.Proof.Argon2.Arm.satState

/-- The emitted function, against the shared contract. -/
theorem compress_verified :
    Verified Arm.target Impl.Argon2.Arm.compress (Spec.Argon2.compressContract Arm.abi) :=
  compress_verified'.of_implies VG.Proof.Argon2.Arm.compress_implies

end VG.Proof.Argon2.Arm

end
