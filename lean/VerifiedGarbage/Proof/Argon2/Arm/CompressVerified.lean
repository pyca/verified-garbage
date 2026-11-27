module

public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Argon2.Arm.CompressLit
public import VerifiedGarbage.Impl.Argon2.Arm.Compress
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Argon2.Arm.CompressLit
meta import VerifiedGarbage.Impl.Argon2.Arm.Compress
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Argon2.Contract
import VerifiedGarbage.Proof.Argon2.Permutation
public import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Argon2.Permutation
import VerifiedGarbage.Proof.Framework.PlainSimp
meta import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Sha512.Arm.Rounds
public import VerifiedGarbage.Spec.Argon2.Contract
meta import VerifiedGarbage.Proof.Argon2.Contract
meta import VerifiedGarbage.Proof.Sha512.Arm.Rounds
meta import VerifiedGarbage.Spec.Argon2.Contract
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Argon2.Spec
import VerifiedGarbage.Proof.Blake2.Arm.BlockB
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Bswap
public import VerifiedGarbage.Spec.Argon2
public import Init.Data.BitVec.Basic
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Argon2.Spec
meta import VerifiedGarbage.Proof.Blake2.Arm.BlockB
meta import VerifiedGarbage.Proof.Framework.PowLit
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Bswap
meta import VerifiedGarbage.Spec.Argon2
meta import Init.Data.BitVec.Basic

/-! ### `Argon2.Arm.Words`, which this module and modules that import it used -/

section

/-! ### `Argon2.Arm.Gb`, which this module and modules that import it used -/

section

/-! ### `Argon2.Arm.Mix`, which this module and modules that import it used -/

section

/-!
# Argon2 on ARMv7: the products and GB

`mulHi_ok`: the high half of a 32 × 32-bit product, from four products of
16-bit halves (`VG.Impl.Argon2.Arm.mulHi`); `addMul_ok`: `addMul` on a pair of
registers; and `wp_gb`: GB on four words of `scratch` (at `r3`), computed in
registers as BLAKE2b's `G` is (`Proof/Blake2/Arm/BlockB.lean`), leaves the
memory `gbMem`, with the words of `Proof.Argon2.mix` stored.
-/

@[expose] public section

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
  omega_arith

theorem toNat_hi16 (z : BitVec 32) : (z >>> 16).toNat = z.toNat / 2 ^ 16 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem toNat_mul16 {a b : BitVec 32} (ha : a.toNat < 2 ^ 16) (hb : b.toNat < 2 ^ 16) :
    (a * b).toNat = a.toNat * b.toNat := by
  rw [BitVec.toNat_mul]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le ha (Nat.le_of_lt hb) (by omega_arith))
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

theorem mul16_le {a b : Nat} (ha : a < 2 ^ 16) (hb : b < 2 ^ 16) : a * b ≤ (2 ^ 16 - 1) * (2 ^ 16 - 1) :=
  Nat.mul_le_mul (by omega_arith) (by omega_arith)

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
  have bx0 : (x <<< 16 >>> 16).toNat < 2 ^ 16 := by rw [ex0]; omega_arith
  have by0 : (y <<< 16 >>> 16).toNat < 2 ^ 16 := by rw [ey0]; omega_arith
  have bx1 : (x >>> 16).toNat < 2 ^ 16 := by rw [ex1]; omega_arith
  have by1 : (y >>> 16).toNat < 2 ^ 16 := by rw [ey1]; omega_arith
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
  omega_arith

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
  rw [hi_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (by omega_arith)]

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

end

end

/-!
# Argon2 on ARMv7: GB on the permuted block

`wp_gb`: GB on the words at `[r3, #a]`, …, `[r3, #d]` stores the words of
`Proof.Argon2.mix` (`gbMem`), with the registers of `gbRegs` written. The
permuted block in `scratch[1024, 2048)` as a vector of words (`working`), and
`gbAt_ok`: one GB, with `r3` moved on from the base by `8e` bytes, updates
words `e` further on as `Proof.Argon2.mixWords`, and writes nothing else.
-/

@[expose] public section

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
variable {rest : List Instr} {s : State} {Q : State → Prop}

theorem wp_gb {a b c d : Nat} {V : BitVec 32} {N : Nat} (hN : N ≤ 4092)
    (ha : a + 8 ≤ N) (hb : b + 8 ≤ N) (hc : c + 8 ≤ N) (hd : d + 8 ≤ N)
    (hRV : Reg64 s.wr V N) (h3 : s.gpr .r3 = V)
    (K : ∀ s', Wrote gbRegs s s' (gbMem s.mem V a b c d) → WP isa (.block rest) s' Q) :
    WP isa (.block (gb a b c d ++ rest)) s Q := by
  unfold gb
  simp only [List.append_assoc]
  obtain iV : ∀ o, o + 8 ≤ N → InRegions (s.rd ++ s.wr) (A V o) 4 ∧
      InRegions (s.rd ++ s.wr) (A V (o + 4)) 4 := fun o ho => ⟨mem_rd (hRV o ho).1, mem_rd (hRV o ho).2⟩
  -- Load the four words.
  refine wp_ld64 (by decide) (by decide) (by omega_using [hN, ha]) h3 rfl (iV a ha).1 (iV a ha).2
    fun s₁ o₁ pa => ?_
  refine wp_ld64 (by decide) (by decide) (by omega_using [hN, hb]) (by rw [o₁.gpr _ (by decide), h3]) o₁.mem
    (by rw [o₁.rd, o₁.wr]; exact (iV b hb).1) (by rw [o₁.rd, o₁.wr]; exact (iV b hb).2)
    fun s₂ o₂ pb => ?_
  obtain O₂ := o₁.trans o₂
  refine wp_ld64 (by decide) (by decide) (by omega_using [hN, hc]) (by rw [O₂.gpr _ (by decide), h3]) O₂.mem
    (by rw [O₂.rd, O₂.wr]; exact (iV c hc).1) (by rw [O₂.rd, O₂.wr]; exact (iV c hc).2)
    fun s₃ o₃ pc => ?_
  obtain O₃ := O₂.trans o₃
  refine wp_ld64 (by decide) (by decide) (by omega_using [hN, hd]) (by rw [O₃.gpr _ (by decide), h3]) O₃.mem
    (by rw [O₃.rd, O₃.wr]; exact (iV d hd).1) (by rw [O₃.rd, O₃.wr]; exact (iV d hd).2)
    fun s₄ o₄ pd => ?_
  obtain O₄ := O₃.trans o₄
  -- a := addMul(a, b)
  refine addMul_ok (by decide) (pa.of_only ((o₂.trans o₃).trans o₄) (by decide) (by decide))
    (pb.of_only (o₃.trans o₄) (by decide) (by decide)) fun s₅ o₅ pa₁ => ?_
  -- d := (d ⊕ a) >>> 32
  refine wp_xor64 (by decide) (by decide) (pd.of_only o₅ (by decide) (by decide)) pa₁
    fun s₆ o₆ p₆ => ?_
  obtain pd₁ := pair_swap p₆
  -- c := addMul(c, d)
  refine addMul_ok (by decide) (pc.of_only ((o₄.trans o₅).trans o₆) (by decide) (by decide)) pd₁
    fun s₇ o₇ pc₁ => ?_
  -- b := (b ⊕ c) >>> 24
  refine wp_xor64 (by decide) (by decide)
    (pb.of_only ((((o₃.trans o₄).trans o₅).trans o₆).trans o₇) (by decide) (by decide)) pc₁
    fun s₈ o₈ p₈ => ?_
  refine wp_rotr (n := 24) (by decide) (by decide) (by decide) (by decide) (by decide) p₈
    fun s₉ o₉ pb₁ => ?_
  -- a := addMul(a, b)
  refine addMul_ok (by decide) (pa₁.of_only ((((o₆.trans o₇).trans o₈).trans o₉)) (by decide) (by decide))
    pb₁ fun s₁₀ o₁₀ pa₂ => ?_
  -- d := (d ⊕ a) >>> 16
  refine wp_xor64 (by decide) (by decide)
    (pd₁.of_only ((((o₇.trans o₈).trans o₉).trans o₁₀)) (by decide) (by decide)) pa₂
    fun s₁₁ o₁₁ p₁₁ => ?_
  refine wp_rotr (n := 16) (by decide) (by decide) (by decide) (by decide) (by decide) p₁₁
    fun s₁₂ o₁₂ pd₂ => ?_
  -- c := addMul(c, d)
  refine addMul_ok (by decide)
    (pc₁.of_only (((((o₈.trans o₉).trans o₁₀).trans o₁₁).trans o₁₂)) (by decide) (by decide)) pd₂
    fun s₁₃ o₁₃ pc₂ => ?_
  -- b := (b ⊕ c) >>> 63
  refine wp_xor64 (by decide) (by decide)
    (pb₁.of_only ((((o₁₀.trans o₁₁).trans o₁₂).trans o₁₃)) (by decide) (by decide)) pc₂
    fun s₁₄ o₁₄ p₁₄ => ?_
  refine wp_rotr' (n := 63) (by decide) (by decide) (by decide) (by decide) (by decide) p₁₄
    fun s₁₅ o₁₅ pb₂ => ?_
  obtain O₁₅ := ((((((((((O₄.trans o₅).trans o₆).trans o₇).trans o₈).trans o₉).trans o₁₀).trans
    o₁₁).trans o₁₂).trans o₁₃).trans o₁₄).trans o₁₅
  obtain pa₂' := pa₂.of_only ((((o₁₁.trans o₁₂).trans o₁₃).trans o₁₄).trans o₁₅) (by decide) (by decide)
  obtain pc₂' := pc₂.of_only (o₁₄.trans o₁₅) (by decide) (by decide)
  obtain pd₂' := pd₂.of_only ((o₁₃.trans o₁₄).trans o₁₅) (by decide) (by decide)
  -- Store them.
  obtain w : Reg64 s₁₅.wr V N := by rw [O₁₅.wr]; exact hRV
  obtain r3 : s₁₅.gpr .r3 = V := by rw [O₁₅.gpr _ (by decide), h3]
  refine wp_st (by omega_using [hN, ha]) r3 pa₂' (w a ha).1 (w a ha).2 fun s₁₆ u₁₆ => ?_
  refine wp_st (by omega_using [hN, hb]) (by rw [u₁₆.gpr, r3]) (by rw [Pair, u₁₆.gpr]; exact pb₂)
    (by rw [u₁₆.wr]; exact (w b hb).1) (by rw [u₁₆.wr]; exact (w b hb).2) fun s₁₇ u₁₇ => ?_
  refine wp_st (by omega_using [hN, hc]) (by rw [u₁₇.gpr, u₁₆.gpr, r3]) (by rw [Pair, u₁₇.gpr, u₁₆.gpr]; exact pc₂')
    (by rw [u₁₇.wr, u₁₆.wr]; exact (w c hc).1) (by rw [u₁₇.wr, u₁₆.wr]; exact (w c hc).2)
    fun s₁₈ u₁₈ => ?_
  refine wp_st (by omega_using [hN, hd]) (by rw [u₁₈.gpr, u₁₇.gpr, u₁₆.gpr, r3])
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
def working (m : Mem) (B : BitVec 32) : Block := Vector.ofFn fun i => rd64 m B (wOff i.val)

theorem working_get (m : Mem) (B : BitVec 32) (i : Fin 128) :
    (working m B)[i] = rd64 m B (wOff i.val) := by
  simp only [working, Fin.getElem_fin, Vector.getElem_ofFn]

/-- The permuted block's region. -/
abbrev permR (B : BitVec 32) : Region := ⟨State.addr B + BitVec.ofNat 64 1024, 1024⟩

theorem wOff_lt (i : Fin 128) : wOff i.val + 8 ≤ 2048 := by have := i.isLt; simp only [wOff]; omega_using []

section
variable {B : BitVec 32} (hfit : B.toNat + 4096 ≤ 2 ^ 32)
include hfit

theorem working_write (m : Mem) (i : Fin 128) (v : Word) :
    working (write64 m B (wOff i.val) v) B = (working m B).set i v := by
  apply Vector.ext
  intro j hj
  simp only [working, Vector.getElem_ofFn, Vector.getElem_set]
  by_cases h : i.val = j
  · subst j
    simp only [ite_true]
    exact rd64_write64_self m v (by have := wOff_lt i; omega_using [hfit, this])
  · simp only [h, ite_false]
    exact rd64_write64_ne m v (by have := wOff_lt i; omega_using [hfit, this]) (by simp only [wOff]; omega_using [hfit, hj])
      (by simp only [wOff]; omega_using [h])

/-- A write to a word of the permuted block stays in its region. -/
theorem frame_write (m m' : Mem) (hf : Frame [permR B] m m') (i : Fin 128) (v : Word) :
    Frame [permR B] m (write64 m' B (wOff i.val) v) := by
  obtain c : ∀ e, e + 4 ≤ 1024 → (permR B).Contains (A B (1024 + e)) 4 := fun e he => by
    rw [VG.Proof.Sha512.Arm.A_eq (by omega_using [hfit, he]), ← Offset.add_ofNat_add_ofNat]
    exact Offset.contains_base _ he (by omega_using [he])
  obtain m₁ := List.mem_singleton_self (permR B)
  have := i.isLt
  simp only [write64]
  exact (hf.writeW m₁ _ (c (8 * i.val) (by omega_using []))).writeW m₁ _
    (by rw [show wOff i.val + 4 = 1024 + (8 * i.val + 4) by simp only [wOff]; omega_using []]
        exact c _ (by omega_using []))

end

/-! ## GB -/

/-- `s'` is `s` but for the registers GB writes and memory. -/
structure Keep (s s' : State) : Prop where
  gpr : ∀ r, r ∉ gbRegs → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem Keep.refl (s : State) : Keep s s := ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem Keep.trans {s s₁ s₂ : State} (k₁ : Keep s s₁) (k₂ : Keep s₁ s₂) : Keep s s₂ :=
  ⟨fun r hr => by rw [k₂.gpr r hr, k₁.gpr r hr], k₂.rd.trans k₁.rd, k₂.wr.trans k₁.wr, k₂.sp.trans k₁.sp⟩

theorem Keep.r3 {s s' : State} (k : Keep s s') : s'.gpr .r3 = s.gpr .r3 := k.gpr _ (by decide)

/-- What a step of GB leaves: the registers but GB's, and the memory at `B`
with the permuted block `v` in place of the old one, `Frame [permR B]`. -/
structure Step (B : BitVec 32) (s : State) (v : Block) (t : State) : Prop where
  keep : Keep s t
  working : working t.mem B = v
  frame : Frame [permR B] s.mem t.mem

theorem Step.trans {B : BitVec 32} {s t u : State} {v w : Block} (h : Step B s v t) (h' : Step B t w u) :
    Step B s w u := ⟨h.keep.trans h'.keep, h'.working, h.frame.trans h'.frame⟩

/-! ## GB with `r3` moved on -/

theorem A_shift (b : BitVec 32) (d o : Nat) : A (b + BitVec.ofNat 32 d) o = A b (d + o) := by
  simp only [A, BitVec.add_assoc, BitVec.ofNat_add]

theorem rd64_shift (m : Mem) (b : BitVec 32) (d o : Nat) :
    rd64 m (b + BitVec.ofNat 32 d) o = rd64 m b (d + o) := by
  simp only [rd64, A_shift, Nat.add_assoc]

theorem write64_shift (m : Mem) (b : BitVec 32) (d o : Nat) (x : BitVec 64) :
    write64 m (b + BitVec.ofNat 32 d) o x = write64 m b (d + o) x := by
  simp only [write64, A_shift, Nat.add_assoc]

theorem gbMem_shift (m : Mem) (B : BitVec 32) (e a b c d : Nat) :
    gbMem m (B + BitVec.ofNat 32 e) a b c d = gbMem m B (e + a) (e + b) (e + c) (e + d) := by
  simp only [gbMem, rd64_shift, write64_shift]

theorem reg64_shift {wr : List Region} {B : BitVec 32} {N N' d : Nat} (h : Reg64 wr B N)
    (hd : d + N' ≤ N) : Reg64 wr (B + BitVec.ofNat 32 d) N' := fun o ho => by
  rw [A_shift, A_shift, ← Nat.add_assoc]
  exact h (d + o) (by omega_using [hd, ho])

/-- GB on the words `a₀`, …, `d₀` of the permuted block at `r3`, which is
`8e` bytes past `B`: on the words `a = a₀ + e`, …, `d` of the block at `B`. -/
theorem gbAt_ok {B : BitVec 32} (hfit : B.toNat + 4096 ≤ 2 ^ 32) {s : State} {e : Nat}
    (h3 : s.gpr .r3 = B + BitVec.ofNat 32 (8 * e)) (hA : Reg64 s.wr B 2048) {a₀ b₀ c₀ d₀ : Nat}
    (a b c d : Fin 128) (ha : a.val = a₀ + e) (hb : b.val = b₀ + e) (hc : c.val = c₀ + e)
    (hd : d.val = d₀ + e) :
    WP isa (gbAt a₀ b₀ c₀ d₀) s
      (Step B s (Proof.Argon2.mixWords (working s.mem B) a b c d)) := by
  have sh (x : Fin 128) (x₀ : Nat) (h : x.val = x₀ + e) : 8 * e + wOff x₀ = wOff x.val := by
    simp only [wOff]; omega_using [h]
  have lt (x : Fin 128) (x₀ : Nat) (h : x.val = x₀ + e) : wOff x₀ + 8 ≤ 2048 - 8 * e := by
    have := x.isLt; simp only [wOff]; omega
  unfold gbAt
  rw [← List.append_nil (gb _ _ _ _)]
  refine wp_gb (N := 2048 - 8 * e) (by omega_using []) (lt a a₀ ha) (lt b b₀ hb) (lt c c₀ hc) (lt d d₀ hd)
    (reg64_shift hA (by omega)) h3 fun t w => WP.block_nil ⟨⟨w.gpr, w.rd, w.wr, w.sp⟩, ?_, ?_⟩
  · rw [w.mem, gbMem_shift, sh a a₀ ha, sh b b₀ hb, sh c c₀ hc, sh d d₀ hd, gbMem]
    simp only [working_write hfit, ← working_get]
    rfl
  · rw [w.mem, gbMem_shift, sh a a₀ ha, sh b b₀ hb, sh c c₀ hc, sh d d₀ hd, gbMem]
    exact frame_write hfit _ _ (frame_write hfit _ _ (frame_write hfit _ _ (frame_write hfit _ _
      (Frame.refl _ _) _ _) _ _) _ _) _ _

end VG.Proof.Argon2.Arm

end

end

/-!
# Argon2 on ARMv7: blocks as 32-bit words

A block at `B + o` (`blk m B o`) as 64-bit words, each the pair of 32-bit words
the code copies: `blk_of_words` builds it from them, `blockAt_eq` relates it to
the contract's `Proof.Argon2.blockAt`, and `xor_words` XORs two blocks word by
word.
-/

@[expose] public section

namespace VG.Proof.Argon2.Arm

open VG VG.Arm VG.Spec.Argon2
open VG.Impl.Sha512.Arm (lo hi)
open VG.Proof.Sha512.Arm (rd64 A A_eq readW64 lo_xor hi_xor lo_append hi_append eq_of_lo_hi)

/-- The block at `B + o`, as pairs of 32-bit words. -/
def blk (m : Mem) (B : BitVec 32) (o : Nat) : Block := Vector.ofFn fun j => rd64 m B (o + 8 * j.val)

/-- The block made of the 32-bit words `f 0, f 1, …` (two per 64-bit word, the low one first). -/
def ofWords (f : Nat → BitVec 32) : Block := Vector.ofFn fun j => f (2 * j.val + 1) ++ f (2 * j.val)

theorem blk_of_words {m : Mem} {B : BitVec 32} {o : Nat} {f : Nat → BitVec 32}
    (h : ∀ i < 256, m.readW (A B (o + 4 * i)) 32 = f i) : blk m B o = ofWords f := by
  apply Vector.ext
  intro j hj
  simp only [blk, ofWords, Vector.getElem_ofFn, rd64]
  rw [show o + 8 * j + 4 = o + 4 * (2 * j + 1) by omega_using [], show o + 8 * j = o + 4 * (2 * j) by omega_using [],
    h _ (by omega_using [hj]), h _ (by omega_using [hj])]

theorem working_eq (m : Mem) (B : BitVec 32) : working m B = blk m B 1024 := by
  apply Vector.ext
  intro j hj
  simp only [working, blk, Vector.getElem_ofFn, Impl.Argon2.Arm.wOff]

theorem blockAt_eq {m : Mem} {B : BitVec 32} (hfit : B.toNat + 1024 ≤ 2 ^ 32) :
    blockAt m (State.addr B) = blk m B 0 := by
  apply Vector.ext
  intro j hj
  simp only [blockAt, blk, Vector.getElem_ofFn, Nat.zero_add, rd64]
  rw [A_eq (by omega_using [hfit, hj]), A_eq (by omega_using [hfit, hj]), ← Offset.add_ofNat_add_ofNat _ _ 4,
    show BitVec.ofNat 64 4 = (4 : Addr) from rfl, ← readW64]
  simp only [Mem.readW, BitVec.setWidth_eq]

theorem append_xor (a b c d : BitVec 32) : (a ++ b) ^^^ (c ++ d) = (a ^^^ c) ++ (b ^^^ d) :=
  eq_of_lo_hi (by rw [lo_xor, lo_append, lo_append, lo_append])
    (by rw [hi_xor, hi_append, hi_append, hi_append])

theorem xor_words (f g : Nat → BitVec 32) :
    xorBlock (ofWords f) (ofWords g) = ofWords fun i => f i ^^^ g i := by
  apply Vector.ext
  intro j hj
  simp only [xorBlock, ofWords, Vector.getElem_zipWith, Vector.getElem_ofFn, append_xor]

/-- A prefix of `n` 32-bit words at `B + o` holds `f`. -/
def Words (m : Mem) (B : BitVec 32) (o : Nat) (f : Nat → BitVec 32) (n : Nat) : Prop :=
  ∀ i < n, m.readW (A B (o + 4 * i)) 32 = f i

end VG.Proof.Argon2.Arm

end

end

/-! ### `Argon2.Arm.Compress`, which this module and modules that import it used -/

section

/-! ### `Argon2.Arm.CompressContract`, which this module and modules that import it used -/

section

/-!
# Argon2 compression on ARMv7: the contract of the proof

`compressArm`: the contract the proof is written against (and the derivation
uses for its calls); `Proof.Argon2.compressContract` implies it
(`Proof/Argon2/Arm/CompressVerified.lean`). `Pre` names the facts of its
precondition.
-/

@[expose] public section

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
  post s s' := blockAt s'.mem (State.addr (s.gpr .r2)) =
    compress (blockAt s.mem (State.addr (s.gpr .r0))) (blockAt s.mem (State.addr (s.gpr .r1)))
  pub s₁ s₂ := s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
    s₁.gpr .r3 = s₂.gpr .r3

section
variable (s₀ : State)

abbrev xp : BitVec 32 := s₀.gpr .r0
abbrev yp : BitVec 32 := s₀.gpr .r1
abbrev op : BitVec 32 := s₀.gpr .r2
abbrev scr : BitVec 32 := s₀.gpr .r3
abbrev xR : Region := ⟨State.addr (xp s₀), 1024⟩
abbrev yR : Region := ⟨State.addr (yp s₀), 1024⟩
abbrev outR : Region := ⟨State.addr (op s₀), 1024⟩
abbrev scrR : Region := ⟨State.addr (scr s₀), 4096⟩

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [xR s₀, yR s₀]
  wr : s₀.wr = [outR s₀, scrR s₀]
  out_scr : (outR s₀).Disjoint (scrR s₀)
  x_out : (xR s₀).Disjoint (outR s₀)
  x_scr : (xR s₀).Disjoint (scrR s₀)
  y_out : (yR s₀).Disjoint (outR s₀)
  y_scr : (yR s₀).Disjoint (scrR s₀)
  x_fits : (xp s₀).toNat + 1024 ≤ 2 ^ 32
  y_fits : (yp s₀).toNat + 1024 ≤ 2 ^ 32
  out_fits : (op s₀).toNat + 1024 ≤ 2 ^ 32
  scr_fits : (scr s₀).toNat + 4096 ≤ 2 ^ 32

theorem pre_of (s₀ : State) (h : compressArm.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

namespace Pre
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem scr_contains {d : Nat} (hd : d + 4 ≤ 4096) : (scrR s₀).Contains (A (scr s₀) d) 4 :=
  contains_A hp.scr_fits hd

theorem out_wr {s : State} (hw : s.wr = s₀.wr) {d : Nat} (hd : d + 4 ≤ 1024) :
    InRegions s.wr (A (op s₀) d) 4 :=
  ⟨outR s₀, by simp [hw, hp.wr], contains_A hp.out_fits hd⟩

theorem scr_wr {s : State} (hw : s.wr = s₀.wr) {d : Nat} (hd : d + 4 ≤ 4096) :
    InRegions s.wr (A (scr s₀) d) 4 :=
  ⟨scrR s₀, by simp [hw, hp.wr], contains_A hp.scr_fits hd⟩

theorem in_scr {s : State} (hw : s.wr = s₀.wr) {d : Nat} (hd : d + 4 ≤ 4096) :
    InRegions (s.rd ++ s.wr) (A (scr s₀) d) 4 :=
  VG.Proof.Sha512.Arm.mem_rd (hp.scr_wr hw hd)

theorem in_x {s : State} (hrd : s.rd = s₀.rd) {d : Nat} (hd : d + 4 ≤ 1024) :
    InRegions (s.rd ++ s.wr) (A (xp s₀) d) 4 :=
  ⟨xR s₀, by simp [hrd, hp.rd], contains_A hp.x_fits hd⟩

theorem in_y {s : State} (hrd : s.rd = s₀.rd) {d : Nat} (hd : d + 4 ≤ 1024) :
    InRegions (s.rd ++ s.wr) (A (yp s₀) d) 4 :=
  ⟨yR s₀, by simp [hrd, hp.rd], contains_A hp.y_fits hd⟩

/-- A word of `x` is unchanged while only `out` and `scratch` are written. -/
theorem x_frame {m : Mem} (hf : Frame [outR s₀, scrR s₀] s₀.mem m) {d : Nat} (hd : d + 4 ≤ 1024) :
    m.readW (A (xp s₀) d) 32 = s₀.mem.readW (A (xp s₀) d) 32 := by
  refine hf.readW (r := xR s₀) (contains_A hp.x_fits hd) ?_ (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨hp.x_out, hp.x_scr⟩

theorem y_frame {m : Mem} (hf : Frame [outR s₀, scrR s₀] s₀.mem m) {d : Nat} (hd : d + 4 ≤ 1024) :
    m.readW (A (yp s₀) d) 32 = s₀.mem.readW (A (yp s₀) d) 32 := by
  refine hf.readW (r := yR s₀) (contains_A hp.y_fits hd) ?_ (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨hp.y_out, hp.y_scr⟩

/-- A word of `scratch` is unchanged while only `out` is written. -/
theorem scr_frame {m m' : Mem} (hf : Frame [outR s₀] m m') {d : Nat} (hd : d + 4 ≤ 4096) :
    m'.readW (A (scr s₀) d) 32 = m.readW (A (scr s₀) d) 32 := by
  refine hf.readW (r := scrR s₀) (contains_A hp.scr_fits hd) ?_ (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]
  exact hp.out_scr.symm

end Pre

end VG.Proof.Argon2.Arm

end

end

/-! ### `Argon2.Arm.Pass`, which this module and modules that import it used -/

section

/-! ### `Argon2.Arm.Rounds`, which this module and modules that import it used -/

section

/-!
# Argon2 on ARMv7: the row and column permutations

As on x86 (`Proof/Argon2/X86/Rounds.lean`): P on any injectively selected
row or column (`permuteAt_ok`). The code addresses the words of `index₀` at
`r3`, which is `8e` bytes past the base `B`: it permutes those of `index`,
`e` words on. The passes over the rows and columns are in
`Proof/Argon2/Arm/CompressVerified.lean`.
-/

@[expose] public section

namespace VG.Proof.Argon2.Arm

open VG VG.Arm VG.Spec.Argon2
open VG.Proof.Argon2
open VG.Proof.Sha512.Arm (Reg64)

/-- The selected sixteen words and the unchanged words outside them. -/
def Holds (index : Fin 16 → Fin 128) (b : Block) (v : Vector Word 16) (m : Mem)
    (B : BitVec 32) : Prop :=
  gather index (working m B) = v ∧ ∀ k : Fin 128, (∀ j, index j ≠ k) → (working m B)[k] = b[k]

/-- The base and the permissions of `scratch`, with `r3` `8e` bytes past the base. -/
def At (B : BitVec 32) (e : Nat) (s : State) : Prop :=
  s.gpr .r3 = B + BitVec.ofNat 32 (8 * e) ∧ Reg64 s.wr B 2048

theorem At.of_step {B : BitVec 32} {e : Nat} {s t : State} {v : Block} (h : At B e s)
    (st : Step B s v t) : At B e t :=
  ⟨st.keep.r3.trans h.1, st.keep.wr ▸ h.2⟩

section
variable {B : BitVec 32} (hfit : B.toNat + 4096 ≤ 2 ^ 32)
  (index index₀ : Fin 16 → Fin 128) (e : Nat) (hidx : ∀ k, (index k).val = (index₀ k).val + e)

include hfit hidx

/-- One GB advances the selected row or column and preserves its complement:
the code GB on `index₀`, with `r3` `8e` bytes on, is GB on `index`. -/
theorem step_ok (hi : Function.Injective index) {s : State}
    (hs : At B e s) (base : Block) (v : Vector Word 16) (hv : Holds index base v s.mem B)
    (a b c d : Fin 16) (hab : a.val ≠ b.val) (hac : a.val ≠ c.val) (had : a.val ≠ d.val)
    (hbc : b.val ≠ c.val) (hbd : b.val ≠ d.val) (hcd : c.val ≠ d.val) :
    WP isa (Impl.Argon2.Arm.gbAt (index₀ a).val (index₀ b).val (index₀ c).val (index₀ d).val) s
      fun t => Holds index base (GB v a b c d) t.mem B ∧ ∃ w, Step B s w t := by
  refine (gbAt_ok hfit hs.1 hs.2 (index a) (index b) (index c) (index d)
    (hidx a) (hidx b) (hidx c) (hidx d)).mono fun t st => ?_
  refine ⟨⟨?_, ?_⟩, _, st⟩
  · rw [st.working, gather_mixWords index hi, hv.1, GB_eq_mixWords v hab hac had hbc hbd hcd]
  · intro k hn
    rw [st.working]
    have ne' (j : Fin 16) : (index j).val ≠ k.val := fun h => hn j (Fin.ext h)
    simp only [mixWords, Fin.getElem_fin, Vector.getElem_set, ne', ite_false]
    exact hv.2 k hn

/-- P on any injectively selected row or column. -/
theorem permuteAt_holds (hi : Function.Injective index) {s : State}
    (hs : At B e s) (base : Block) (v : Vector Word 16) (hv : Holds index base v s.mem B) :
    WP isa (Impl.Argon2.Arm.permuteAt index₀) s fun t =>
      Holds index base (permute v) t.mem B ∧ ∃ w, Step B s w t := by
  have advance (t : State) (v' : Vector Word 16)
      (h : Holds index base v' t.mem B ∧ ∃ w, Step B s w t)
      (a b c d : Fin 16)
      (hab : a.val ≠ b.val) (hac : a.val ≠ c.val) (had : a.val ≠ d.val)
      (hbc : b.val ≠ c.val) (hbd : b.val ≠ d.val) (hcd : c.val ≠ d.val) :
      WP isa (Impl.Argon2.Arm.gbAt (index₀ a).val (index₀ b).val (index₀ c).val (index₀ d).val)
        t fun u => Holds index base (GB v' a b c d) u.mem B ∧ ∃ w, Step B s w u := by
    obtain ⟨hh, w, st⟩ := h
    refine (step_ok hfit index index₀ e hidx hi (hs.of_step st) base v' hh a b c d
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
theorem permuteAt_ok (hi : Function.Injective index) {s : State} (hs : At B e s) :
    WP isa (Impl.Argon2.Arm.permuteAt index₀) s
      (Step B s (Spec.Argon2.permuteAt index (working s.mem B))) := by
  refine (permuteAt_holds hfit index index₀ e hidx hi hs (working s.mem B)
    (gather index (working s.mem B)) ⟨rfl, fun _ _ => rfl⟩).mono ?_
  rintro t ⟨ht, w, st⟩
  exact ⟨st.keep, eq_scatter index hi _ _ _ ht.1 ht.2, st.frame⟩

end

end VG.Proof.Argon2.Arm

end

end

/-!
# Argon2 on ARMv7: the loops over the rows and the columns

A pass (`Impl.Argon2.Arm.pass`) runs P on row (column) 0 at `r3`, moving
`r3` on to the next row (column) each time, eight times, counting down in the
word at `r3 + 2088`, which moves with `r3`. `iter_ok`: an iteration from
`Inv n` (`8 - n` rows or columns done) reaches `Inv (n - 1)`, with the flags
saying whether `n - 1` is zero; `pass_ok`: a pass permutes every row
(column) of the block at `B` and writes nothing outside the block and the
counts; `rounds_ok`: the rows, then the columns.

Constant time (`pass_ct`): the taint analysis proves that each piece's
addresses depend only on `r3`, which both runs agree on, and the loop's
branches agree since the count is the same in both runs (`RelCT.loop`).
-/

@[expose] public section

namespace VG.Proof.Argon2.Arm

open VG VG.Arm VG.Spec.Argon2
open VG.Impl.Argon2.Arm (pass next ctrOff permuteAt wOff)
open VG.Proof.Sha512.Arm (A A_eq Reg64 rd64 mem_rd)
open VG.Proof.MdStream.Arm (Upd Mupd Fupd wp_ldr wp_str wp_mov wp_add wp_sub wp_cmp op2_imm)

/-- The words in which the passes keep their counts. -/
abbrev ctrR (B : BitVec 32) : Region := ⟨State.addr B + BitVec.ofNat 64 2088, 2008⟩

/-- `scratch` at `B`: within the address space, and writable. -/
structure Scr (B : BitVec 32) (wr : List Region) : Prop where
  fit : B.toNat + 4096 ≤ 2 ^ 32
  wr : ∀ o, o + 4 ≤ 4096 → InRegions wr (A B o) 4

theorem Scr.reg64 {B : BitVec 32} {wr : List Region} (h : Scr B wr) : Reg64 wr B 2048 :=
  fun o ho => ⟨h.wr o (by omega_using [ho]), h.wr (o + 4) (by omega_using [ho])⟩

section
variable {B : BitVec 32} (hfit : B.toNat + 4096 ≤ 2 ^ 32)
include hfit

/-- A word of `scratch` outside the regions a pass writes is unchanged. -/
theorem outside_pass {m m' : Mem} (hf : Frame [permR B, ctrR B] m m') {d : Nat} (hd : d + 4 ≤ 1024 ∨
    (2048 ≤ d ∧ d + 4 ≤ 2088)) : m'.readW (A B d) 32 = m.readW (A B d) 32 := by
  refine hf.readW (r := ⟨A B d, 4⟩) (Region.contains_self _ _) ?_ (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  rw [A_eq (by omega_using [hfit, hd])]
  exact ⟨Offset.disjoint _ (by omega_using [hd]) (by omega_using [hd]) (by omega_using []),
    Offset.disjoint _ (by omega_using [hd]) (by omega_using [hd]) (by omega_using [])⟩

/-- A word of `scratch` beyond the permuted block is unchanged by its writes. -/
theorem outside_perm {m m' : Mem} (hf : Frame [permR B] m m') {d : Nat} (hd : 2048 ≤ d)
    (hd' : d + 4 ≤ 4096) : m'.readW (A B d) 32 = m.readW (A B d) 32 := by
  refine hf.readW (r := ⟨A B d, 4⟩) (Region.contains_self _ _) ?_ (by decide)
  simp only [List.mem_singleton, forall_eq]
  rw [A_eq (by omega_using [hfit, hd'])]
  exact Offset.disjoint _ (by omega_using [hd]) (by omega_using [hd']) (by omega_using [])

/-- The permuted block is unchanged by writes to the counts. -/
theorem working_ctr {m m' : Mem} (hf : Frame [ctrR B] m m') : working m' B = working m B := by
  apply Vector.ext
  intro j hj
  have rd (o : Nat) (ho : o + 4 ≤ 2048) : m'.readW (A B o) 32 = m.readW (A B o) 32 := by
    refine hf.readW (r := ⟨A B o, 4⟩) (Region.contains_self _ _) ?_ (by decide)
    simp only [List.mem_singleton, forall_eq]
    rw [A_eq (by omega_using [hfit, ho])]
    exact Offset.disjoint _ (by omega_using [ho]) (by omega_using [ho]) (by omega_using [])
  simp only [working, Vector.getElem_ofFn, rd64, wOff]
  rw [rd _ (by omega_using [hj]), rd _ (by omega_using [hj])]

/-- The count at `B + o` is written within the counts. -/
theorem ctr_contains {o : Nat} (ho : 2088 ≤ o) (ho' : o + 4 ≤ 4096) : (ctrR B).Contains (A B o) 4 := by
  rw [A_eq (by omega_using [hfit, ho'])]
  exact Offset.contains _ ho (by omega_using [ho']) (by omega_using [])

end

/-! ## A pass -/

/-- What a pass needs of the row or column `index i` it permutes in iteration
`i`: they are injective, and `sh * i` words on from those of iteration 0. -/
structure PassOk (index : Fin 8 → Fin 16 → Fin 128) (sh : Nat) : Prop where
  inj : ∀ i, Function.Injective (index i)
  idx : ∀ i k, (index i k).val = (index 0 k).val + sh * i.val
  le : sh ≤ 16
  enc : encodable (BitVec.ofNat 32 (8 * sh)) = true
  enc8 : encodable (BitVec.ofNat 32 (8 * (8 * sh))) = true

theorem rows_ok : PassOk rowIndex 16 :=
  ⟨Proof.Argon2.rowIndex_injective, fun i k => by simp only [rowIndex]; omega_using [], by decide, by decide,
    by decide⟩

theorem cols_ok : PassOk colIndex 2 :=
  ⟨Proof.Argon2.colIndex_injective, fun i k => by simp only [colIndex]; omega_using [], by decide, by decide,
    by decide⟩

theorem foldl_take_succ {α : Type} (f : α → Fin 8 → α) (x : α) {j : Nat} (hj : j < 8) :
    ((List.finRange 8).take (j + 1)).foldl f x = f (((List.finRange 8).take j).foldl f x) ⟨j, hj⟩ := by
  rw [List.take_add_one, List.foldl_append, List.getElem?_eq_getElem (by simpa using hj)]
  simp

theorem off_le {sh j : Nat} (hsh : sh ≤ 16) (hj : j ≤ 8) : sh * j ≤ 128 :=
  Nat.le_trans (Nat.mul_le_mul hsh hj) (by decide)

section
variable (index : Fin 8 → Fin 16 → Fin 128) (sh : Nat) (s₀ : State)

/-- After `8 - n` iterations of a pass from `s₀`, with `n` left. -/
structure Inv (n : Nat) (s : State) : Prop where
  le : n ≤ 8
  r3 : s.gpr .r3 = s₀.gpr .r3 + BitVec.ofNat 32 (8 * (sh * (8 - n)))
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  ctr : s.mem.readW (A (s₀.gpr .r3) (8 * (sh * (8 - n)) + ctrOff)) 32 = BitVec.ofNat 32 n
  working : working s.mem (s₀.gpr .r3) = ((List.finRange 8).take (8 - n)).foldl
    (fun b i => Spec.Argon2.permuteAt (index i) b) (working s₀.mem (s₀.gpr .r3))
  frame : Frame [permR (s₀.gpr .r3), ctrR (s₀.gpr .r3)] s₀.mem s.mem

end

/-- What a pass leaves: `r3` and the regions as they were, the block at `B`
permuted to `v`, and nothing written outside it and the counts. -/
structure Passed (B : BitVec 32) (s : State) (v : Block) (t : State) : Prop where
  r3 : t.gpr .r3 = s.gpr .r3
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  working : working t.mem B = v
  frame : Frame [permR B, ctrR B] s.mem t.mem

theorem Passed.trans {B : BitVec 32} {s t u : State} {v w : Block} (h : Passed B s v t)
    (h' : Passed B t w u) : Passed B s w u :=
  ⟨h'.r3.trans h.r3, h'.rd.trans h.rd, h'.wr.trans h.wr, h'.sp.trans h.sp, h'.working,
    h.frame.trans h'.frame⟩

theorem count_sub : ∀ n < 9, 1 ≤ n → BitVec.ofNat 32 n - 1 = BitVec.ofNat 32 (n - 1) := by decide

theorem count_ne : ∀ n < 9, 1 ≤ n →
    (!(BitVec.ofNat 32 (n - 1) - 0 == 0)) = decide (n - 1 ≠ 0) := by decide

theorem finish_r3 (sh : Nat) (x : BitVec 32) :
    x + BitVec.ofNat 32 (8 * (sh * (8 - 0))) - BitVec.ofNat 32 (8 * (8 * sh)) = x := by
  rw [Nat.sub_zero, Nat.mul_comm sh 8, BitVec.add_sub_cancel]

section
variable {index : Fin 8 → Fin 16 → Fin 128} {sh : Nat} (hP : PassOk index sh) {s₀ : State}
  (hs : Scr (s₀.gpr .r3) s₀.wr)
include hP hs

/-- One iteration of a pass, from `n ≥ 1` rows or columns left. -/
theorem iter_ok {n : Nat} (hn : 1 ≤ n) {s : State} (h : Inv index sh s₀ n s) :
    WP isa (.seq (permuteAt (index 0)) (.block (next (8 * sh)))) s fun t =>
      Inv index sh s₀ (n - 1) t ∧ isa.eval .ne t = some (decide (n - 1 ≠ 0)) := by
  have fit := hs.fit
  have hle := h.le
  have hsh := hP.le
  have hi : 8 - n < 8 := by omega_using [hn]
  have o₀ := off_le hsh (Nat.sub_le 8 n)
  have o₁ := off_le hsh (Nat.sub_le 8 (n - 1))
  have e₁ : 8 * (sh * (8 - n)) + 8 * sh = 8 * (sh * (8 - (n - 1))) := by
    rw [show 8 - (n - 1) = 8 - n + 1 by omega_using [hn, hle], Nat.mul_succ, Nat.mul_add]
  apply WP.seq
  refine (permuteAt_ok fit (index ⟨8 - n, hi⟩) (index 0) (sh * (8 - n)) (hP.idx _) (hP.inj _)
    ⟨h.r3, by rw [h.wr]; exact hs.reg64⟩).mono fun t st => ?_
  have k := st.keep
  have r3t : t.gpr .r3 = s₀.gpr .r3 + BitVec.ofNat 32 (8 * (sh * (8 - n))) := k.r3.trans h.r3
  unfold next
  refine wp_ldr (a := A (s₀.gpr .r3) (8 * (sh * (8 - n)) + ctrOff)) (by decide)
    (by rw [r3t]; exact A_shift _ _ _)
    (mem_rd (by rw [k.wr, h.wr]; exact hs.wr _ (by simp only [ctrOff]; omega_using [o₀]))) fun t₁ u₁ => ?_
  refine wp_sub (op2_imm (by decide)) fun t₂ u₂ => ?_
  refine wp_add (op2_imm hP.enc) fun t₃ u₃ => ?_
  have r3₃ : t₃.gpr .r3 = s₀.gpr .r3 + BitVec.ofNat 32 (8 * (sh * (8 - (n - 1)))) := by
    rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), r3t, BitVec.add_assoc,
      ← BitVec.ofNat_add, e₁]
  refine wp_str (a := A (s₀.gpr .r3) (8 * (sh * (8 - (n - 1))) + ctrOff)) (by decide)
    (by rw [r3₃]; exact A_shift _ _ _)
    (by rw [u₃.wr, u₂.wr, u₁.wr, k.wr, h.wr]; exact hs.wr _ (by simp only [ctrOff]; omega_using [o₁]))
    fun t₄ u₄ => ?_
  refine wp_cmp (op2_imm (by decide)) fun t₅ u₅ hz => WP.block_nil ?_
  have v₁ : t₁.gpr .r0 = BitVec.ofNat 32 n := by
    rw [u₁.gpr, outside_perm fit st.frame (by simp only [ctrOff]; omega_using []) (by simp only [ctrOff]; omega_using [o₀]),
      h.ctr]
  have v₃ : t₃.gpr .r0 = BitVec.ofNat 32 (n - 1) := by
    rw [u₃.other _ (by decide), u₂.gpr, v₁, count_sub n (by omega_using [hle]) hn]
  have m₅ : t₅.mem = t.mem.writeW (A (s₀.gpr .r3) (8 * (sh * (8 - (n - 1))) + ctrOff))
      (BitVec.ofNat 32 (n - 1)) := by
    rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem, v₃]
  have cf : Frame [ctrR (s₀.gpr .r3)] t.mem t₅.mem := by
    rw [m₅]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (ctr_contains fit (by simp only [ctrOff]; omega_using []) (by simp only [ctrOff]; omega_using [o₁]))
  refine ⟨⟨by omega_using [hle], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [u₅.gpr, u₄.gpr, r3₃]
  · rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, k.rd, h.rd]
  · rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, k.wr, h.wr]
  · rw [u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, k.sp, h.sp]
  · rw [m₅, Mem.readW_writeW_self32]
  · rw [working_ctr fit cf, st.working, h.working, show 8 - (n - 1) = 8 - n + 1 by omega_using [hn, hle],
      foldl_take_succ _ _ hi]
  · rw [m₅]
    exact (h.frame.trans (st.frame.mono (by simp))).writeW (by simp) _
      (ctr_contains fit (by simp only [ctrOff]; omega_using []) (by simp only [ctrOff]; omega_using [o₁]))
  · show some (!t₅.z) = _
    rw [hz, u₄.gpr, v₃, count_ne n (by omega_using [hle]) hn]

omit hP in
/-- The start of a pass: eight rows or columns left. -/
theorem start_ok :
    WP isa (.block [.mov .r0 (.imm 8), .str .r0 .r3 ctrOff]) s₀ (Inv index sh s₀ 8) := by
  have fit := hs.fit
  refine wp_mov (op2_imm (by decide)) fun t₁ u₁ => ?_
  refine wp_str (by decide) (by rw [u₁.other _ (by decide)]) (by rw [u₁.wr]; exact hs.wr _ (by decide))
    fun t₂ u₂ => WP.block_nil ?_
  have m₂ : t₂.mem = s₀.mem.writeW (A (s₀.gpr .r3) ctrOff) (BitVec.ofNat 32 8) := by
    rw [u₂.mem, u₁.mem, u₁.gpr]; rfl
  have z : 8 * (sh * (8 - 8)) = 0 := by simp
  have cf : Frame [ctrR (s₀.gpr .r3)] s₀.mem t₂.mem := by
    rw [m₂]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (ctr_contains fit (by decide) (by decide))
  refine ⟨by decide, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₂.gpr, u₁.other _ (by decide), z]; exact (BitVec.add_zero _).symm
  · rw [u₂.rd, u₁.rd]
  · rw [u₂.wr, u₁.wr]
  · rw [u₂.sp, u₁.sp]
  · rw [m₂, z, Nat.zero_add, Mem.readW_writeW_self32]
  · rw [working_ctr fit cf]; rfl
  · rw [m₂]
    exact (Frame.refl _ _).writeW (by simp) _ (ctr_contains fit (by decide) (by decide))

/-- The loop of a pass, from the start. -/
theorem loop_ok {s : State} (h : Inv index sh s₀ 8 s) :
    WP isa (.loop (.seq (permuteAt (index 0)) (.block (next (8 * sh)))) .ne) s (Inv index sh s₀ 0) := by
  have step (n : Nat) (u : State) (hu : Inv index sh s₀ n u ∧ 1 ≤ n) :
      WP isa (.seq (permuteAt (index 0)) (.block (next (8 * sh)))) u fun t =>
        (isa.eval .ne t = some false ∧ Inv index sh s₀ 0 t) ∨
        (isa.eval .ne t = some true ∧ ∃ m < n, Inv index sh s₀ m t ∧ 1 ≤ m) := by
    refine (iter_ok hP hs hu.2 hu.1).mono fun t ⟨ht, he⟩ => ?_
    by_cases hz : n - 1 = 0
    · simp only [hz, ne_eq, not_true_eq_false, decide_false] at he
      exact .inl ⟨he, hz ▸ ht⟩
    · simp only [hz, ne_eq, not_false_eq_true, decide_true] at he
      exact .inr ⟨he, n - 1, by omega_using [hz], ht, by omega_using [hz]⟩
  exact VG.WP.loop (M := isa) (fun (n : Nat) (u : State) => Inv index sh s₀ n u ∧ 1 ≤ n) step 8 s
    ⟨h, by decide⟩

/-- A pass permutes every row (column), and writes nothing outside the block
and the counts. -/
theorem pass_ok :
    WP isa (pass (index 0) (8 * sh)) s₀ (Passed (s₀.gpr .r3) s₀
      ((List.finRange 8).foldl (fun b i => Spec.Argon2.permuteAt (index i) b)
        (working s₀.mem (s₀.gpr .r3)))) := by
  unfold pass
  refine WP.seq ((start_ok hs).mono fun s₁ h₁ => WP.seq ((loop_ok hP hs h₁).mono fun s₂ h₂ => ?_))
  refine wp_sub (op2_imm hP.enc8) fun t u => WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u.gpr, h₂.r3, finish_r3 sh _]
  · rw [u.rd, h₂.rd]
  · rw [u.wr, h₂.wr]
  · rw [u.sp, h₂.sp]
  · rw [u.mem, h₂.working, Nat.sub_zero, List.take_of_length_le (by simp)]
  · rw [u.mem]; exact h₂.frame

end

/-- The rows, then the columns. -/
theorem rounds_ok {s : State} (hs : Scr (s.gpr .r3) s.wr) :
    WP isa Impl.Argon2.Arm.rounds s (Passed (s.gpr .r3) s
      ((List.finRange 8).foldl (fun b i => Spec.Argon2.permuteAt (colIndex i) b)
        ((List.finRange 8).foldl (fun b i => Spec.Argon2.permuteAt (rowIndex i) b)
          (working s.mem (s.gpr .r3))))) := by
  show WP isa (.seq (pass (rowIndex 0) (8 * 16)) (pass (colIndex 0) (8 * 2))) s _
  refine WP.seq ((pass_ok rows_ok hs).mono fun t ht => ?_)
  have hs' : Scr (t.gpr .r3) t.wr := by rw [ht.r3, ht.wr]; exact hs
  refine (pass_ok cols_ok hs').mono fun u hu => ?_
  rw [ht.r3, ht.working] at hu
  exact ht.trans hu

/-! ## Constant time -/

/-- Two runs on the same `scratch`. -/
def PassRel (s₁ s₂ : State) : Prop :=
  s₁.gpr .r3 = s₂.gpr .r3 ∧ Scr (s₁.gpr .r3) s₁.wr ∧ Scr (s₂.gpr .r3) s₂.wr

section
variable {index : Fin 8 → Fin 16 → Fin 128} {sh : Nat} (hP : PassOk index sh)
include hP

/-- Two runs of a pass leak the same, given that the taint analysis proves
that the addresses of the loop's body and of the end of the pass depend only
on `r3`. -/
theorem pass_ct
    (hbody : ∃ hc, (VG.Taint.check taint (VG.Arm.Taint.ofRegs [.r3])
      (.seq (permuteAt (index 0)) (.block (next (8 * sh)))) hc).isSome = true)
    (hfin : ∃ hc, (VG.Taint.check taint (VG.Arm.Taint.ofRegs [.r3])
      (.block [.dp .sub .r3 .r3 (.imm (BitVec.ofNat 32 (8 * (8 * sh))))]) hc).isSome = true) :
    RelCT isa PassRel (pass (index 0) (8 * sh)) PassRel := by
  obtain ⟨_, hbody⟩ := hbody
  obtain ⟨_, hfin⟩ := hfin
  unfold pass
  let I (n : Nat) (s₁ s₂ : State) : Prop :=
    ∃ σ₁ σ₂, PassRel σ₁ σ₂ ∧ Inv index sh σ₁ n s₁ ∧ Inv index sh σ₂ n s₂
  have agree {n : Nat} {σ₁ σ₂ : State} (hp : PassRel σ₁ σ₂) (s₁ s₂ : State)
      (h : Inv index sh σ₁ n s₁ ∧ Inv index sh σ₂ n s₂) :
      VG.Arm.Taint.Agree (VG.Arm.Taint.ofRegs [.r3]) s₁ s₂ :=
    VG.Arm.Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h.1.r3, h.2.r3, hp.1]
  -- The start.
  have hstart : RelCT isa PassRel (.block [.mov .r0 (.imm 8), .str .r0 .r3 ctrOff]) (I 8) := by
    have ct : RelCT isa PassRel (.block [.mov .r0 (.imm 8), .str .r0 .r3 ctrOff]) fun _ _ => True :=
      RelCT.taint (A := taint) (VG.Arm.Taint.ofRegs [.r3]) (fun s₁ s₂ h => VG.Arm.Taint.agree_ofRegs
        fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h.1) (by taint_decide)
    refine (ct.wpDep (F := fun σ => Inv index sh σ 8)
      fun s₁ s₂ h => ⟨start_ok h.2.1, start_ok h.2.2⟩).mono (fun _ _ h => h) ?_
    rintro s₁ s₂ ⟨-, σ₁, σ₂, hp, i₁, i₂⟩
    exact ⟨σ₁, σ₂, hp, i₁, i₂⟩
  -- The loop.
  have hloop : RelCT isa (I 8) (.loop (.seq (permuteAt (index 0)) (.block (next (8 * sh)))) .ne)
      (I 0) := by
    refine (RelCT.loop (fun n s₁ s₂ => I n s₁ s₂ ∧ 1 ≤ n) (fun n => ?_) 8).mono
      (fun s₁ s₂ h => ⟨h, by decide⟩) (fun _ _ h => h)
    intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨⟨σ₁, σ₂, hp, i₁, i₂⟩, hn⟩ e₁ e₂
    have ct := (RelCT.taint (A := taint)
      (P := fun s₁ s₂ => Inv index sh σ₁ n s₁ ∧ Inv index sh σ₂ n s₂) (VG.Arm.Taint.ofRegs [.r3])
      (agree hp) hbody).wp
      (F₁ := fun t => Inv index sh σ₁ (n - 1) t ∧ isa.eval .ne t = some (decide (n - 1 ≠ 0)))
      (F₂ := fun t => Inv index sh σ₂ (n - 1) t ∧ isa.eval .ne t = some (decide (n - 1 ≠ 0)))
      (fun _ _ h => ⟨iter_ok hP hp.2.1 hn h.1, iter_ok hP hp.2.2 hn h.2⟩)
    obtain ⟨ht, -, ⟨j₁, c₁⟩, ⟨j₂, c₂⟩⟩ := ct _ _ _ _ _ _ ⟨i₁, i₂⟩ e₁ e₂
    refine ⟨ht, by rw [c₁, c₂], fun hf => ?_, fun htr => ?_⟩
    · rw [c₁] at hf
      have hz : n - 1 = 0 := by simpa using hf
      exact ⟨σ₁, σ₂, hp, hz ▸ j₁, hz ▸ j₂⟩
    · rw [c₁] at htr
      have hz : n - 1 ≠ 0 := by simpa using htr
      exact ⟨n - 1, by omega_using [hn], ⟨σ₁, σ₂, hp, j₁, j₂⟩, by omega_using [hz]⟩
  -- The end.
  have hend : RelCT isa (I 0)
      (.block [.dp .sub .r3 .r3 (.imm (BitVec.ofNat 32 (8 * (8 * sh))))]) PassRel := by
    intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨σ₁, σ₂, hp, i₁, i₂⟩ e₁ e₂
    have fin_ok {σ s : State} (i : Inv index sh σ 0 s) :
        WP isa (.block [.dp .sub .r3 .r3 (.imm (BitVec.ofNat 32 (8 * (8 * sh))))]) s
          fun t => t.gpr .r3 = σ.gpr .r3 ∧ t.wr = σ.wr :=
      wp_sub (op2_imm hP.enc8) fun t u => WP.block_nil
        ⟨by rw [u.gpr, i.r3, finish_r3 sh _], by rw [u.wr, i.wr]⟩
    have ct := (RelCT.taint (A := taint)
      (P := fun s₁ s₂ => Inv index sh σ₁ 0 s₁ ∧ Inv index sh σ₂ 0 s₂) (VG.Arm.Taint.ofRegs [.r3])
      (agree hp) hfin).wp (fun _ _ h => ⟨fin_ok h.1, fin_ok h.2⟩)
    obtain ⟨ht, -, ⟨a₁, w₁⟩, ⟨a₂, w₂⟩⟩ := ct _ _ _ _ _ _ ⟨i₁, i₂⟩ e₁ e₂
    refine ⟨ht, by rw [a₁, a₂, hp.1], ?_, ?_⟩
    · rw [a₁, w₁]; exact hp.2.1
    · rw [a₂, w₂]; exact hp.2.2
  exact hstart.seq (hloop.seq hend)

end

/-- The rows, then the columns. -/
theorem rounds_ct : RelCT isa PassRel Impl.Argon2.Arm.rounds PassRel := by
  show RelCT isa PassRel (.seq (pass (rowIndex 0) (8 * 16)) (pass (colIndex 0) (8 * 2))) PassRel
  exact (pass_ct rows_ok ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩).seq
    (pass_ct cols_ok ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩)

end VG.Proof.Argon2.Arm

end

end

/-!
# Argon2 compression on ARMv7: correctness

The prologue saving the caller's registers and `out` (`prologue_ok`), the
initialization of both halves of scratch with X XOR Y (`init_ok`, one word at
a time), the rows and columns (`Proof/Argon2/Arm/CompressVerified.lean`), and the
epilogue writing the output and restoring the registers: `correct`.
-/

@[expose] public section

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
  rw [A_eq (by omega_arith), A_eq (by omega_arith)]
  exact readW_writeW_save m _ v (by omega_arith) (by omega_arith) h

theorem spill_slots : Spill.Slots 2048 2088 spill := by decide

theorem saved_slots : Spill.Slots 2048 2084 saved := by decide

theorem saved_restorable : Spill.Restorable .r3 saved := by decide

/-- 32-bit word `i` of X XOR Y. -/
def xy (s₀ : State) (i : Nat) : BitVec 32 :=
  s₀.mem.readW (A (xp s₀) (4 * i)) 32 ^^^ s₀.mem.readW (A (yp s₀) (4 * i)) 32

/-- After the prologue and the first `n` words of the initialization. -/
structure InitInv (s₀ s : State) (n : Nat) : Prop where
  regs : ∀ r, r ≠ .r4 → r ≠ .r5 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [scrR s₀] s₀.mem s.mem
  saved : Spill.Saved s.mem (State.addr (scr s₀)) s₀.gpr spill
  low : Words s.mem (scr s₀) 0 (xy s₀) n
  high : Words s.mem (scr s₀) 1024 (xy s₀) n

section
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem prologue_ok {rest : List Instr} {Q : State → Prop} (k : ∀ s, InitInv s₀ s 0 → WP isa (.block rest) s Q) :
    WP isa (.block (prologue ++ rest)) s₀ Q := by
  have fits := hp.scr_fits
  unfold prologue
  refine Spill.save_slots_ok spill_slots (by show (scr s₀).toNat + 2088 ≤ _; omega_arith) (fun d h₁ h₂ => ?_) (k _ ⟨fun _ _ _ => rfl, rfl, rfl, rfl,
    ?_, Spill.saveMem_saved _ _ _ _ spill_slots, fun i hi => absurd hi (Nat.not_lt_zero _),
    fun i hi => absurd hi (Nat.not_lt_zero _)⟩)
  · exact ⟨scrR s₀, by simp [hp.wr], Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  · exact Spill.saveMem_frame_of _ _ (List.mem_singleton_self _) _ _ fun p hpm => by
      have := spill_slots.bound hpm
      exact Offset.contains_base _ (by omega_arith) (by omega_arith)

/-- One word of the initialization. -/
theorem initWord_ok {s : State} {n : Nat} (hn : n < 256) (h : InitInv s₀ s n) :
    WP isa (.block (initWord n)) s (InitInv s₀ · (n + 1)) := by
  have hm : scrR s₀ ∈ [scrR s₀] := List.mem_singleton_self _
  have fits := hp.scr_fits
  unfold initWord
  refine wp_ldr (by omega_arith) (by rw [h.regs _ (by decide) (by decide)]) (hp.in_x h.rd (by omega_arith)) fun s₁ u₁ => ?_
  refine wp_ldr (by omega_arith) (by rw [u₁.other _ (by decide), h.regs _ (by decide) (by decide)])
    (by rw [u₁.rd, u₁.wr]; exact hp.in_y h.rd (by omega_arith)) fun s₂ u₂ => ?_
  refine wp_eor (op2_reg _ _) fun s₃ u₃ => ?_
  have v₃ : s₃.gpr .r4 = xy s₀ n := by
    rw [u₃.gpr, u₂.other _ (by decide), u₁.gpr, u₂.gpr, u₁.mem,
      hp.x_frame (h.frame.mono (by simp)) (by omega_arith), hp.y_frame (h.frame.mono (by simp)) (by omega_arith)]; rfl
  have r3 : s₃.gpr .r3 = scr s₀ := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.regs _ (by decide) (by decide)]
  refine wp_str (by omega_arith) (by rw [r3]) (by rw [u₃.wr, u₂.wr, u₁.wr, h.wr]; exact hp.scr_wr rfl (by omega_arith))
    fun s₄ u₄ => ?_
  refine wp_str (by omega_arith) (by rw [u₄.gpr, r3])
    (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr]; exact hp.scr_wr rfl (by omega_arith)) fun s₅ u₅ => WP.block_nil ?_
  have m₅ : s₅.mem = (s.mem.writeW (A (scr s₀) (4 * n)) (xy s₀ n)).writeW (A (scr s₀) (1024 + 4 * n)) (xy s₀ n) := by
    rw [u₅.mem, u₄.gpr, u₄.mem, u₃.mem, u₂.mem, u₁.mem, v₃]
  have r₅ : ∀ e, e + 4 ≤ 4096 → (e + 4 ≤ 4 * n ∨ 4 * n + 4 ≤ e) →
      (e + 4 ≤ 1024 + 4 * n ∨ 1024 + 4 * n + 4 ≤ e) →
      s₅.mem.readW (A (scr s₀) e) 32 = s.mem.readW (A (scr s₀) e) 32 := by
    intro e he h1 h2
    rw [m₅, readW_writeW_A _ _ (by omega_arith) (by omega_arith) h2, readW_writeW_A _ _ (by omega_arith) (by omega_arith) h1]
  refine ⟨fun r h4 h5 => ?_, ?_, ?_, ?_, ?_, fun p hpm => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · rw [u₅.gpr, u₄.gpr, u₃.other _ h4, u₂.other _ h5, u₁.other _ h4, h.regs r h4 h5]
  · rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd]
  · rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr]
  · rw [u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, h.sp]
  · rw [m₅]
    exact (h.frame.writeW hm _ (hp.scr_contains (by omega_arith))).writeW hm _ (hp.scr_contains (by omega_arith))
  · have := spill_slots.bound hpm
    have e := r₅ p.2 (by omega_arith) (by omega_arith) (by omega_arith)
    rw [A_eq (by omega_arith)] at e
    rw [e]; exact h.saved p hpm
  · by_cases e : i = n
    · subst e
      rw [m₅, readW_writeW_A _ _ (by omega_arith) (by omega_arith) (by omega_arith), Nat.zero_add, Mem.readW_writeW_self32]
    · rw [r₅ _ (by omega_arith) (by omega_arith) (by omega_arith)]; exact h.low i (by omega_arith)
  · by_cases e : i = n
    · subst e; rw [m₅, Mem.readW_writeW_self32]
    · rw [r₅ _ (by omega_arith) (by omega_arith) (by omega_arith)]; exact h.high i (by omega_arith)

theorem init_ok {s : State} (h : InitInv s₀ s 0) (n : Nat) (hn : n ≤ 256) :
    WP isa (.block ((List.range n).flatMap initWord)) s (InitInv s₀ · n) := by
  induction n with
  | zero => exact WP.block_nil h
  | succ n ih =>
    simp only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
    exact WP.block_append ((ih (by omega_arith)).mono fun t ht => initWord_ok hp (by omega_arith) ht)

end

/-! ## The epilogue -/

/-- Word `i` of the output: the permuted block XOR R, in memory `m`. -/
def outWord (B : BitVec 32) (m : Mem) (i : Nat) : BitVec 32 :=
  m.readW (A B (1024 + 4 * i)) 32 ^^^ m.readW (A B (4 * i)) 32

/-- After the first `n` words of the output, from the state `s₄` after the rounds. -/
structure FinInv (s₀ s₄ s : State) (n : Nat) : Prop where
  r3 : s.gpr .r3 = scr s₀
  r2 : s.gpr .r2 = op s₀
  regs : ∀ r, r ≠ .r4 → r ≠ .r5 → r ≠ .r2 → s.gpr r = s₄.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [outR s₀] s₄.mem s.mem
  out : Words s.mem (op s₀) 0 (outWord (scr s₀) s₄.mem) n

section
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem finishWord_ok {s₄ s : State} {n : Nat} (hn : n < 256) (h : FinInv s₀ s₄ s n) :
    WP isa (.block (finishWord n)) s (FinInv s₀ s₄ · (n + 1)) := by
  have hm : outR s₀ ∈ [outR s₀] := List.mem_singleton_self _
  have fits := hp.out_fits
  have sfits := hp.scr_fits
  unfold finishWord
  refine wp_ldr (by omega_arith) (by rw [h.r3]) (hp.in_scr h.wr (by omega_arith)) fun s₁ u₁ => ?_
  refine wp_ldr (by omega_arith) (by rw [u₁.other .r3 (by decide), h.r3])
    (by rw [u₁.rd, u₁.wr]; exact hp.in_scr h.wr (by omega_arith)) fun s₂ u₂ => ?_
  refine wp_eor (op2_reg _ _) fun s₃ u₃ => ?_
  have v₃ : s₃.gpr .r4 = outWord (scr s₀) s₄.mem n := by
    rw [u₃.gpr, u₂.other _ (by decide), u₁.gpr, u₂.gpr, u₁.mem, hp.scr_frame h.frame (by omega_arith),
      hp.scr_frame h.frame (by omega_arith)]; rfl
  refine wp_str (by omega_arith) (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.r2])
    (by rw [u₃.wr, u₂.wr, u₁.wr]; exact hp.out_wr h.wr (by omega_arith)) fun s₄' u₄ => WP.block_nil ?_
  have m₄ : s₄'.mem = s.mem.writeW (A (op s₀) (4 * n)) (outWord (scr s₀) s₄.mem n) := by
    rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem, v₃]
  refine ⟨?_, ?_, fun r h4 h5 h2 => ?_, ?_, ?_, ?_, ?_, fun i hi => ?_⟩
  · rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.r3]
  · rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.r2]
  · rw [u₄.gpr, u₃.other _ h4, u₂.other _ h5, u₁.other _ h4, h.regs r h4 h5 h2]
  · rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd]
  · rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr]
  · rw [u₄.sp, u₃.sp, u₂.sp, u₁.sp, h.sp]
  · rw [m₄]; exact h.frame.writeW hm _ (contains_A fits (by omega_arith))
  · rw [m₄]
    by_cases e : i = n
    · subst e; rw [Nat.zero_add, Mem.readW_writeW_self32]
    · rw [readW_writeW_A _ _ (by omega_arith) (by omega_arith) (by omega_arith)]
      exact h.out i (by omega_arith)

theorem finish_ok {s₄ s : State} (h : FinInv s₀ s₄ s 0) (n : Nat) (hn : n ≤ 256) :
    WP isa (.block ((List.range n).flatMap finishWord)) s (FinInv s₀ s₄ · n) := by
  induction n with
  | zero => exact WP.block_nil h
  | succ n ih =>
    simp only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
    exact WP.block_append ((ih (by omega_arith)).mono fun t ht => finishWord_ok hp (by omega_arith) ht)

end

/-! ## The whole function -/

theorem low_pass {B : BitVec 32} (hfit : B.toNat + 4096 ≤ 2 ^ 32) {m m' : Mem}
    (hf : Frame [permR B, ctrR B] m m') : blk m' B 0 = blk m B 0 := by
  apply Vector.ext
  intro j hj
  simp only [blk, Vector.getElem_ofFn, rd64]
  rw [outside_pass hfit hf (by omega_arith), outside_pass hfit hf (by omega_arith)]

theorem words_zero {m : Mem} {B : BitVec 32} {f : Nat → BitVec 32} (h : Words m B 0 f 256) :
    blk m B 0 = ofWords f := blk_of_words fun i hi => h i hi

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa Impl.Argon2.Arm.compress s₀ fun t =>
      (∀ r ∈ preserved, t.gpr r = s₀.gpr r) ∧ compressArm.post s₀ t := by
  have fits := hp.scr_fits
  unfold Impl.Argon2.Arm.compress
  refine WP.seq (prologue_ok hp fun s₁ h₁ => (init_ok hp h₁ 256 (Nat.le_refl _)).mono fun s₂ h₂ => ?_)
  have S₂ : Scr (s₂.gpr .r3) s₂.wr := by
    rw [h₂.regs _ (by decide) (by decide), h₂.wr]
    exact ⟨fits, fun o ho => hp.scr_wr rfl ho⟩
  refine WP.seq ((rounds_ok S₂).mono fun s₄ st₄ => ?_)
  rw [h₂.regs _ (by decide) (by decide)] at st₄
  have pf := st₄.frame
  have r3₄ : s₄.gpr .r3 = scr s₀ := by rw [st₄.r3, h₂.regs _ (by decide) (by decide)]
  have sv₄ : Spill.Saved s₄.mem (State.addr (scr s₀)) s₀.gpr spill :=
    h₂.saved.frame spill_slots pf fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)
      · exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)
  have i₄ : InRegions (s₄.rd ++ s₄.wr) (A (scr s₀) outOff) 4 := by
    rw [st₄.rd, st₄.wr, h₂.rd, h₂.wr]; exact hp.in_scr rfl (by decide)
  refine WP.seq (wp_ldr (by decide) (by rw [r3₄]) i₄ fun s₅ u₅ => WP.block_nil ?_)
  have e₅ : s₅.gpr .r2 = op s₀ := by
    rw [u₅.gpr]
    have := sv₄ (.r2, outOff) (by decide)
    rw [A_eq (by simp only [outOff]; omega_arith)]; exact this
  have h₅ : FinInv s₀ s₄ s₅ 0 :=
    ⟨by rw [u₅.other _ (by decide), r3₄], e₅, fun r _ _ h2 => u₅.other r h2,
      by rw [u₅.rd, st₄.rd, h₂.rd], by rw [u₅.wr, st₄.wr, h₂.wr], by rw [u₅.sp, st₄.sp, h₂.sp],
      by rw [u₅.mem]; exact Frame.refl _ _, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  unfold Impl.Argon2.Arm.epilogue
  refine WP.block_append ((finish_ok hp h₅ 256 (Nat.le_refl _)).mono fun s₆ h₆ => ?_)
  have sv₆ : Spill.Saved s₆.mem (State.addr (scr s₀)) s₀.gpr saved := fun p hpm =>
    h₆.frame.readW (r := ⟨State.addr (scr s₀) + BitVec.ofNat 64 p.2, 4⟩) (Region.contains_self _ _) (by
      have := saved_slots.bound hpm
      simp only [List.mem_singleton, forall_eq]
      exact (hp.out_scr.sub_right (Offset.sub_base _ (by omega_arith))).symm) (by decide) |>.trans
      (sv₄ p (List.mem_append_left _ hpm))
  rw [← List.append_nil (List.map _ saved)]
  refine Spill.restore_slots_ok saved_slots saved_restorable (g := s₀.gpr) (by rw [h₆.r3]; omega_arith)
    (fun d h₁ h₂ => by rw [h₆.r3, h₆.rd, h₆.wr, ← A_eq (by omega_arith)]; exact hp.in_scr rfl (by omega_arith))
    (by rw [h₆.r3]; exact sv₆) fun t ht ho hm hrd hwr hsp => WP.block_nil ⟨?_, ?_⟩
  · intro r hr
    exact Spill.restored_of ht (by decide) r hr
  · -- The output.
    have R₂ : blk s₂.mem (scr s₀) 0 = ofWords (xy s₀) := words_zero h₂.low
    have W₂ : working s₂.mem (scr s₀) = ofWords (xy s₀) := by
      rw [working_eq]; exact blk_of_words fun i hi => h₂.high i hi
    have X : xorBlock (blockAt s₀.mem (State.addr (xp s₀))) (blockAt s₀.mem (State.addr (yp s₀))) =
        ofWords (xy s₀) := by
      rw [blockAt_eq hp.x_fits, blockAt_eq hp.y_fits,
        blk_of_words (f := fun i => s₀.mem.readW (A (xp s₀) (4 * i)) 32)
          (fun i _ => by rw [Nat.zero_add]),
        blk_of_words (f := fun i => s₀.mem.readW (A (yp s₀) (4 * i)) 32)
          (fun i _ => by rw [Nat.zero_add]), xor_words]
      rfl
    have O : blk t.mem (op s₀) 0 = xorBlock (working s₄.mem (scr s₀)) (blk s₄.mem (scr s₀) 0) := by
      rw [hm, words_zero h₆.out, working_eq,
        blk_of_words (f := fun i => s₄.mem.readW (A (scr s₀) (1024 + 4 * i)) 32) (fun _ _ => rfl),
        blk_of_words (f := fun i => s₄.mem.readW (A (scr s₀) (4 * i)) 32)
          (fun i _ => by rw [Nat.zero_add]), xor_words]
      rfl
    show blockAt t.mem (State.addr (op s₀)) = _
    rw [blockAt_eq hp.out_fits, O, low_pass fits pf, R₂, st₄.working, W₂, ← X]
    simp only [compress]

end VG.Proof.Argon2.Arm

end

end

/-!
# Argon2 compression on ARMv7: verified

Constant time puts together the taint analysis of each piece, from what
both runs agree on (`RelCT`): the pointers are public; the passes over the
rows and columns depend only on `scratch` (`rounds_ct`); and `out`, loaded
from `scratch` after the rounds, is the same in both runs, by correctness. `compress_verified'` is the proof against `compressArm`, which the
derivation uses for its calls.
-/

@[expose] public section

namespace VG.Proof.Argon2.Arm

open VG VG.Arm VG.Spec.Argon2
open VG.Impl.Argon2.Arm (outOff)
open VG.Proof.Sha512.Arm (A A_eq)
open VG.Proof.MdStream.Arm (wp_ldr)

/-- The pointers are public. -/
theorem agree₀ {s₁ s₂ : State} (hpub : compressArm.pub s₁ s₂) :
    VG.Arm.Taint.Agree (VG.Arm.Taint.ofRegs [.r0, .r1, .r2, .r3]) s₁ s₂ := by
  obtain ⟨p0, p1, p2, p3⟩ := hpub
  exact VG.Arm.Taint.agree_ofRegs fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption

/-- Two runs from the precondition, with the same pointers. -/
def P₀ (s₁ s₂ : State) : Prop := compressArm.pre s₁ ∧ compressArm.pre s₂ ∧ compressArm.pub s₁ s₂

/-- After the initialization, from states related by `P₀`. -/
def R₁ (s₁ s₂ : State) : Prop := ∃ σ₁ σ₂, P₀ σ₁ σ₂ ∧ InitInv σ₁ s₁ 256 ∧ InitInv σ₂ s₂ 256

/-- What the rounds keep: `r3`, the regions, and the word holding `out`. -/
def Kept (u t : State) : Prop :=
  t.gpr .r3 = u.gpr .r3 ∧ t.rd = u.rd ∧ t.wr = u.wr ∧
    t.mem.readW (A (u.gpr .r3) outOff) 32 = u.mem.readW (A (u.gpr .r3) outOff) 32

/-- After the rounds. -/
def R₂ (s₁ s₂ : State) : Prop := ∃ u₁ u₂, R₁ u₁ u₂ ∧ Kept u₁ s₁ ∧ Kept u₂ s₂

/-- `out` loaded: in `r2`, with `r3` still `scratch`. -/
def Loaded (u t : State) : Prop := t.gpr .r2 = u.mem.readW (A (u.gpr .r3) outOff) 32 ∧ t.gpr .r3 = u.gpr .r3

/-- After loading `out`. -/
def R₃ (s₁ s₂ : State) : Prop := ∃ u₁ u₂, R₂ u₁ u₂ ∧ Loaded u₁ s₁ ∧ Loaded u₂ s₂

section
variable {σ s : State} (hp : Pre σ) (h : InitInv σ s 256)
include hp h

omit hp in
theorem InitInv.r3 : s.gpr .r3 = scr σ := h.regs _ (by decide) (by decide)

theorem InitInv.scr : Scr (s.gpr .r3) s.wr := by
  rw [h.r3, h.wr]; exact ⟨hp.scr_fits, fun o ho => hp.scr_wr rfl ho⟩

theorem InitInv.out : s.mem.readW (A (s.gpr .r3) outOff) 32 = op σ := by
  have := h.saved (.r2, outOff) (by decide)
  rw [h.r3, A_eq (by have := hp.scr_fits; simp only [outOff]; omega_using [this])]; exact this

end

theorem init_all {σ : State} (hp : Pre σ) :
    WP isa (.block (Impl.Argon2.Arm.prologue ++ (List.range 256).flatMap Impl.Argon2.Arm.initWord)) σ
      (InitInv σ · 256) :=
  prologue_ok hp fun _ h₁ => init_ok hp h₁ 256 (Nat.le_refl _)

theorem compress_ct : ConstantTime isa compressArm.pre compressArm.pub Impl.Argon2.Arm.compress := by
  apply RelCT.constantTime (Q := fun _ _ => True)
  unfold Impl.Argon2.Arm.compress
  -- The prologue and the initialization: the pointers are public.
  have h₁ : RelCT isa P₀ (.block (Impl.Argon2.Arm.prologue ++
      (List.range 256).flatMap Impl.Argon2.Arm.initWord)) R₁ := by
    have ct : RelCT isa P₀ (.block (Impl.Argon2.Arm.prologue ++
        (List.range 256).flatMap Impl.Argon2.Arm.initWord)) fun _ _ => True :=
      RelCT.taint (A := taint) (VG.Arm.Taint.ofRegs [.r0, .r1, .r2, .r3]) (fun _ _ h => agree₀ h.2.2)
        (by taint_decide)
    refine (ct.wpDep (F := fun σ s => InitInv σ s 256)
      fun s₁ s₂ h => ⟨init_all (pre_of _ h.1), init_all (pre_of _ h.2.1)⟩).mono (fun _ _ h => h) ?_
    rintro s₁ s₂ ⟨-, h⟩
    exact h
  -- The rounds: `scratch` is the same in both runs.
  have h₂ : RelCT isa R₁ Impl.Argon2.Arm.rounds R₂ := by
    have ct : RelCT isa R₁ Impl.Argon2.Arm.rounds fun _ _ => True := by
      refine rounds_ct.mono ?_ fun _ _ _ => trivial
      rintro s₁ s₂ ⟨σ₁, σ₂, ⟨q₁, q₂, pub⟩, i₁, i₂⟩
      have hp₁ := pre_of _ q₁; have hp₂ := pre_of _ q₂
      exact ⟨by rw [i₁.r3, i₂.r3]; exact pub.2.2.2, i₁.scr hp₁, i₂.scr hp₂⟩
    have kept {σ u : State} (hp : Pre σ) (i : InitInv σ u 256) : WP isa Impl.Argon2.Arm.rounds u (Kept u) :=
      (rounds_ok (i.scr hp)).mono fun t ht => ⟨ht.r3, ht.rd, ht.wr,
        outside_pass (by rw [i.r3]; exact hp.scr_fits) ht.frame (.inr ⟨by decide, by decide⟩)⟩
    refine (ct.wpDep (F := Kept) fun s₁ s₂ h => ?_).mono (fun _ _ h => h) ?_
    · obtain ⟨σ₁, σ₂, ⟨q₁, q₂, -⟩, i₁, i₂⟩ := h
      exact ⟨kept (pre_of _ q₁) i₁, kept (pre_of _ q₂) i₂⟩
    · rintro s₁ s₂ ⟨-, h⟩
      exact h
  -- Loading `out`: `r3` is `scratch`, in both runs.
  have h₃ : RelCT isa R₂ (.block [.ldr .r2 .r3 outOff]) R₃ := by
    have ct : RelCT isa R₂ (.block [.ldr .r2 .r3 outOff]) fun _ _ => True := by
      refine RelCT.taint (A := taint) (VG.Arm.Taint.ofRegs [.r3]) (fun s₁ s₂ h => ?_) (by taint_decide)
      obtain ⟨u₁, u₂, ⟨σ₁, σ₂, ⟨q₁, q₂, pub⟩, i₁, i₂⟩, k₁, k₂⟩ := h
      exact VG.Arm.Taint.agree_ofRegs fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rw [k₁.1, k₂.1, i₁.r3, i₂.r3]; exact pub.2.2.2
    have load {σ u t : State} (hp : Pre σ) (i : InitInv σ u 256) (k : Kept u t) :
        WP isa (.block [.ldr .r2 .r3 outOff]) t (Loaded t) :=
      wp_ldr (by decide) rfl (by
        rw [k.2.1, k.2.2.1, k.1, i.r3, i.rd, i.wr]; exact hp.in_scr rfl (by decide))
        fun t' u' => WP.block_nil ⟨u'.gpr, u'.other _ (by decide)⟩
    refine (ct.wpDep (F := Loaded) fun s₁ s₂ h => ?_).mono (fun _ _ h => h) ?_
    · obtain ⟨u₁, u₂, ⟨σ₁, σ₂, ⟨q₁, q₂, -⟩, i₁, i₂⟩, k₁, k₂⟩ := h
      exact ⟨load (pre_of _ q₁) i₁ k₁, load (pre_of _ q₂) i₂ k₂⟩
    · rintro s₁ s₂ ⟨-, h⟩
      exact h
  -- The output and the epilogue: `out` and `scratch` are public.
  have h₄ : RelCT isa R₃ (.block Impl.Argon2.Arm.epilogue) fun _ _ => True := by
    refine RelCT.taint (A := taint) (VG.Arm.Taint.ofRegs [.r2, .r3]) (fun s₁ s₂ h => ?_) (by taint_decide)
    obtain ⟨t₁, t₂, ⟨u₁, u₂, ⟨σ₁, σ₂, ⟨q₁, q₂, pub⟩, i₁, i₂⟩, k₁, k₂⟩, l₁, l₂⟩ := h
    have hp₁ := pre_of _ q₁; have hp₂ := pre_of _ q₂
    exact VG.Arm.Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [l₁.1, l₂.1, k₁.1, k₂.1, k₁.2.2.2, k₂.2.2.2, i₁.out hp₁, i₂.out hp₂]; exact pub.2.2.1
      · rw [l₁.2, l₂.2, k₁.1, k₂.1, i₁.r3, i₂.r3]; exact pub.2.2.2
  exact h₁.seq (h₂.seq (h₃.seq h₄))

/-- A state satisfying the precondition. -/
def satState : State where
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

theorem sat_pre : compressArm.pre satState := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, by decide, by decide, by decide, by decide⟩ <;>
  exact Region.disjoint_of_sep (by decide)

/-- The proof, against the contract the derivation's calls use. -/
theorem compress_verified' : Verified Arm.target Impl.Argon2.Arm.compress compressArm := by
  refine ⟨fun s hs => ?_, compress_ct, ⟨satState, sat_pre⟩⟩
  obtain ⟨t, s', he, h₁, h₂⟩ := correct (pre_of s hs)
  exact ⟨t, s', he, ⟨h₁, Exec.sp he⟩, h₂⟩

end VG.Proof.Argon2.Arm
