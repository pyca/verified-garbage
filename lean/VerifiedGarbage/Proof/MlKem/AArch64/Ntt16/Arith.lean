module

public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Trace
public import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16
public import VerifiedGarbage.Proof.MlKem.NttLayer
import VerifiedGarbage.Proof.MlKem.AArch64.Barrett
import VerifiedGarbage.Proof.MlKem.Arith
import VerifiedGarbage.Proof.Framework.Omega

/-! # The arithmetic of the NTTs' halfwords

Each is a 16-bit signed integer that represents an element of `ℤ_q` (`Rep`), within a bound. -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Ntt16

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.Ntt16
open VG.Spec.MlKem (Zq)

/-- The integer of `x` represents `a`, and is between `lo` and `hi`. -/
structure Rep (x : BitVec 16) (a : Zq) (lo hi : Int) : Prop where
  lo : lo ≤ x.toInt
  hi : x.toInt ≤ hi
  mod : x.toInt % 3329 = (a.val : Int)

theorem Rep.mono {x : BitVec 16} {a : Zq} {lo hi lo' hi' : Int} (h : Rep x a lo hi) (hl : lo' ≤ lo) (hh : hi ≤ hi') :
    Rep x a lo' hi' :=
  ⟨by have := h.lo; omega_using [this, hl], by have := h.hi; omega_using [this, hh], h.mod⟩

theorem bmod_id {x : Int} (h : -32768 ≤ x) (h' : x < 32768) : x.bmod (2 ^ 16) = x :=
  Int.bmod_eq_of_le (m := 65536) (by omega_using [h]) (by omega_using [h'])

theorem val_lt_int (a : Zq) : a.val < 3329 := a.isLt
theorem val_add_nat (a b : Zq) : (a + b).val = (a.val + b.val) % 3329 := val_add' a b
theorem val_sub_nat (a b : Zq) : (a - b).val = (a.val + (3329 - b.val)) % 3329 := val_sub' a b
theorem val_mul_nat (a b : Zq) : (a * b).val = a.val * b.val % 3329 := val_mul a b

theorem Rep.add {x y : BitVec 16} {a a' : Zq} {l u l' u' : Int} (h : Rep x a l u) (h' : Rep y a' l' u')
    (hl : -32768 ≤ l + l') (hu : u + u' < 32768) : Rep (x + y) (a + a') (l + l') (u + u') := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨h4, h5, h6⟩ := h'
  have e : (x + y).toInt = x.toInt + y.toInt := by
    rw [BitVec.toInt_add, bmod_id (by omega_using [h1, h4, hl]) (by omega_using [h2, h5, hu])]
  refine ⟨by omega_using [e, h1, h4], by omega_using [e, h2, h5], ?_⟩
  have := val_add_nat a a'
  omega_using [this, e, h3, h6]

theorem Rep.sub {x y : BitVec 16} {a a' : Zq} {l u l' u' : Int} (h : Rep x a l u) (h' : Rep y a' l' u')
    (hl : -32768 ≤ l - u') (hu : u - l' < 32768) : Rep (x - y) (a - a') (l - u') (u - l') := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨h4, h5, h6⟩ := h'
  have e : (x - y).toInt = x.toInt - y.toInt := by
    rw [BitVec.toInt_sub, bmod_id (by omega_using [h1, h5, hl]) (by omega_using [h2, h4, hu])]
  refine ⟨by omega_using [e, h1, h5], by omega_using [e, h2, h4], ?_⟩
  have := val_lt_int a'
  have hs := val_sub_nat a a'
  omega_using [hs, e, h3, h6, this]

/-- A sum less `8q`, which may wrap around before `8q` is subtracted. -/
theorem Rep.addOfs {x y : BitVec 16} {a a' : Zq} {l u l' u' : Int} (h : Rep x a l u) (h' : Rep y a' l' u')
    (hl : -32768 ≤ l + l' - 26632) (hu : u + u' - 26632 < 32768) :
    Rep (x + y - 26632#16) (a + a') (l + l' - 26632) (u + u' - 26632) := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨h4, h5, h6⟩ := h'
  have e : (x + y - 26632#16).toInt = x.toInt + y.toInt - 26632 := by
    rw [BitVec.toInt_sub, BitVec.toInt_add, show (26632#16).toInt = 26632 from rfl, Int.bmod_sub_bmod,
      bmod_id (by omega_using [h1, h4, hl]) (by omega_using [h2, h5, hu])]
  refine ⟨by omega_using [e, h1, h4], by omega_using [e, h2, h5], ?_⟩
  have := val_add_nat a a'
  omega_using [this, e, h3, h6]

/-- A multiplier and its quotient. -/
structure IsMul (z t : BitVec 16) (c : Zq) : Prop where
  mod : z.toInt % 3329 = (c.val : Int)
  lo : -1664 ≤ 32768 * z.toInt - 3329 * t.toInt
  hi : 32768 * z.toInt - 3329 * t.toInt ≤ 1664

theorem toInt_lo (x : BitVec 16) : -32768 ≤ x.toInt := by have := BitVec.le_toInt x; simpa using this
theorem toInt_hi (x : BitVec 16) : x.toInt ≤ 32767 := by
  have := BitVec.toInt_lt (x := x); simp at this; omega_using [this]

theorem sqr_bmod (x t : BitVec 16) :
    (sqr x t).toInt = ((2 * x.toInt * t.toInt + 32768) / 65536).bmod (2 ^ 16) := by
  rw [sqr, BitVec.toInt_ofInt, Int.shiftRight_eq_div_pow]; rfl

/-- A reduced product, of any halfword. -/
theorem rep_red {x z t : BitVec 16} {a c : Zq} (hx : x.toInt % 3329 = (a.val : Int)) (h : IsMul z t c) :
    Rep (red x z t) (c * a) (-3328) 3328 := by
  obtain ⟨hm, hl, hh⟩ := h
  have b1 := toInt_lo x
  have b2 := toInt_hi x
  generalize hX : x.toInt = X at *
  generalize hZ : z.toInt = Z at *
  generalize hT : t.toInt = T at *
  -- The error of the quotient.
  have k1 : -(32768 * 1664) ≤ X * (32768 * Z - 3329 * T) ∧ X * (32768 * Z - 3329 * T) ≤ 32768 * 1664 := by
    generalize 32768 * Z - 3329 * T = D at hl hh
    have : (X * D).natAbs ≤ 32768 * 1664 := by
      rw [Int.natAbs_mul]
      exact Nat.mul_le_mul (by omega_using [b1, b2]) (by omega_using [hl, hh])
    omega_using [this]
  have k2 : X * (32768 * Z - 3329 * T) = 32768 * (X * Z) - 3329 * (X * T) := by
    rw [Int.mul_sub, Int.mul_left_comm X 32768, Int.mul_left_comm X 3329]
  rw [k2] at k1
  have e : (red x z t).toInt = X * Z - 3329 * ((2 * (X * T) + 32768) / 65536) := by
    rw [red, BitVec.toInt_sub, BitVec.toInt_mul, BitVec.toInt_mul, sqr_bmod, hX, hZ, hT,
      show (3329#16).toInt = 3329 from rfl, ← Int.sub_bmod, Int.mul_assoc 2 X T]
    rw [Int.mul_comm _ 3329, Int.sub_bmod, Int.mul_bmod_bmod, ← Int.sub_bmod]
    refine bmod_id ?_ ?_ <;> · generalize X * Z = P at *; generalize X * T = S at *; omega_using [k1]
  have k3 : X * Z % 3329 = ((c * a).val : Int) := by
    rw [val_mul_nat, Int.mul_emod, hx, hm, Int.mul_comm]
    rw [Int.natCast_emod, Int.natCast_mul]; rfl
  refine ⟨?_, ?_, ?_⟩ <;> rw [e]
  · generalize X * Z = P at *; generalize X * T = S at *; omega_using [k1]
  · generalize X * Z = P at *; generalize X * T = S at *; omega_using [k1]
  · generalize X * Z = P at *; generalize X * T = S at *; omega_using [k3]

/-- The floor of a quotient by `q`. -/
theorem flo_toInt {x : BitVec 16} (h : -26632 ≤ x.toInt) (h' : x.toInt ≤ 26632) : (flo x).toInt = x.toInt / 3329 := by
  rw [flo, BitVec.toInt_sshiftRight, sqr_bmod, show (20159#16).toInt = 20159 from rfl, Int.shiftRight_eq_div_pow]
  generalize x.toInt = X at *
  rw [bmod_id (by omega_using [h]) (by omega_using [h'])]
  show (2 * X * 20159 + 32768) / 65536 / 2048 = X / 3329
  omega_using [h, h']

/-- The least residue. -/
def canon (x : BitVec 16) : BitVec 16 := x - flo x * 3329#16

theorem canon_toNat {x : BitVec 16} {a : Zq} {l u : Int} (h : Rep x a l u) (hl : -26632 ≤ l) (hu : u ≤ 26632) :
    (canon x).toNat = a.val := by
  obtain ⟨h1, h2, h3⟩ := h
  have e : (canon x).toInt = x.toInt % 3329 := by
    rw [canon, BitVec.toInt_sub, BitVec.toInt_mul, flo_toInt (by omega_using [h1, hl]) (by omega_using [h2, hu]),
      show (3329#16).toInt = 3329 from rfl, Int.sub_bmod, Int.bmod_bmod, ← Int.sub_bmod]
    generalize x.toInt = X at *
    rw [bmod_id (by omega_using []) (by omega_using [])]
    omega_using []
  rw [h3] at e
  have l := val_lt_int a
  have := BitVec.toInt_eq_toNat_cond (canon x)
  split at this <;> omega_using [this, e, l, (canon x).isLt]

/-- `x`, or `x + q` if it is negative. -/
def pos (x : BitVec 16) : BitVec 16 := x + (x.sshiftRight 15 &&& 3329#16)

theorem pos_toNat {x : BitVec 16} {a : Zq} (h : Rep x a (-3328) 3328) : (pos x).toNat = a.val := by
  obtain ⟨h1, h2, h3⟩ := h
  have l := val_lt_int a
  have hs : x.sshiftRight 15 = if x.toInt < 0 then BitVec.allOnes 16 else 0#16 := by
    apply BitVec.eq_of_toInt_eq
    rw [BitVec.toInt_sshiftRight, Int.shiftRight_eq_div_pow]
    split
    · rw [show (BitVec.allOnes 16).toInt = -1 from rfl]
      show x.toInt / 32768 = -1
      omega_using [h1, ‹x.toInt < 0›]
    · rw [show (0#16).toInt = 0 from rfl]
      show x.toInt / 32768 = 0
      omega_using [h2, ‹¬x.toInt < 0›]
  have ht := BitVec.toInt_eq_toNat_cond x
  have hx := x.isLt
  rw [pos, hs]
  split
  · rw [BitVec.allOnes_and, BitVec.toNat_add, show (3329#16).toNat = 3329 from rfl]
    split at ht <;> omega_using [ht, h1, h2, h3, l, hx, ‹x.toInt < 0›]
  · rw [BitVec.zero_and, BitVec.add_zero]
    split at ht <;> omega_using [ht, h1, h2, h3, l, hx, ‹¬x.toInt < 0›]

/-- The multiplier by `ζ_k`, and its quotient. -/
def zB (k : Nat) : BitVec 16 := BitVec.ofNat 16 (cen (Impl.MlKem.AArch64.Ntt16.zeta k))
def tB (k : Nat) : BitVec 16 := BitVec.ofNat 16 (quo (Impl.MlKem.AArch64.Ntt16.zeta k))

theorem zB_facts : ∀ k < 128, (zB k).toInt % 3329 = ((zetaTable.getD k 0 : Nat) : Int) ∧
    -1664 ≤ 32768 * (zB k).toInt - 3329 * (tB k).toInt ∧ 32768 * (zB k).toInt - 3329 * (tB k).toInt ≤ 1664 := by
  decide +kernel

theorem zeta_val {k : Nat} (hk : k < 128) : zetaTable.getD k 0 = (Proof.MlKem.zeta k).val := by
  rw [← zetas_getD hk, ← zetaTable_eq]

theorem isMul {k : Nat} (hk : k < 128) : IsMul (zB k) (tB k) (Proof.MlKem.zeta k) := by
  obtain ⟨h1, h2, h3⟩ := zB_facts k hk
  exact ⟨by rw [h1, zeta_val hk], h2, h3⟩

end VG.Proof.MlKem.AArch64.Ntt16
