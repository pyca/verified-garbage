module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.Loops
public import VerifiedGarbage.Impl.Rsa.PPC64LE.InvBatch
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontRound
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontStep
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Divstep.WordBasic

/-!
# The batched inverse on PPC64LE: its digit loops

Over `n` digits of 32 bits at byte offsets of the working space, pointers in
`r5`–`r7` and the count in `r8`, as `Loops.lean`'s:

* `macLoop_ok`: `[o] := [a] + k [b]`, `k < 2^32` in `r11`, the carry in `r9`;
* `shrLoop_ok`: `[o] := [a] >> 30`, reading one digit more;
* `linLoop_ok`: `[o] := u [a] + v [b]` for signed `u`, `v` in `r11`, `r12`,
  the signed carry in `r9`.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.InvBatch

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Impl.Rsa.PPC64LE.Keys
open VG.Impl.Rsa.PPC64LE.InvBatch (macBody shrBody linBody)
open VG.Proof.Rsa.PPC64LE.Loops (loopRegs Ahead Ahead.outside)

/-! ## `mac` -/

/-- A digit of `a + k m + c`, on bit vectors: below `2^64`. -/
theorem mac_arith (k : BitVec 64) (m a : BitVec 32) (c : BitVec 64) (hk : k.toNat < 2 ^ 32)
    (hc : c.toNat < 2 ^ 32) :
    let S := k * m.setWidth 64 + a.setWidth 64 + c
    (S >>> 32).toNat < 2 ^ 32 ∧
      (S.setWidth 32).toNat + 2 ^ 32 * (S >>> 32).toNat = a.toNat + k.toNat * m.toNat + c.toNat := by
  intro S
  have hm := m.isLt
  have ha := a.isLt
  have hkm : k.toNat * m.toNat ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have vS : S.toNat = ((k.toNat * m.toNat % 2 ^ 64 + a.toNat) % 2 ^ 64 + c.toNat) % 2 ^ 64 := by
    simp only [S, BitVec.toNat_add, BitVec.toNat_mul, toNat_ext32]
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_setWidth, vS]
  generalize k.toNat * m.toNat = P at hkm ⊢
  omega

/-- `[o] := [a] + k [m]` over `n` digits (`countLoop .r8 macBody`), from the
carry `c` in `r9`: the sum and the carry out. -/
theorem macLoop_ok {s : State} {B : Addr} {Z dO dA dM n : Nat} (hs : Scr s B Z)
    (h5 : s.gpr .r5 = off B dO) (h6 : s.gpr .r6 = off B dA) (h7 : s.gpr .r7 = off B dM)
    (h8 : s.gpr .r8 = BitVec.ofNat 64 n) (h9 : (s.gpr .r9).toNat < 2 ^ 32)
    (h11 : (s.gpr .r11).toNat < 2 ^ 32) (hn : 1 ≤ n) (hn' : n < 2 ^ 32)
    (hO : dO + 4 * n ≤ Z) (hA : dA + 4 * n ≤ Z) (hM : dM + 4 * n ≤ Z)
    (aA : Ahead dO dA n) (aM : Ahead dO dM n) :
    WP isa (countLoop .r8 macBody) s fun t =>
      (t.gpr .r9).toNat < 2 ^ 32 ∧
      val32 t.mem B dO n + 2 ^ (32 * n) * (t.gpr .r9).toNat =
        val32 s.mem B dA n + (s.gpr .r11).toNat * val32 s.mem B dM n + (s.gpr .r9).toNat ∧
      t.gpr .r5 = off B (dO + 4 * n) ∧ Outside B dO (4 * n) s.mem t.mem ∧ Keep loopRegs s t := by
  have hnw := hs.nowrap
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .r5 = off B (dO + 4 * i) ∧ t.gpr .r6 = off B (dA + 4 * i) ∧ t.gpr .r7 = off B (dM + 4 * i) ∧
      (t.gpr .r9).toNat < 2 ^ 32 ∧ Outside B dO (4 * i) s.mem t.mem ∧
      val32 t.mem B dO i + 2 ^ (32 * i) * (t.gpr .r9).toNat =
        val32 s.mem B dA i + (s.gpr .r11).toNat * val32 s.mem B dM i + (s.gpr .r9).toNat ∧
      Keep loopRegs s t
  refine WP.mono (wp_countdown (body := .block (macBody ++ ([.subi .r8 .r8 1] : List Instr)))
    (cnt := .r8) (N := n) (by omega_arith) (by omega_arith) Inv
    (fun i hi t ⟨j5, j6, j7, j9, jout, jeq, jk⟩ hc => ?_)
    ⟨by rw [h5]; rfl, by rw [h6]; rfl, by rw [h7]; rfl, h9, Outside.refl _ _ _ _,
      by simp [val32], Keep.refl _ _⟩ h8)
    fun t ⟨j5, _, _, j9, jout, jeq, jk⟩ => ⟨j9, jeq, j5, jout, jk⟩
  have k11 : t.gpr .r11 = s.gpr .r11 := jk.gpr _ (by decide)
  have hst := (show WP isa (.block (macBody ++ ([.subi .r8 .r8 1] : List Instr))) t fun t' =>
      let S := t.gpr .r11 * (t.mem.readW (off B (dM + 4 * i)) 32).setWidth 64 +
        (t.mem.readW (off B (dA + 4 * i)) 32).setWidth 64 + t.gpr .r9
      (t'.gpr .r5 = off B (dO + 4 * i + 4) ∧ t'.gpr .r6 = off B (dA + 4 * i + 4) ∧
        t'.gpr .r7 = off B (dM + 4 * i + 4) ∧ t'.gpr .r9 = S >>> 32 ∧
        t'.gpr .r8 = t.gpr .r8 - BitVec.ofNat 64 1 ∧
        t'.mem = t.mem.writeW (off B (dO + 4 * i)) (S.setWidth 32)) ∧ Keep loopRegs t t' from by
    refine WP.keep _ ?_ (by decide)
    prun [macBody, j5, j6, j7, (hs.congr jk.wr).ld (show dA + 4 * i + 4 ≤ Z by omega_arith),
      (hs.congr jk.wr).ld (show dM + 4 * i + 4 ≤ Z by omega_arith),
      (hs.congr jk.wr).st (show dO + 4 * i + 4 ≤ Z by omega_arith)])
  refine WP.mono hst fun t' ⟨⟨l5, l6, l7, l9, l8, lm⟩, lk⟩ => ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, jk.trans' lk⟩, l8⟩
  · rw [l5, show dO + 4 * i + 4 = dO + 4 * (i + 1) by omega_arith]
  · rw [l6, show dA + 4 * i + 4 = dA + 4 * (i + 1) by omega_arith]
  · rw [l7, show dM + 4 * i + 4 = dM + 4 * (i + 1) by omega_arith]
  · rw [l9]; exact (mac_arith _ _ _ _ (by rw [k11]; exact h11) j9).1
  · rw [lm]
    exact (jout.mono (Nat.le_refl _) (by omega_arith)).trans
      ((writeW32_outside _ B (d := dO + 4 * i) _ (by omega_arith)).mono (by omega_arith) (by omega_arith))
  · have wa : w32 t.mem B (dA + 4 * i) = w32 s.mem B (dA + 4 * i) :=
      jout.w32 (by have := aA.outside hi; omega_arith) (by omega_arith)
    have wm : w32 t.mem B (dM + 4 * i) = w32 s.mem B (dM + 4 * i) :=
      jout.w32 (by have := aM.outside hi; omega_arith) (by omega_arith)
    have k : _ = w32 t.mem B (dA + 4 * i) + (t.gpr .r11).toNat * w32 t.mem B (dM + 4 * i) + (t.gpr .r9).toNat :=
      (mac_arith (t.gpr .r11) (t.mem.readW (off B (dM + 4 * i)) 32)
        (t.mem.readW (off B (dA + 4 * i)) 32) _ (by rw [k11]; exact h11) j9).2
    rw [lm, l9, val32_write_top _ _ _ _ _ (by omega_arith), val32_succ s.mem B dM i, val32_succ s.mem B dA i,
      ← pow32_mul i, ← wa, ← wm, ← k11]
    rw [k11] at k
    grind

/-! ## `shr` -/

/-- A digit of the shift by 30: the top two bits of `x` and the low 30 of `y`. -/
theorem shr_arith (x y : BitVec 32) :
    (((x.setWidth 64 >>> 30) + (y.setWidth 64 <<< 2)).setWidth 32).toNat =
      x.toNat / 2 ^ 30 + 4 * (y.toNat % 2 ^ 30) := by
  have hx := x.isLt
  have hy := y.isLt
  rw [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft,
    toNat_ext32, toNat_ext32, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  omega

/-- `[o] := [a] >> 30` over `n` digits (`countLoop .r8 shrBody`), reading `n + 1`
digits of `a`, apart from `o`. -/
theorem shrLoop_ok {s : State} {B : Addr} {Z dO dA n : Nat} (hs : Scr s B Z)
    (h5 : s.gpr .r5 = off B dO) (h6 : s.gpr .r6 = off B dA) (h8 : s.gpr .r8 = BitVec.ofNat 64 n)
    (hn : 1 ≤ n) (hn' : n < 2 ^ 32) (hO : dO + 4 * n ≤ Z) (hA : dA + 4 * (n + 1) ≤ Z)
    (sep : dO + 4 * n ≤ dA ∨ dA + 4 * (n + 1) ≤ dO) :
    WP isa (countLoop .r8 shrBody) s fun t =>
      val32 t.mem B dO n + 2 ^ (32 * n) * (w32 s.mem B (dA + 4 * n) / 2 ^ 30) =
        val32 s.mem B dA (n + 1) / 2 ^ 30 ∧
      Outside B dO (4 * n) s.mem t.mem ∧ Keep loopRegs s t := by
  have hnw := hs.nowrap
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .r5 = off B (dO + 4 * i) ∧ t.gpr .r6 = off B (dA + 4 * i) ∧ Outside B dO (4 * i) s.mem t.mem ∧
      val32 t.mem B dO i + 2 ^ (32 * i) * (w32 s.mem B (dA + 4 * i) / 2 ^ 30) =
        val32 s.mem B dA (i + 1) / 2 ^ 30 ∧ Keep loopRegs s t
  refine WP.mono (wp_countdown (body := .block (shrBody ++ ([.subi .r8 .r8 1] : List Instr)))
    (cnt := .r8) (N := n) (by omega_arith) (by omega_arith) Inv
    (fun i hi t ⟨j5, j6, jout, jeq, jk⟩ hc => ?_)
    ⟨by rw [h5]; rfl, by rw [h6]; rfl, Outside.refl _ _ _ _,
      by simp only [val32, Nat.mul_zero, Nat.add_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add], Keep.refl _ _⟩ h8)
    fun t ⟨_, _, jout, jeq, jk⟩ => ⟨jeq, jout, jk⟩
  have hst := (show WP isa (.block (shrBody ++ ([.subi .r8 .r8 1] : List Instr))) t fun t' =>
      (t'.gpr .r5 = off B (dO + 4 * i + 4) ∧ t'.gpr .r6 = off B (dA + 4 * i + 4) ∧
        t'.gpr .r8 = t.gpr .r8 - BitVec.ofNat 64 1 ∧
        t'.mem = t.mem.writeW (off B (dO + 4 * i))
          (((t.mem.readW (off B (dA + 4 * i)) 32).setWidth 64 >>> 30 +
            (t.mem.readW (off B (dA + 4 * i + 4)) 32).setWidth 64 <<< 2).setWidth 32)) ∧
        Keep loopRegs t t' from by
    refine WP.keep _ ?_ (by decide)
    prun [shrBody, j5, j6, (hs.congr jk.wr).ld (show dA + 4 * i + 4 ≤ Z by omega_arith),
      (hs.congr jk.wr).ld (show dA + 4 * i + 4 + 4 ≤ Z by omega_arith),
      (hs.congr jk.wr).st (show dO + 4 * i + 4 ≤ Z by omega_arith)])
  refine WP.mono hst fun t' ⟨⟨l5, l6, l8, lm⟩, lk⟩ => ⟨⟨?_, ?_, ?_, ?_, jk.trans' lk⟩, l8⟩
  · rw [l5, show dO + 4 * i + 4 = dO + 4 * (i + 1) by omega_arith]
  · rw [l6, show dA + 4 * i + 4 = dA + 4 * (i + 1) by omega_arith]
  · rw [lm]
    exact (jout.mono (Nat.le_refl _) (by omega_arith)).trans
      ((writeW32_outside _ B (d := dO + 4 * i) _ (by omega_arith)).mono (by omega_arith) (by omega_arith))
  · have wa : w32 t.mem B (dA + 4 * i) = w32 s.mem B (dA + 4 * i) :=
      jout.w32 (by omega_arith) (by omega_arith)
    have wb : w32 t.mem B (dA + 4 * i + 4) = w32 s.mem B (dA + 4 * i + 4) :=
      jout.w32 (by omega_arith) (by omega_arith)
    have k : _ = w32 t.mem B (dA + 4 * i) / 2 ^ 30 + 4 * (w32 t.mem B (dA + 4 * i + 4) % 2 ^ 30) :=
      shr_arith (t.mem.readW (off B (dA + 4 * i)) 32) (t.mem.readW (off B (dA + 4 * i + 4)) 32)
    rw [wa, wb] at k
    rw [lm, val32_write_top _ _ _ _ _ (by omega_arith), k, val32_succ s.mem B dA (i + 1),
      show dA + 4 * (i + 1) = dA + 4 * i + 4 by omega_arith]
    generalize w32 s.mem B (dA + 4 * i + 4) = y at jeq ⊢
    generalize w32 s.mem B (dA + 4 * i) = x at jeq ⊢
    have ey : y = 2 ^ 30 * (y / 2 ^ 30) + y % 2 ^ 30 := (Nat.div_add_mod y _).symm
    have e32 : 2 ^ (32 * (i + 1)) = 2 ^ 30 * (4 * 2 ^ (32 * i)) := by
      rw [← pow32_mul]; omega_arith
    rw [e32, Nat.mul_assoc (2 ^ 30) (4 * 2 ^ (32 * i)) y, Nat.add_mul_div_left _ _ (by decide), ← jeq]
    generalize 2 ^ (32 * i) = P
    generalize y / 2 ^ 30 = q at ey ⊢
    generalize y % 2 ^ 30 = r at ey ⊢
    subst ey
    grind

/-! ## `lin` -/

theorem setWidth_ofInt (x : BitVec 32) : x.setWidth 64 = BitVec.ofInt 64 (x.toNat : Int) := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_ext32, BitVec.toNat_ofInt]
  have := x.isLt
  omega

/-- A 64-bit sum `T` of a small `t`: its low digit, and its arithmetic shift by
32 (the logical shift less `2^32` where `T` is negative), `t / 2^32`. -/
theorem lin_core (t : Int) (h1 : -2 ^ 63 ≤ t) (h2 : t < 2 ^ 63) :
    let T := BitVec.ofInt 64 t
    (T >>> 32) - ((T >>> 63) <<< 32) = BitVec.ofInt 64 (t / 2 ^ 32) ∧
      ((T.setWidth 32).toNat : Int) + 2 ^ 32 * (t / 2 ^ 32) = t := by
  intro T
  have hT : (T.toNat : Int) = t % 2 ^ 64 := Divstep.toNat_ofInt64 t
  have hT' := T.isLt
  have hR : ((BitVec.ofInt 64 (t / 2 ^ 32)).toNat : Int) = (t / 2 ^ 32) % 2 ^ 64 := Divstep.toNat_ofInt64 _
  refine ⟨BitVec.eq_of_toNat_eq ?_, ?_⟩
  · rw [BitVec.toNat_sub, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ushiftRight,
      Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
    omega
  · rw [BitVec.toNat_setWidth]
    omega

/-- `x`, sign-extended from 32 bits. -/
theorem sext_arith (x : BitVec 32) :
    x.setWidth 64 - ((x.setWidth 64 >>> 31) <<< 32) = BitVec.ofInt 64 x.toInt := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow, toNat_ext32, BitVec.toNat_ofInt, BitVec.toInt_eq_toNat_cond]
  have := x.isLt
  split <;> omega

/-- `|u X| ≤ |u| 2^32` for `|X| ≤ 2^32`. -/
theorem small_mul {u X : Int} (hX1 : -2 ^ 32 ≤ X) (hX2 : X ≤ 2 ^ 32) :
    (u * X).natAbs ≤ u.natAbs * 2 ^ 32 := by
  rw [Int.natAbs_mul]
  exact Nat.mul_le_mul_left _ (by omega)

/-- A digit of `u x + v y + c`, on bit vectors: the low digit of the 64-bit
sum and its arithmetic shift by 32, for `x`, `y` between `-2^31` and `2^32`. -/
theorem lin_arith (u v c X Y : Int) (huv : u.natAbs + v.natAbs ≤ 2 ^ 30) (hc1 : -2 ^ 31 ≤ c) (hc2 : c ≤ 2 ^ 31) (hX1 : -2 ^ 31 ≤ X) (hX2 : X < 2 ^ 32)
    (hY1 : -2 ^ 31 ≤ Y) (hY2 : Y < 2 ^ 32) :
    let T := BitVec.ofInt 64 u * BitVec.ofInt 64 X + BitVec.ofInt 64 v * BitVec.ofInt 64 Y + BitVec.ofInt 64 c
    let t := u * X + v * Y + c
    (T >>> 32) - ((T >>> 63) <<< 32) = BitVec.ofInt 64 (t / 2 ^ 32) ∧
      ((T.setWidth 32).toNat : Int) + 2 ^ 32 * (t / 2 ^ 32) = t ∧ -2 ^ 31 ≤ t / 2 ^ 32 ∧ t / 2 ^ 32 ≤ 2 ^ 31 := by
  intro T t
  have eT : T = BitVec.ofInt 64 t := by simp only [T, t, BitVec.ofInt_add, BitVec.ofInt_mul]
  have a := small_mul (u := u) (X := X) (by omega) (by omega)
  have b := small_mul (u := v) (X := Y) (by omega) (by omega)
  obtain ⟨e1, e2⟩ := lin_core t (by omega) (by omega)
  rw [eT]
  exact ⟨e1, e2, by omega, by omega⟩

/-- `[o] := u [a] + v [b]` over `n` digits (`countLoop .r8 linBody`), for
`|u|, |v| ≤ 2^30` in `r11`, `r12`, from the signed carry `c` in `r9`: the
combination and the carry out. -/
theorem linLoop_ok {s : State} {B : Addr} {Z dO dA dB n : Nat} (hs : Scr s B Z) {u v c : Int}
    (h5 : s.gpr .r5 = off B dO) (h6 : s.gpr .r6 = off B dA) (h7 : s.gpr .r7 = off B dB)
    (h8 : s.gpr .r8 = BitVec.ofNat 64 n) (h9 : s.gpr .r9 = BitVec.ofInt 64 c)
    (h11 : s.gpr .r11 = BitVec.ofInt 64 u) (h12 : s.gpr .r12 = BitVec.ofInt 64 v)
    (huv : u.natAbs + v.natAbs ≤ 2 ^ 30)
    (hc1 : -2 ^ 31 ≤ c) (hc2 : c ≤ 2 ^ 31) (hn : 1 ≤ n) (hn' : n < 2 ^ 32)
    (hO : dO + 4 * n ≤ Z) (hA : dA + 4 * n ≤ Z) (hB : dB + 4 * n ≤ Z)
    (aA : Ahead dO dA n) (aB : Ahead dO dB n) :
    WP isa (countLoop .r8 linBody) s fun t =>
      (∃ c' : Int, -2 ^ 31 ≤ c' ∧ c' ≤ 2 ^ 31 ∧ t.gpr .r9 = BitVec.ofInt 64 c' ∧
        (val32 t.mem B dO n : Int) + 2 ^ (32 * n) * c' =
          u * val32 s.mem B dA n + v * val32 s.mem B dB n + c) ∧
      t.gpr .r5 = off B (dO + 4 * n) ∧ t.gpr .r6 = off B (dA + 4 * n) ∧ t.gpr .r7 = off B (dB + 4 * n) ∧
      Outside B dO (4 * n) s.mem t.mem ∧ Keep loopRegs s t := by
  have hnw := hs.nowrap
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .r5 = off B (dO + 4 * i) ∧ t.gpr .r6 = off B (dA + 4 * i) ∧ t.gpr .r7 = off B (dB + 4 * i) ∧
      (∃ c' : Int, -2 ^ 31 ≤ c' ∧ c' ≤ 2 ^ 31 ∧ t.gpr .r9 = BitVec.ofInt 64 c' ∧
        (val32 t.mem B dO i : Int) + 2 ^ (32 * i) * c' =
          u * val32 s.mem B dA i + v * val32 s.mem B dB i + c) ∧
      Outside B dO (4 * i) s.mem t.mem ∧ Keep loopRegs s t
  refine WP.mono (wp_countdown (body := .block (linBody ++ ([.subi .r8 .r8 1] : List Instr)))
    (cnt := .r8) (N := n) (by omega_arith) (by omega_arith) Inv
    (fun i hi t ⟨j5, j6, j7, ⟨c', jc1, jc2, j9, jeq⟩, jout, jk⟩ hc => ?_)
    ⟨by rw [h5]; rfl, by rw [h6]; rfl, by rw [h7]; rfl,
      ⟨c, hc1, hc2, h9, by simp [val32]⟩, Outside.refl _ _ _ _, Keep.refl _ _⟩ h8)
    fun t ⟨j5, j6, j7, jc, jout, jk⟩ => ⟨jc, j5, j6, j7, jout, jk⟩
  have k11 : t.gpr .r11 = BitVec.ofInt 64 u := (jk.gpr _ (by decide)).trans h11
  have k12 : t.gpr .r12 = BitVec.ofInt 64 v := (jk.gpr _ (by decide)).trans h12
  have hst := (show WP isa (.block (linBody ++ ([.subi .r8 .r8 1] : List Instr))) t fun t' =>
      let T := t.gpr .r11 * (t.mem.readW (off B (dA + 4 * i)) 32).setWidth 64 +
        t.gpr .r12 * (t.mem.readW (off B (dB + 4 * i)) 32).setWidth 64 + t.gpr .r9
      (t'.gpr .r5 = off B (dO + 4 * i + 4) ∧ t'.gpr .r6 = off B (dA + 4 * i + 4) ∧
        t'.gpr .r7 = off B (dB + 4 * i + 4) ∧ t'.gpr .r9 = (T >>> 32) - ((T >>> 63) <<< 32) ∧
        t'.gpr .r8 = t.gpr .r8 - BitVec.ofNat 64 1 ∧
        t'.mem = t.mem.writeW (off B (dO + 4 * i)) (T.setWidth 32)) ∧ Keep loopRegs t t' from by
    refine WP.keep _ ?_ (by decide)
    prun [linBody, j5, j6, j7, (hs.congr jk.wr).ld (show dA + 4 * i + 4 ≤ Z by omega_arith),
      (hs.congr jk.wr).ld (show dB + 4 * i + 4 ≤ Z by omega_arith),
      (hs.congr jk.wr).st (show dO + 4 * i + 4 ≤ Z by omega_arith)])
  have wa : w32 t.mem B (dA + 4 * i) = w32 s.mem B (dA + 4 * i) :=
    jout.w32 (by have := aA.outside hi; omega_arith) (by omega_arith)
  have wb : w32 t.mem B (dB + 4 * i) = w32 s.mem B (dB + 4 * i) :=
    jout.w32 (by have := aB.outside hi; omega_arith) (by omega_arith)
  have xa : w32 t.mem B (dA + 4 * i) < 2 ^ 32 := (t.mem.readW (off B (dA + 4 * i)) 32).isLt
  have xb : w32 t.mem B (dB + 4 * i) < 2 ^ 32 := (t.mem.readW (off B (dB + 4 * i)) 32).isLt
  obtain ⟨e1, e2, e3, e4⟩ := lin_arith u v c' (w32 t.mem B (dA + 4 * i) : Int) (w32 t.mem B (dB + 4 * i) : Int)
    huv jc1 jc2 (by omega) (by omega) (by omega) (by omega)
  refine WP.mono hst fun t' ⟨⟨l5, l6, l7, l9, l8, lm⟩, lk⟩ => ⟨⟨?_, ?_, ?_, ?_, ?_, jk.trans' lk⟩, l8⟩
  · rw [l5, show dO + 4 * i + 4 = dO + 4 * (i + 1) by omega_arith]
  · rw [l6, show dA + 4 * i + 4 = dA + 4 * (i + 1) by omega_arith]
  · rw [l7, show dB + 4 * i + 4 = dB + 4 * (i + 1) by omega_arith]
  · rw [k11, k12, j9, setWidth_ofInt, setWidth_ofInt] at l9 lm
    refine ⟨_, e3, e4, l9.trans e1, ?_⟩
    have hx : ((t.mem.readW (off B (dA + 4 * i)) 32).toNat : Int) = (w32 t.mem B (dA + 4 * i) : Int) := rfl
    have hy : ((t.mem.readW (off B (dB + 4 * i)) 32).toNat : Int) = (w32 t.mem B (dB + 4 * i) : Int) := rfl
    have eP : (2 : Int) ^ (32 * (i + 1)) = 2 ^ 32 * 2 ^ (32 * i) := by
      rw [show 32 * (i + 1) = 32 * i + 32 by omega, Int.pow_add, Int.mul_comm]
    rw [lm, val32_write_top _ _ _ _ _ (by omega_arith), val32_succ s.mem B dB i, val32_succ s.mem B dA i,
      ← wa, ← wb, hx, hy, eP]
    push_cast
    generalize ((BitVec.ofInt 64 u * BitVec.ofInt 64 (w32 t.mem B (dA + 4 * i) : Int) +
      BitVec.ofInt 64 v * BitVec.ofInt 64 (w32 t.mem B (dB + 4 * i) : Int) + BitVec.ofInt 64 c').setWidth 32).toNat = L at e2 ⊢
    generalize (2 : Int) ^ (32 * i) = P at jeq ⊢
    grind
  · rw [lm]
    exact (jout.mono (Nat.le_refl _) (by omega_arith)).trans
      ((writeW32_outside _ B (d := dO + 4 * i) _ (by omega_arith)).mono (by omega_arith) (by omega_arith))

end VG.Proof.Rsa.PPC64LE.InvBatch
