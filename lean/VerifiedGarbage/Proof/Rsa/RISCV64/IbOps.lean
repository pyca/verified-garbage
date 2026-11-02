module

public import VerifiedGarbage.Impl.Rsa.RISCV64.InvBatch
public import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public import VerifiedGarbage.Proof.Divstep.WordDef
public import VerifiedGarbage.Proof.Rsa.RISCV64.IbLoops
public import VerifiedGarbage.Proof.Rsa.RISCV64.KeyLayout
import VerifiedGarbage.Proof.Divstep.Word
import VerifiedGarbage.Proof.Divstep.WordBasic
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Bignum.RISCV64.MontFinish64
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega

/-! # The batched inverse on RISC-V: the divsteps

`wstepCode_ok`: one divstep's code leaves in `t6`, `a4`, `t0`–`t4` the words
of `Proof/Divstep/WordDef.lean`'s `wstep` of their values; `wsteps_ok`: `k` of
them, `wsteps k`.
-/

@[expose] public section

namespace VG.Proof.Rsa.RISCV64.InvBatch

open VG VG.RISCV64 VG.Proof.Bignum.RISCV64 VG.Impl.Rsa.RISCV64.InvBatch
open VG.Proof.Divstep (WSt wstep)

/-- The words of a divstep: `d f g u v q r` in `t6`, `a4`, `t0`–`t4`. -/
def regsW (s : State) : WSt :=
  ⟨s.gpr .t6, s.gpr .a4, s.gpr .t0, s.gpr .t1, s.gpr .t2, s.gpr .t3, s.gpr .t4⟩

/-- The registers the divsteps and the array operations change. -/
abbrev kRegs : List Reg := [.t0, .t1, .t2, .t3, .t4, .t5, .t6, .a4, .a5, .a7]

theorem wstepCode_ok (s : State) :
    WP isa (.block wstepCode) s fun t => (regsW t = wstep (regsW s) ∧ t.mem = s.mem) ∧ Keep kRegs s t := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  brun [wstepCode, regsW, fin64_exec_li_zero]
  simp only [wstep, Divstep.shl1]
  rfl

/-- `k` divsteps, unrolled. -/
theorem wsteps_ok (k : Nat) (s : State) :
    WP isa (.block (wsteps k)) s fun t =>
      (regsW t = Divstep.wsteps k (regsW s) ∧ t.mem = s.mem) ∧ Keep kRegs s t := by
  induction k generalizing s with
  | zero => exact WP.block_nil ⟨⟨rfl, rfl⟩, Keep.refl _ _⟩
  | succ k ih =>
    rw [wsteps, List.replicate_succ, List.flatten_cons, WP.block_append_iff]
    refine WP.mono (wstepCode_ok s) fun t ⟨⟨e, m⟩, k₁⟩ => WP.mono (ih t) fun u ⟨⟨e₂, m₂⟩, k₂⟩ =>
      ⟨⟨by rw [e₂, e]; rfl, m₂.trans m⟩, Keep.trans' k₁ k₂⟩

end VG.Proof.Rsa.RISCV64.InvBatch

/-!
# The batched inverse on RISC-V: its digit loops

Over `n` digits of 32 bits at byte offsets of the working space, pointers in
`t0`–`t2` and the count in `t3`, as `IbLoops.lean`'s:

* `macLoop_ok`: `[o] := [a] + k [b]`, `k < 2^32` in `a5`, the carry in `t4`;
* `shrLoop_ok`: `[o] := [a] >> 30`, reading one digit more;
* `linLoop_ok`: `[o] := u [a] + v [b]` for signed `u`, `v` in `a5`, `a7`,
  the signed carry in `t4`.
-/

namespace VG.Proof.Rsa.RISCV64.InvBatch

open VG VG.RISCV64 VG.Proof.Mont VG.Proof.Bignum.RISCV64 VG.Impl.Bignum.RISCV64
open VG.Impl.Rsa.RISCV64.InvBatch (macBody shrBody linBody linTop)
open VG.Proof.Rsa.RISCV64.Loops (loopRegs)

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

/-- `[o] := [a] + k [m]` over `n` digits (`countLoop .t3 macBody`), from the
carry `c` in `t4`: the sum and the carry out. -/
theorem macLoop_ok {s : State} {B : Addr} {Z dO dA dM n : Nat} (hs : Scr s B Z)
    (h0 : s.gpr .t0 = off B dO) (h1 : s.gpr .t1 = off B dA) (h2 : s.gpr .t2 = off B dM)
    (h3 : s.gpr .t3 = BitVec.ofNat 64 n) (h4 : (s.gpr .t4).toNat < 2 ^ 32)
    (h5 : (s.gpr .a5).toNat < 2 ^ 32) (hn : 1 ≤ n) (hn' : n < 2 ^ 32)
    (hO4 : dO % 4 = 0) (hA4 : dA % 4 = 0) (hM4 : dM % 4 = 0)
    (hO : dO + 4 * n ≤ Z) (hA : dA + 4 * n ≤ Z) (hM : dM + 4 * n ≤ Z)
    (aA : Ahead dO dA n) (aM : Ahead dO dM n) :
    WP isa (countLoop .t3 macBody) s fun t =>
      (t.gpr .t4).toNat < 2 ^ 32 ∧
      val32 t.mem B dO n + 2 ^ (32 * n) * (t.gpr .t4).toNat =
        val32 s.mem B dA n + (s.gpr .a5).toNat * val32 s.mem B dM n + (s.gpr .t4).toNat ∧
      t.gpr .t0 = off B (dO + 4 * n) ∧ Outside B dO (4 * n) s.mem t.mem ∧ Keep loopRegs s t := by
  have hnw := hs.nowrap
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .t0 = off B (dO + 4 * i) ∧ t.gpr .t1 = off B (dA + 4 * i) ∧ t.gpr .t2 = off B (dM + 4 * i) ∧
      (t.gpr .t4).toNat < 2 ^ 32 ∧ Outside B dO (4 * i) s.mem t.mem ∧
      val32 t.mem B dO i + 2 ^ (32 * i) * (t.gpr .t4).toNat =
        val32 s.mem B dA i + (s.gpr .a5).toNat * val32 s.mem B dM i + (s.gpr .t4).toNat ∧
      Keep loopRegs s t
  refine WP.mono (wp_countdown (body := .block (macBody ++ ([.addi .t3 .t3 (-1)] : List Instr)))
    (cnt := .t3) (N := n) (by omega_arith) (by omega_arith) Inv
    (fun i hi t ⟨j0, j1, j2, j4, jout, jeq, jk⟩ hc => ?_)
    ⟨by rw [h0]; rfl, by rw [h1]; rfl, by rw [h2]; rfl, h4, Outside.refl _ _ _ _,
      by simp [val32], Keep.refl _ _⟩ h3)
    fun t ⟨j0, _, _, j4, jout, jeq, jk⟩ => ⟨j4, jeq, j0, jout, jk⟩
  have hs' := hs.congr jk.2.2
  have k5 : t.gpr .a5 = s.gpr .a5 := jk.gpr (by decide)
  have hst := (show WP isa (.block (macBody ++ ([.addi .t3 .t3 (-1)] : List Instr))) t fun t' =>
      let S := t.gpr .a5 * (t.mem.readW (off B (dM + 4 * i)) 32).setWidth 64 +
        (t.mem.readW (off B (dA + 4 * i)) 32).setWidth 64 + t.gpr .t4
      (t'.gpr .t0 = off B (dO + 4 * i + 4) ∧ t'.gpr .t1 = off B (dA + 4 * i + 4) ∧
        t'.gpr .t2 = off B (dM + 4 * i + 4) ∧ t'.gpr .t4 = S >>> 32 ∧
        t'.gpr .t3 = t.gpr .t3 - BitVec.ofNat 64 1 ∧
        t'.mem = t.mem.writeW (off B (dO + 4 * i)) (S.setWidth 32)) ∧ Keep loopRegs t t' from by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [macBody, j0, j1, j2, exec_load_w, exec_store_w,
      hs'.ld (show dA + 4 * i + 4 ≤ Z by omega_arith), hs'.ld (show dM + 4 * i + 4 ≤ Z by omega_arith),
      hs'.st (show dO + 4 * i + 4 ≤ Z by omega_arith),
      Scr.al4 hs' (show dA + 4 * i + 4 ≤ Z by omega_arith) (by omega_arith),
      Scr.al4 hs' (show dM + 4 * i + 4 ≤ Z by omega_arith) (by omega_arith),
      Scr.al4 hs' (show dO + 4 * i + 4 ≤ Z by omega_arith) (by omega_arith)])
  refine WP.mono hst fun t' ⟨⟨l0, l1, l2, l4, l3, lm⟩, lk⟩ => ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, Keep.trans' jk lk⟩, l3⟩
  · rw [l0, show dO + 4 * i + 4 = dO + 4 * (i + 1) by omega_arith]
  · rw [l1, show dA + 4 * i + 4 = dA + 4 * (i + 1) by omega_arith]
  · rw [l2, show dM + 4 * i + 4 = dM + 4 * (i + 1) by omega_arith]
  · rw [l4]; exact (mac_arith _ _ _ _ (by rw [k5]; exact h5) j4).1
  · rw [lm]; exact out_step32 _ jout (by omega_arith)
  · have wa : w32 t.mem B (dA + 4 * i) = w32 s.mem B (dA + 4 * i) :=
      jout.w32 (by have := aA.outside hi; omega_arith) (by omega_arith)
    have wm : w32 t.mem B (dM + 4 * i) = w32 s.mem B (dM + 4 * i) :=
      jout.w32 (by have := aM.outside hi; omega_arith) (by omega_arith)
    have k : _ = w32 t.mem B (dA + 4 * i) + (t.gpr .a5).toNat * w32 t.mem B (dM + 4 * i) + (t.gpr .t4).toNat :=
      (mac_arith (t.gpr .a5) (t.mem.readW (off B (dM + 4 * i)) 32)
        (t.mem.readW (off B (dA + 4 * i)) 32) _ (by rw [k5]; exact h5) j4).2
    rw [lm, l4, val32_write_top _ _ _ _ _ (by omega_arith), val32_succ s.mem B dM i, val32_succ s.mem B dA i,
      ← pow32_mul i, ← wa, ← wm, ← k5]
    rw [k5] at k
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

/-- `[o] := [a] >> 30` over `n` digits (`countLoop .t3 shrBody`), reading `n + 1`
digits of `a`, apart from `o`. -/
theorem shrLoop_ok {s : State} {B : Addr} {Z dO dA n : Nat} (hs : Scr s B Z)
    (h0 : s.gpr .t0 = off B dO) (h1 : s.gpr .t1 = off B dA) (h3 : s.gpr .t3 = BitVec.ofNat 64 n)
    (hn : 1 ≤ n) (hn' : n < 2 ^ 32) (hO4 : dO % 4 = 0) (hA4 : dA % 4 = 0)
    (hO : dO + 4 * n ≤ Z) (hA : dA + 4 * (n + 1) ≤ Z)
    (sep : dO + 4 * n ≤ dA ∨ dA + 4 * (n + 1) ≤ dO) :
    WP isa (countLoop .t3 shrBody) s fun t =>
      val32 t.mem B dO n + 2 ^ (32 * n) * (w32 s.mem B (dA + 4 * n) / 2 ^ 30) =
        val32 s.mem B dA (n + 1) / 2 ^ 30 ∧
      Outside B dO (4 * n) s.mem t.mem ∧ Keep loopRegs s t := by
  have hnw := hs.nowrap
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .t0 = off B (dO + 4 * i) ∧ t.gpr .t1 = off B (dA + 4 * i) ∧ Outside B dO (4 * i) s.mem t.mem ∧
      val32 t.mem B dO i + 2 ^ (32 * i) * (w32 s.mem B (dA + 4 * i) / 2 ^ 30) =
        val32 s.mem B dA (i + 1) / 2 ^ 30 ∧ Keep loopRegs s t
  refine WP.mono (wp_countdown (body := .block (shrBody ++ ([.addi .t3 .t3 (-1)] : List Instr)))
    (cnt := .t3) (N := n) (by omega_arith) (by omega_arith) Inv
    (fun i hi t ⟨j0, j1, jout, jeq, jk⟩ hc => ?_)
    ⟨by rw [h0]; rfl, by rw [h1]; rfl, Outside.refl _ _ _ _,
      by simp only [val32, Nat.mul_zero, Nat.add_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add], Keep.refl _ _⟩ h3)
    fun t ⟨_, _, jout, jeq, jk⟩ => ⟨jeq, jout, jk⟩
  have hs' := hs.congr jk.2.2
  have hst := (show WP isa (.block (shrBody ++ ([.addi .t3 .t3 (-1)] : List Instr))) t fun t' =>
      (t'.gpr .t0 = off B (dO + 4 * i + 4) ∧ t'.gpr .t1 = off B (dA + 4 * i + 4) ∧
        t'.gpr .t3 = t.gpr .t3 - BitVec.ofNat 64 1 ∧
        t'.mem = t.mem.writeW (off B (dO + 4 * i))
          (((t.mem.readW (off B (dA + 4 * i)) 32).setWidth 64 >>> 30 +
            (t.mem.readW (off B (dA + 4 * i + 4)) 32).setWidth 64 <<< 2).setWidth 32)) ∧
        Keep loopRegs t t' from by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [shrBody, j0, j1, exec_load_w, exec_store_w,
      hs'.ld (show dA + 4 * i + 4 ≤ Z by omega_arith), hs'.ld (show dA + 4 * i + 4 + 4 ≤ Z by omega_arith),
      hs'.st (show dO + 4 * i + 4 ≤ Z by omega_arith),
      Scr.al4 hs' (show dA + 4 * i + 4 ≤ Z by omega_arith) (by omega_arith),
      Scr.al4 hs' (show dA + 4 * i + 4 + 4 ≤ Z by omega_arith) (by omega_arith),
      Scr.al4 hs' (show dO + 4 * i + 4 ≤ Z by omega_arith) (by omega_arith)])
  refine WP.mono hst fun t' ⟨⟨l0, l1, l3, lm⟩, lk⟩ => ⟨⟨?_, ?_, ?_, ?_, Keep.trans' jk lk⟩, l3⟩
  · rw [l0, show dO + 4 * i + 4 = dO + 4 * (i + 1) by omega_arith]
  · rw [l1, show dA + 4 * i + 4 = dA + 4 * (i + 1) by omega_arith]
  · rw [lm]; exact out_step32 _ jout (by omega_arith)
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

/-- A 64-bit sum `T` of a small `t`: its low digit, and its arithmetic shift
by 32, `t / 2^32`. -/
theorem lin_core (t : Int) (h1 : -2 ^ 63 ≤ t) (h2 : t < 2 ^ 63) :
    let T := BitVec.ofInt 64 t
    T.sshiftRight 32 = BitVec.ofInt 64 (t / 2 ^ 32) ∧
      ((T.setWidth 32).toNat : Int) + 2 ^ 32 * (t / 2 ^ 32) = t := by
  intro T
  have hT : (T.toNat : Int) = t % 2 ^ 64 := Divstep.toNat_ofInt64 t
  refine ⟨BitVec.eq_of_toInt_eq ?_, ?_⟩
  · rw [BitVec.toInt_sshiftRight, BitVec.toInt_ofInt, BitVec.toInt_ofInt, Int.shiftRight_eq_div_pow,
      Int.bmod_eq_of_le (by omega) (by omega), Int.bmod_eq_of_le (by omega) (by omega)]
    simp only [Nat.cast_pow, Nat.cast_ofNat]
  · rw [BitVec.toNat_setWidth]
    omega

/-- `x`, sign-extended from 32 bits by `addiw`. -/
theorem sext_arith (x : BitVec 32) :
    sext32 ((x.setWidth 64).setWidth 32 + BitVec.ofNat 32 0) = BitVec.ofInt 64 x.toInt := by
  rw [lo32_ext, BitVec.add_zero]
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_signExtend, BitVec.toInt_ofInt, show min 64 32 = 32 from rfl]
  have h1 := x.toInt_le
  have h2 := x.le_toInt
  simp only [Nat.reduceSub] at h1 h2
  rw [Int.bmod_eq_of_le (by omega) (by omega), Int.bmod_eq_of_le (by omega) (by omega)]

/-- `|u X| ≤ |u| 2^32` for `|X| ≤ 2^32`. -/
theorem small_mul {u X : Int} (hX1 : -2 ^ 32 ≤ X) (hX2 : X ≤ 2 ^ 32) :
    (u * X).natAbs ≤ u.natAbs * 2 ^ 32 := by
  rw [Int.natAbs_mul]
  exact Nat.mul_le_mul_left _ (by omega)

/-- A digit of `u x + v y + c`, on bit vectors: the low digit of the 64-bit
sum and its arithmetic shift by 32, for `x`, `y` between `-2^31` and `2^32`. -/
theorem lin_arith (u v c X Y : Int) (huv : u.natAbs + v.natAbs ≤ 2 ^ 30) (hc1 : -2 ^ 31 ≤ c)
    (hc2 : c ≤ 2 ^ 31) (hX1 : -2 ^ 31 ≤ X) (hX2 : X < 2 ^ 32) (hY1 : -2 ^ 31 ≤ Y) (hY2 : Y < 2 ^ 32) :
    let T := BitVec.ofInt 64 u * BitVec.ofInt 64 X + BitVec.ofInt 64 v * BitVec.ofInt 64 Y + BitVec.ofInt 64 c
    let t := u * X + v * Y + c
    T.sshiftRight 32 = BitVec.ofInt 64 (t / 2 ^ 32) ∧
      ((T.setWidth 32).toNat : Int) + 2 ^ 32 * (t / 2 ^ 32) = t ∧ -2 ^ 31 ≤ t / 2 ^ 32 ∧ t / 2 ^ 32 ≤ 2 ^ 31 := by
  intro T t
  have eT : T = BitVec.ofInt 64 t := by simp only [T, t, BitVec.ofInt_add, BitVec.ofInt_mul]
  have a := small_mul (u := u) (X := X) (by omega) (by omega)
  have b := small_mul (u := v) (X := Y) (by omega) (by omega)
  obtain ⟨e1, e2⟩ := lin_core t (by omega) (by omega)
  rw [eT]
  exact ⟨e1, e2, by omega, by omega⟩

/-- `[o] := u [a] + v [b]` over `n` digits (`countLoop .t3 linBody`), for
`|u|, |v| ≤ 2^30` in `a5`, `a7`, from the signed carry `c` in `t4`: the
combination and the carry out. -/
theorem linLoop_ok {s : State} {B : Addr} {Z dO dA dB n : Nat} (hs : Scr s B Z) {u v c : Int}
    (h0 : s.gpr .t0 = off B dO) (h1 : s.gpr .t1 = off B dA) (h2 : s.gpr .t2 = off B dB)
    (h3 : s.gpr .t3 = BitVec.ofNat 64 n) (h4 : s.gpr .t4 = BitVec.ofInt 64 c)
    (h5 : s.gpr .a5 = BitVec.ofInt 64 u) (h7 : s.gpr .a7 = BitVec.ofInt 64 v)
    (huv : u.natAbs + v.natAbs ≤ 2 ^ 30)
    (hc1 : -2 ^ 31 ≤ c) (hc2 : c ≤ 2 ^ 31) (hn : 1 ≤ n) (hn' : n < 2 ^ 32)
    (hO4 : dO % 4 = 0) (hA4 : dA % 4 = 0) (hB4 : dB % 4 = 0)
    (hO : dO + 4 * n ≤ Z) (hA : dA + 4 * n ≤ Z) (hB : dB + 4 * n ≤ Z)
    (aA : Ahead dO dA n) (aB : Ahead dO dB n) :
    WP isa (countLoop .t3 linBody) s fun t =>
      (∃ c' : Int, -2 ^ 31 ≤ c' ∧ c' ≤ 2 ^ 31 ∧ t.gpr .t4 = BitVec.ofInt 64 c' ∧
        (val32 t.mem B dO n : Int) + 2 ^ (32 * n) * c' =
          u * val32 s.mem B dA n + v * val32 s.mem B dB n + c) ∧
      t.gpr .t0 = off B (dO + 4 * n) ∧ t.gpr .t1 = off B (dA + 4 * n) ∧ t.gpr .t2 = off B (dB + 4 * n) ∧
      Outside B dO (4 * n) s.mem t.mem ∧ Keep loopRegs s t := by
  have hnw := hs.nowrap
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .t0 = off B (dO + 4 * i) ∧ t.gpr .t1 = off B (dA + 4 * i) ∧ t.gpr .t2 = off B (dB + 4 * i) ∧
      (∃ c' : Int, -2 ^ 31 ≤ c' ∧ c' ≤ 2 ^ 31 ∧ t.gpr .t4 = BitVec.ofInt 64 c' ∧
        (val32 t.mem B dO i : Int) + 2 ^ (32 * i) * c' =
          u * val32 s.mem B dA i + v * val32 s.mem B dB i + c) ∧
      Outside B dO (4 * i) s.mem t.mem ∧ Keep loopRegs s t
  refine WP.mono (wp_countdown (body := .block (linBody ++ ([.addi .t3 .t3 (-1)] : List Instr)))
    (cnt := .t3) (N := n) (by omega_arith) (by omega_arith) Inv
    (fun i hi t ⟨j0, j1, j2, ⟨c', jc1, jc2, j4, jeq⟩, jout, jk⟩ hc => ?_)
    ⟨by rw [h0]; rfl, by rw [h1]; rfl, by rw [h2]; rfl,
      ⟨c, hc1, hc2, h4, by simp [val32]⟩, Outside.refl _ _ _ _, Keep.refl _ _⟩ h3)
    fun t ⟨j0, j1, j2, jc, jout, jk⟩ => ⟨jc, j0, j1, j2, jout, jk⟩
  have hs' := hs.congr jk.2.2
  have k5 : t.gpr .a5 = BitVec.ofInt 64 u := (jk.gpr (by decide)).trans h5
  have k7 : t.gpr .a7 = BitVec.ofInt 64 v := (jk.gpr (by decide)).trans h7
  have hst := (show WP isa (.block (linBody ++ ([.addi .t3 .t3 (-1)] : List Instr))) t fun t' =>
      let T := t.gpr .a5 * (t.mem.readW (off B (dA + 4 * i)) 32).setWidth 64 +
        t.gpr .a7 * (t.mem.readW (off B (dB + 4 * i)) 32).setWidth 64 + t.gpr .t4
      (t'.gpr .t0 = off B (dO + 4 * i + 4) ∧ t'.gpr .t1 = off B (dA + 4 * i + 4) ∧
        t'.gpr .t2 = off B (dB + 4 * i + 4) ∧ t'.gpr .t4 = T.sshiftRight 32 ∧
        t'.gpr .t3 = t.gpr .t3 - BitVec.ofNat 64 1 ∧
        t'.mem = t.mem.writeW (off B (dO + 4 * i)) (T.setWidth 32)) ∧ Keep loopRegs t t' from by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [linBody, j0, j1, j2, exec_load_w, exec_store_w,
      hs'.ld (show dA + 4 * i + 4 ≤ Z by omega_arith), hs'.ld (show dB + 4 * i + 4 ≤ Z by omega_arith),
      hs'.st (show dO + 4 * i + 4 ≤ Z by omega_arith),
      Scr.al4 hs' (show dA + 4 * i + 4 ≤ Z by omega_arith) (by omega_arith),
      Scr.al4 hs' (show dB + 4 * i + 4 ≤ Z by omega_arith) (by omega_arith),
      Scr.al4 hs' (show dO + 4 * i + 4 ≤ Z by omega_arith) (by omega_arith)])
  have wa : w32 t.mem B (dA + 4 * i) = w32 s.mem B (dA + 4 * i) :=
    jout.w32 (by have := aA.outside hi; omega_arith) (by omega_arith)
  have wb : w32 t.mem B (dB + 4 * i) = w32 s.mem B (dB + 4 * i) :=
    jout.w32 (by have := aB.outside hi; omega_arith) (by omega_arith)
  have xa : w32 t.mem B (dA + 4 * i) < 2 ^ 32 := (t.mem.readW (off B (dA + 4 * i)) 32).isLt
  have xb : w32 t.mem B (dB + 4 * i) < 2 ^ 32 := (t.mem.readW (off B (dB + 4 * i)) 32).isLt
  obtain ⟨e1, e2, e3, e4⟩ := lin_arith u v c' (w32 t.mem B (dA + 4 * i) : Int) (w32 t.mem B (dB + 4 * i) : Int)
    huv jc1 jc2 (by omega) (by omega) (by omega) (by omega)
  refine WP.mono hst fun t' ⟨⟨l0, l1, l2, l4, l3, lm⟩, lk⟩ => ⟨⟨?_, ?_, ?_, ?_, ?_, Keep.trans' jk lk⟩, l3⟩
  · rw [l0, show dO + 4 * i + 4 = dO + 4 * (i + 1) by omega_arith]
  · rw [l1, show dA + 4 * i + 4 = dA + 4 * (i + 1) by omega_arith]
  · rw [l2, show dB + 4 * i + 4 = dB + 4 * (i + 1) by omega_arith]
  · rw [k5, k7, j4, setWidth_ofInt, setWidth_ofInt] at l4 lm
    refine ⟨_, e3, e4, l4.trans e1, ?_⟩
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
  · rw [lm]; exact out_step32 _ jout (by omega_arith)

end VG.Proof.Rsa.RISCV64.InvBatch

/-!
# The batched inverse on RISC-V: its operations on arrays

In the key operations' working space (`Ws`), with `n` in `s8` (`Ctx`): each
operation of `Impl/Rsa/RISCV64/InvBatch.lean` on `n + 1` (or `n + 2`) digits
of arrays, signed numbers read by `sv` (the low digits and a signed top
digit).
-/

namespace VG.Proof.Rsa.RISCV64.InvBatch

open VG VG.RISCV64 VG.Proof.Mont VG.Proof.Bignum.RISCV64 VG.Proof.Rsa.RISCV64.Keys VG.Impl.Bignum.RISCV64
open VG.Impl.Rsa.RISCV64.Keys (ptr seqs mov)
open VG.Impl.Rsa.RISCV64.InvBatch
open VG.Proof.Rsa.RISCV64.Loops (loopRegs)
open VG.RISCV64.RegUpd

/-! ## The context -/

/-- The working space, and `n` in `s8`. -/
structure Ctx (s : State) (B : Addr) (Z w N n : Nat) : Prop where
  ws : Ws s B Z w N
  s8 : s.gpr .s8 = BitVec.ofNat 64 n
  npos : 1 ≤ n
  nw : n ≤ 2 * w
  room : 15 ≤ N
  wbig : 4 ≤ w

theorem Ctx.of_keep {s t : State} {B : Addr} {Z w N n : Nat} (h : Ctx s B Z w N n)
    (k : Keep kRegs s t) : Ctx t B Z w N n :=
  ⟨h.ws.of_keep k, (k.gpr (by decide)).trans h.s8, h.npos, h.nw, h.room, h.wbig⟩

/-- An array's offset is a multiple of 4. -/
theorem arr_al4 (w j : Nat) : arr w j % 4 = 0 := by
  have := arr_al w j; omega

/-! ## Signed numbers -/

/-- `k + 1` digits at `d`, the top one signed. -/
def sv (m : Mem) (B : Addr) (d k : Nat) : Int :=
  (val32 m B d k : Int) + 2 ^ (32 * k) * (m.readW (off B (d + 4 * k)) 32).toInt

theorem toInt_cond (x : BitVec 32) : (x.toInt : Int) = x.toNat - if 2 ^ 31 ≤ x.toNat then 2 ^ 32 else 0 := by
  rw [BitVec.toInt_eq_toNat_cond]
  have := x.isLt
  split <;> split <;> omega

/-- The digits read unsigned. -/
theorem val_sv (m : Mem) (B : Addr) (d k : Nat) :
    (val32 m B d (k + 1) : Int) = sv m B d k +
      2 ^ (32 * (k + 1)) * (if 2 ^ 31 ≤ w32 m B (d + 4 * k) then 1 else 0) := by
  rw [sv, val32_succ, toInt_cond, show 32 * (k + 1) = 32 * k + 32 by omega, Int.pow_add]
  push_cast
  split <;> grind

theorem sv_range (m : Mem) (B : Addr) (d k : Nat) :
    -2 ^ (32 * k + 31) ≤ sv m B d k ∧ sv m B d k < 2 ^ (32 * k + 31) := by
  have hv := val32_lt m B d k
  have ht1 := (m.readW (off B (d + 4 * k)) 32).toInt_le
  have ht2 := (m.readW (off B (d + 4 * k)) 32).le_toInt
  rw [sv, Int.pow_add]
  generalize (m.readW (off B (d + 4 * k)) 32).toInt = T at ht1 ht2 ⊢
  have hP : (0 : Int) < 2 ^ (32 * k) := by exact_mod_cast Nat.two_pow_pos _
  have hv' : (val32 m B d k : Int) < 2 ^ (32 * k) := by exact_mod_cast hv
  generalize (2 : Int) ^ (32 * k) = P at hP hv' ⊢
  have ht1' : T ≤ 2 ^ 31 - 1 := by simpa using ht1
  have ht2' : -2 ^ 31 ≤ T := by simpa using ht2
  constructor
  · have := Int.mul_le_mul_of_nonneg_left ht2' (Int.le_of_lt hP); grind
  · have := Int.mul_le_mul_of_nonneg_left ht1' (Int.le_of_lt hP); grind

/-- A multiple of `H > 0` strictly between `-H` and `H` is zero. -/
theorem mul_small {H d : Int} (hH : 0 < H) (h1 : -H < H * d) (h2 : H * d < H) : d = 0 := by
  rcases Int.lt_trichotomy d 0 with hd | hd | hd
  · have := Int.mul_le_mul_of_nonneg_left (show d ≤ -1 by omega) (Int.le_of_lt hH); omega
  · exact hd
  · have := Int.mul_le_mul_of_nonneg_left (show 1 ≤ d by omega) (Int.le_of_lt hH); omega

/-- A signed number from the unsigned digits of it, plus a multiple of
`2^(32 (k + 1))`. -/
theorem sv_of_eq {m : Mem} {B : Addr} {d k : Nat} {z q : Int}
    (h : (val32 m B d (k + 1) : Int) = z + 2 ^ (32 * (k + 1)) * q)
    (hz1 : -2 ^ (32 * k + 31) ≤ z) (hz2 : z < 2 ^ (32 * k + 31)) : sv m B d k = z := by
  have e := val_sv m B d k
  have r := sv_range m B d k
  rw [e] at h
  have eP : (2 : Int) ^ (32 * (k + 1)) = 2 * 2 ^ (32 * k + 31) := by
    rw [show 32 * (k + 1) = (32 * k + 31) + 1 by omega, Int.pow_succ, Int.mul_comm]
  have hH : (0 : Int) < 2 ^ (32 * k + 31) := by exact_mod_cast Nat.two_pow_pos _
  rw [eP] at h
  generalize (2 : Int) ^ (32 * k + 31) = H at h hz1 hz2 r hH
  generalize sv m B d k = x at h r ⊢
  generalize (if 2 ^ 31 ≤ w32 m B (d + 4 * k) then (1 : Int) else 0) = b at h
  have h0 : (2 * H) * (b - q) = z - x := by grind
  have := mul_small (H := 2 * H) (d := b - q) (by omega) (by omega) (by omega)
  rw [this, Int.mul_zero] at h0
  omega

/-- The first `k` digits (`4 k ≤ S w`) of an array outside a frame. -/
theorem keep_val {B : Addr} {w : Nat} {js ds : List Nat} {m m' : Mem}
    (h : Keys.Frame B w js ds m m') {j k : Nat} (hk : 4 * k ≤ S w) (hj : ∀ x ∈ js, x ≠ j)
    (hd : ∀ d ∈ ds, d + 8 ≤ hdr) (fit : arr w j + S w ≤ 2 ^ 64) :
    val32 m' B (arr w j) k = val32 m B (arr w j) k := by
  refine Outs.val32 h (fun r hr => ?_) (by omega)
  simp only [ranges, List.mem_append, List.mem_map] at hr
  rcases hr with ⟨x, hx, rfl⟩ | ⟨d, hd', rfl⟩
  · have := arr_disj (w := w) (hj x hx); dsimp only; omega
  · have := hd d hd'; have : hdr ≤ arr w j := hdr_le_arr w j; dsimp only; omega

/-- A word of `≤ 8` bytes inside an array outside a frame. -/
theorem keep_word {B : Addr} {w : Nat} {js ds : List Nat} {m m' : Mem}
    (h : Keys.Frame B w js ds m m') {j o b : Nat} (hb : o + b / 8 ≤ S w) (hj : ∀ x ∈ js, x ≠ j)
    (hd : ∀ d ∈ ds, d + 8 ≤ hdr) (fit : arr w j + S w ≤ 2 ^ 64) :
    m'.readW (off B (arr w j + o)) b = m.readW (off B (arr w j + o)) b := by
  refine Mem.readW_congr fun i hi => h _ fun r hr => ?_
  rw [ofs_off B (by omega)]
  simp only [ranges, List.mem_append, List.mem_map] at hr
  rcases hr with ⟨x, hx, rfl⟩ | ⟨d, hd', rfl⟩
  · have := arr_disj (w := w) (hj x hx); dsimp only; omega
  · have := hd d hd'; have : hdr ≤ arr w j := hdr_le_arr w j; dsimp only; omega

/-- A signed number of `k + 1` digits (`4 (k + 1) ≤ S w`) in an array outside a frame. -/
theorem keep_sv {B : Addr} {w : Nat} {js ds : List Nat} {m m' : Mem}
    (h : Keys.Frame B w js ds m m') {j k : Nat} (hk : 4 * (k + 1) ≤ S w) (hj : ∀ x ∈ js, x ≠ j)
    (hd : ∀ d ∈ ds, d + 8 ≤ hdr) (fit : arr w j + S w ≤ 2 ^ 64) :
    sv m' B (arr w j) k = sv m B (arr w j) k := by
  unfold sv
  rw [keep_val h (by omega) hj hd fit, keep_word h (o := 4 * k) (b := 32) (by omega) hj hd fit]

/-! ## Blocks -/

/-- `ldW r o`: `r` := the window's 64-bit word at `o`. -/
theorem ldW_ok {s : State} {B : Addr} {Z w N n : Nat} (h : Ctx s B Z w N n) {r : Reg}
    (h10 : r ≠ .s10) (h11 : r ≠ .s11) {o : Nat} (ho : o + 8 ≤ 48) (ho8 : o % 8 = 0) {rest : List Instr}
    {Q : State → Prop} (k : WP isa (.block rest) (s.write r (s.mem.readW (off B (arr w aW + o)) 64)) Q) :
    WP isa (.block (ldW r o ++ rest)) s Q := by
  have fit := h.ws.arr_fit (j := aW) (by have := h.room; unfold aW; omega)
  have hS : S w = 8 * (w + 2) := rfl
  have := h.wbig
  rw [ldW, List.append_assoc]
  refine ptr_ok h.ws h10 h11 (by decide) ?_
  rw [WP.block_append_iff]
  have hs := h.ws.scr
  have hl : InRegions ((s.write r (off B (arr w aW))).rd ++ (s.write r (off B (arr w aW))).wr)
      ((s.write r (off B (arr w aW))).gpr r + BitVec.ofNat 64 o) 8 := by
    simp only [gpr_write, ↓reduceIte, rd_write, wr_write, off_add]
    exact hs.ld (d := arr w aW + o) (n := 8) (by omega)
  have ha : ((s.write r (off B (arr w aW))).gpr r + BitVec.ofNat 64 o).toNat % 8 = 0 := by
    simp only [gpr_write, ↓reduceIte, off_add]
    exact hs.al8 (by omega) (by have := arr_al w aW; omega)
  refine WP.of_runBlock ?_
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_load_d (by omega) ha hl,
    gpr_write, ↓reduceIte, off_add, mem_write, Option.some.injEq, exists_eq_left', write_write]
  exact k

/-- A digit outside the bytes that changed, read as a bit vector. -/
theorem Outside.readW32 {base : Addr} {o n : Nat} {m m' : Mem}
    (h : Outside base o n m m') {d : Nat} (hd : d + 4 ≤ o ∨ o + n ≤ d) (hd' : d + 4 ≤ 2 ^ 64) :
    m'.readW (off base d) 32 = m.readW (off base d) 32 :=
  Mem.readW_congr fun _ _ => h _ (by rw [ofs_off base (by omega)]; omega)

/-! ## `lin` -/

theorem toInt_low {q : Int} (h1 : -2 ^ 31 ≤ q) (h2 : q < 2 ^ 31) :
    ((BitVec.ofInt 64 q).setWidth 32).toInt = q := by
  have e := Divstep.toNat_ofInt64 q
  rw [toInt_cond, BitVec.toNat_setWidth]
  have := (BitVec.ofInt 64 q).isLt
  split <;> omega

/-- The top digit of `u [a] + v [b]`, both signed, and the carry after it. -/
theorem linTop_ok {s : State} {B : Addr} {Z dO dA dB : Nat} (hs : Scr s B Z) {u v c : Int}
    (h0 : s.gpr .t0 = off B dO) (h1 : s.gpr .t1 = off B dA) (h2 : s.gpr .t2 = off B dB)
    (h4 : s.gpr .t4 = BitVec.ofInt 64 c) (h5 : s.gpr .a5 = BitVec.ofInt 64 u)
    (h7 : s.gpr .a7 = BitVec.ofInt 64 v) (huv : u.natAbs + v.natAbs ≤ 2 ^ 30)
    (hc1 : -2 ^ 31 ≤ c) (hc2 : c ≤ 2 ^ 31) (hO4 : dO % 4 = 0) (hA4 : dA % 4 = 0) (hB4 : dB % 4 = 0)
    (hO : dO + 8 ≤ Z) (hA : dA + 4 ≤ Z) (hB : dB + 4 ≤ Z) :
    WP isa (.block linTop) s fun t =>
      ((∃ q : Int, -2 ^ 31 ≤ q ∧ q < 2 ^ 31 ∧
        (w32 t.mem B dO : Int) + 2 ^ 32 * q =
          u * (s.mem.readW (off B dA) 32).toInt + v * (s.mem.readW (off B dB) 32).toInt + c ∧
        (t.mem.readW (off B (dO + 4)) 32).toInt = q) ∧ Outside B dO 8 s.mem t.mem) ∧
      Keep [.t4, .t5, .t6] s t := by
  have hnw := hs.nowrap
  refine WP.keep _ ?_ (by rfl) (by rfl)
  brun [linTop, h0, h1, h2, h4, h5, h7, exec_load_w, exec_store_w, exec_addiw,
    hs.ld (show dA + 4 ≤ Z by omega), hs.ld (show dB + 4 ≤ Z by omega),
    hs.st (show dO + 4 ≤ Z by omega), hs.st (show dO + 4 + 4 ≤ Z by omega),
    Scr.al4 hs (show dA + 4 ≤ Z by omega) hA4, Scr.al4 hs (show dB + 4 ≤ Z by omega) hB4,
    Scr.al4 hs (show dO + 4 ≤ Z by omega) hO4, Scr.al4 hs (show dO + 4 + 4 ≤ Z by omega) (by omega),
    sext_arith]
  have xa1 := (s.mem.readW (off B dA) 32).toInt_le
  have xa2 := (s.mem.readW (off B dA) 32).le_toInt
  have xb1 := (s.mem.readW (off B dB) 32).toInt_le
  have xb2 := (s.mem.readW (off B dB) 32).le_toInt
  generalize (s.mem.readW (off B dA) 32).toInt = X at xa1 xa2 ⊢
  generalize (s.mem.readW (off B dB) 32).toInt = Y at xb1 xb2 ⊢
  obtain ⟨e1, e2, -, -⟩ := lin_arith u v c X Y huv hc1 hc2 (by omega) (by omega) (by omega) (by omega)
  have a : (u * X).natAbs ≤ u.natAbs * 2 ^ 31 := by
    rw [Int.natAbs_mul]; exact Nat.mul_le_mul_left _ (by omega)
  have b : (v * Y).natAbs ≤ v.natAbs * 2 ^ 31 := by
    rw [Int.natAbs_mul]; exact Nat.mul_le_mul_left _ (by omega)
  rw [e1]
  refine ⟨⟨(u * X + v * Y + c) / 2 ^ 32, by omega, by omega, ?_, ?_⟩, ?_⟩
  · rw [(writeW32_outside _ B (d := dO + 4) _ (by omega)).w32 (by omega) (by omega), w32_write_self]
    exact e2
  · rw [Mem.readW_writeW_self32]
    exact toInt_low (by omega) (by omega)
  · exact ((writeW32_outside _ B (d := dO) _ (by omega)).mono (by omega) (by omega)).trans
      ((writeW32_outside _ B (d := dO + 4) _ (by omega)).mono (by omega) (by omega))

/-- Arrays apart are each ahead of the other, for `k` digits (`4 k ≤ S w`). -/
theorem ahead_k {w o a k : Nat} (h : o ≠ a) (hk : 4 * k ≤ S w) : Ahead (arr w o) (arr w a) k := by
  have := arr_disj (w := w) h
  unfold Ahead; omega

/-- Arrays equal or apart: `o` is ahead of `a`, for `k` digits (`4 k ≤ S w`). -/
theorem ahead_any (w o a k : Nat) (hk : 4 * k ≤ S w) : Ahead (arr w o) (arr w a) k := by
  by_cases e : o = a
  · subst e; exact .inl (Nat.le_refl _)
  · exact ahead_k e hk

theorem ofNat_succ (n : Nat) : BitVec.ofNat 64 n + BitVec.ofNat 64 1 = BitVec.ofNat 64 (n + 1) :=
  (BitVec.ofNat_add n 1).symm

/-! ## Counts -/

theorem cntN_ok {t : State} {B : Addr} {Z w N n : Nat} (h : Ctx t B Z w N n) :
    WP isa (.block cntN) t fun x => (x.gpr .t3 = BitVec.ofNat 64 n ∧ x.mem = t.mem) ∧ Keep [.t3] t x := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  brun [cntN, mov, h.s8, add_ofNat_zero']

theorem cntN1_ok {t : State} {B : Addr} {Z w N n : Nat} (h : Ctx t B Z w N n) :
    WP isa (.block cntN1) t fun x => (x.gpr .t3 = BitVec.ofNat 64 (n + 1) ∧ x.mem = t.mem) ∧ Keep [.t3] t x := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  brun [cntN1, h.s8, ofNat_succ]

/-- The pointers of three arrays, a count and no carry. -/
theorem setup_ok {s : State} {B : Addr} {Z w N n : Nat} (h : Ctx s B Z w N n) {o a b K : Nat}
    {cnt : List Instr} (hcnt : ∀ t, Ctx t B Z w N n → WP isa (.block cnt) t fun x =>
      (x.gpr .t3 = BitVec.ofNat 64 K ∧ x.mem = t.mem) ∧ Keep [.t3] t x)
    (ho : o < 2048) (ha : a < 2048) (hb : b < 2048) :
    WP isa (.block (ptr .t0 o ++ ptr .t1 a ++ ptr .t2 b ++ cnt ++ ([.li .t4 0] : List Instr))) s fun t =>
      Ctx t B Z w N n ∧ t.mem = s.mem ∧ t.gpr .t0 = off B (arr w o) ∧ t.gpr .t1 = off B (arr w a) ∧
      t.gpr .t2 = off B (arr w b) ∧ t.gpr .t3 = BitVec.ofNat 64 K ∧ t.gpr .t4 = 0 ∧
      Keep [.t0, .t1, .t2, .t3, .t4] s t := by
  rw [show ptr .t0 o ++ ptr .t1 a ++ ptr .t2 b ++ cnt ++ ([.li .t4 0] : List Instr) =
    VG.Impl.Rsa.RISCV64.Keys.ptrs o a b ++ (cnt ++ ([.li .t4 0] : List Instr)) by
      simp only [VG.Impl.Rsa.RISCV64.Keys.ptrs, List.append_assoc]]
  refine ptrs_ok h.ws ho ha hb fun t p0 p1 p2 kt mt => ?_
  have ht := h.of_keep (kt.mono (by decide))
  rw [WP.block_append_iff]
  refine WP.mono (hcnt t ht) fun x ⟨⟨x3, xm⟩, kx⟩ => ?_
  refine WP.mono (WP.keep [.t4] (Q := fun y => y.gpr .t4 = 0 ∧ y.mem = x.mem) (by brun [fin64_exec_li_zero]; try rfl) (by rfl) (by rfl))
    fun y ⟨⟨y4, ym⟩, ky⟩ => ?_
  have k0 : Keep [.t0, .t1, .t2, .t3, .t4] s y := ((kt.trans kx).trans ky).mono (by decide)
  refine ⟨h.of_keep (k0.mono (by decide)), ym.trans (xm.trans mt), ?_, ?_, ?_, ?_, y4, k0⟩
  · rw [ky.gpr (by decide), kx.gpr (by decide)]; exact p0
  · rw [ky.gpr (by decide), kx.gpr (by decide)]; exact p1
  · rw [ky.gpr (by decide), kx.gpr (by decide)]; exact p2
  · rw [ky.gpr (by decide)]; exact x3

/-- `[o] = c₁ [a] + c₂ [b]` (`lin`), the coefficients `u`, `v` the window's
words at `c₁`, `c₂`. -/
theorem lin_ok {s : State} {B : Addr} {Z w N n : Nat} (h : Ctx s B Z w N n) {c1 c2 o a b : Nat}
    {u v : Int} (ho : o < N) (ha : a < N) (hb : b < N) (hN : N ≤ 256) (hoa : o ≠ a) (hob : o ≠ b)
    (hc1 : c1 + 8 ≤ 48) (hc1' : c1 % 8 = 0) (hc2 : c2 + 8 ≤ 48) (hc2' : c2 % 8 = 0)
    (hu : s.mem.readW (off B (arr w aW + c1)) 64 = BitVec.ofInt 64 u)
    (hv : s.mem.readW (off B (arr w aW + c2)) 64 = BitVec.ofInt 64 v)
    (huv : u.natAbs + v.natAbs ≤ 2 ^ 30) :
    WP isa (lin c1 c2 o a b) s fun t => Ctx t B Z w N n ∧ Keys.Frame B w [o] [] s.mem t.mem ∧
      sv t.mem B (arr w o) (n + 1) = u * sv s.mem B (arr w a) n + v * sv s.mem B (arr w b) n ∧
      Keep kRegs s t := by
  have fo := h.ws.arr_fit ho
  have fa := h.ws.arr_fit ha
  have fb := h.ws.arr_fit hb
  have hS : S w = 8 * (w + 2) := rfl
  have := h.nw
  have := h.npos
  have := h.ws.wle
  have hnw := h.ws.nowrap
  have := arr_al4 w o
  have := arr_al4 w a
  have := arr_al4 w b
  rw [lin]; simp only [seqs]; rw [WP.seq_iff]
  -- The pointers, the coefficients, the count and no carry.
  have hb1 : WP isa (.block (ptr .t0 o ++ ptr .t1 a ++ ptr .t2 b ++ ldW .a5 c1 ++ ldW .a7 c2 ++ cntN ++
      ([.li .t4 0] : List Instr))) s fun t => Ctx t B Z w N n ∧ t.mem = s.mem ∧
      t.gpr .t0 = off B (arr w o) ∧ t.gpr .t1 = off B (arr w a) ∧ t.gpr .t2 = off B (arr w b) ∧
      t.gpr .t3 = BitVec.ofNat 64 n ∧ t.gpr .t4 = BitVec.ofInt 64 0 ∧ t.gpr .a5 = BitVec.ofInt 64 u ∧
      t.gpr .a7 = BitVec.ofInt 64 v ∧ Keep kRegs s t := by
    rw [show ptr .t0 o ++ ptr .t1 a ++ ptr .t2 b ++ ldW .a5 c1 ++ ldW .a7 c2 ++ cntN ++
      ([.li .t4 0] : List Instr) = VG.Impl.Rsa.RISCV64.Keys.ptrs o a b ++
        (ldW .a5 c1 ++ (ldW .a7 c2 ++ (cntN ++ ([.li .t4 0] : List Instr)))) by
          simp only [VG.Impl.Rsa.RISCV64.Keys.ptrs, List.append_assoc]]
    refine ptrs_ok h.ws (by omega) (by omega) (by omega) fun t p0 p1 p2 kt mt => ?_
    have ht := h.of_keep (kt.mono (by decide))
    refine ldW_ok ht (by decide) (by decide) hc1 hc1' ?_
    refine ldW_ok (ht.of_keep ((Keep.write _ .a5 _).mono (rs' := kRegs) (by decide))) (by decide) (by decide)
      hc2 hc2' ?_
    rw [WP.block_append_iff]
    refine WP.mono (cntN_ok (ht.of_keep (((Keep.write _ .a5 _).trans (Keep.write _ .a7 _)).mono
      (rs' := kRegs) (by decide)))) fun x ⟨⟨x3, xm⟩, kx⟩ => ?_
    refine WP.mono (WP.keep [.t4] (Q := fun y => y.gpr .t4 = BitVec.ofInt 64 0 ∧ y.mem = x.mem)
      (by brun [fin64_exec_li_zero]; try rfl) (by rfl) (by rfl)) fun y ⟨⟨y4, ym⟩, ky⟩ => ?_
    have k0 : Keep kRegs s y :=
      ((((kt.trans (Keep.write _ _ _)).trans (Keep.write _ _ _)).trans kx).trans ky).mono (by decide)
    refine ⟨h.of_keep k0, ym.trans (xm.trans mt), ?_, ?_, ?_, ?_, y4, ?_, ?_, k0⟩
    · rw [ky.gpr (by decide), kx.gpr (by decide)]; simp only [gpr_write, reduceCtorEq, ↓reduceIte]; exact p0
    · rw [ky.gpr (by decide), kx.gpr (by decide)]; simp only [gpr_write, reduceCtorEq, ↓reduceIte]; exact p1
    · rw [ky.gpr (by decide), kx.gpr (by decide)]; simp only [gpr_write, reduceCtorEq, ↓reduceIte]; exact p2
    · rw [ky.gpr (by decide)]; exact x3
    · rw [ky.gpr (by decide), kx.gpr (by decide)]; simp only [gpr_write, reduceCtorEq, ↓reduceIte, mt]; exact hu
    · rw [ky.gpr (by decide), kx.gpr (by decide)]; simp only [gpr_write, ↓reduceIte, mem_write, mt]; exact hv
  refine WP.mono hb1 fun t1 ⟨h1, m1, p0, p1, p2, p3, p4, p5, p7, k1⟩ => ?_
  rw [WP.seq_iff]
  refine WP.mono (linLoop_ok h1.ws.scr p0 p1 p2 p3 p4 p5 p7 huv (by decide) (by decide) h.npos (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (ahead_k hoa (by omega)) (ahead_k hob (by omega)))
    fun t2 ⟨⟨c', hc1', hc2', q4, qeq⟩, q0, q1, q2, out2, k2⟩ => ?_
  have h2 := h1.of_keep (k2.mono (by decide))
  refine WP.mono (linTop_ok h2.ws.scr q0 q1 q2 q4 ((k2.gpr (by decide)).trans p5)
    ((k2.gpr (by decide)).trans p7) huv hc1' hc2' (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega)) fun t3 ⟨⟨⟨q, hq1, hq2, qe, qt⟩, out3⟩, k3⟩ => ?_
  have k : Keep kRegs s t3 := Keep.trans' (Keep.trans' k1 (k2.mono (by decide))) (k3.mono (by decide))
  rw [m1] at qeq out2
  refine ⟨h.of_keep k, ?_, ?_, k⟩
  · exact (Keys.Frame.of_arr (d := 0) (by simpa only [Nat.add_zero] using out2) (by omega) (by simp)).trans
      (Keys.Frame.of_arr (d := 4 * n) out3 (by omega) (by simp))
  · have da := (arr_disj (w := w) hoa)
    have db := (arr_disj (w := w) hob)
    have xa : t2.mem.readW (off B (arr w a + 4 * n)) 32 = s.mem.readW (off B (arr w a + 4 * n)) 32 :=
      Outside.readW32 out2 (by omega) (by omega)
    have xb : t2.mem.readW (off B (arr w b + 4 * n)) 32 = s.mem.readW (off B (arr w b + 4 * n)) 32 :=
      Outside.readW32 out2 (by omega) (by omega)
    have vo : val32 t3.mem B (arr w o) n = val32 t2.mem B (arr w o) n := out3.val32 (by omega) (by omega)
    rw [xa, xb] at qe
    unfold sv
    rw [show arr w o + 4 * (n + 1) = arr w o + 4 * n + 4 by omega, qt, val32_succ, vo]
    have eP : (2 : Int) ^ (32 * (n + 1)) = 2 ^ 32 * 2 ^ (32 * n) := by
      rw [show 32 * (n + 1) = 32 * n + 32 by omega, Int.pow_add, Int.mul_comm]
    rw [eP]
    push_cast
    generalize (2 : Int) ^ (32 * n) = P at qeq ⊢
    grind

/-! ## `shr` -/

/-- `[o] = [a] / 2^30` (`shr`), `n + 1` digits, for `[a]` (`n + 2` digits) a
multiple of `2^30`. -/
theorem shr_ok {s : State} {B : Addr} {Z w N n : Nat} (h : Ctx s B Z w N n) {o a : Nat}
    (ho : o < N) (ha : a < N) (hN : N ≤ 256) (hoa : o ≠ a) {z : Int}
    (hy : sv s.mem B (arr w a) (n + 1) = 2 ^ 30 * z) (hz1 : -2 ^ (32 * n + 31) ≤ z)
    (hz2 : z < 2 ^ (32 * n + 31)) :
    WP isa (shr o a) s fun t => Ctx t B Z w N n ∧ Keys.Frame B w [o] [] s.mem t.mem ∧
      sv t.mem B (arr w o) n = z ∧ Keep kRegs s t := by
  have fo := h.ws.arr_fit ho
  have fa := h.ws.arr_fit ha
  have hS : S w = 8 * (w + 2) := rfl
  have := h.nw
  have := h.npos
  have := h.ws.wle
  have hnw := h.ws.nowrap
  have da := arr_disj (w := w) hoa
  have := arr_al4 w o
  have := arr_al4 w a
  rw [shr, WP.seq_iff]
  have hb1 : WP isa (.block (ptr .t0 o ++ ptr .t1 a ++ cntN1)) s fun t => Ctx t B Z w N n ∧
      t.mem = s.mem ∧ t.gpr .t0 = off B (arr w o) ∧ t.gpr .t1 = off B (arr w a) ∧
      t.gpr .t3 = BitVec.ofNat 64 (n + 1) ∧ Keep kRegs s t := by
    refine ptr2_ok h.ws (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by omega) (by omega) fun t p0 p1 kt mt => ?_
    have ht := h.of_keep (kt.mono (by decide))
    refine WP.mono (cntN1_ok ht) fun x ⟨⟨x3, xm⟩, kx⟩ => ?_
    have k0 : Keep kRegs s x := (kt.trans kx).mono (by decide)
    refine ⟨h.of_keep k0, xm.trans mt, ?_, ?_, x3, k0⟩
    · rw [kx.gpr (by decide)]; exact p0
    · rw [kx.gpr (by decide)]; exact p1
  refine WP.mono hb1 fun t1 ⟨h1, m1, p0, p1, p3, k1⟩ => ?_
  refine WP.mono (shrLoop_ok h1.ws.scr p0 p1 p3 (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega)) fun t2 ⟨veq, out2, k2⟩ => ?_
  have k : Keep kRegs s t2 := Keep.trans' k1 (k2.mono (by decide))
  rw [m1] at veq out2
  refine ⟨h.of_keep k, Keys.Frame.of_arr (d := 0) (by simpa only [Nat.add_zero] using out2)
    (by omega) (by simp), ?_, k⟩
  have e := val_sv s.mem B (arr w a) (n + 1)
  rw [hy] at e
  have hd := congrArg (fun x : Nat => (x : Int)) veq
  push_cast at hd
  rw [e] at hd
  refine sv_of_eq (q := 4 * (if 2 ^ 31 ≤ w32 s.mem B (arr w a + 4 * (n + 1)) then 1 else 0) -
    ((w32 s.mem B (arr w a + 4 * (n + 1)) / 2 ^ 30 : Nat) : Int)) ?_ hz1 hz2
  have e1 : (2 : Int) ^ (32 * (n + 1 + 1)) = 2 ^ 30 * (4 * 2 ^ (32 * (n + 1))) := by
    rw [show 32 * (n + 1 + 1) = 30 + (2 + 32 * (n + 1)) by omega, Int.pow_add, Int.pow_add]; rfl
  rw [e1, Int.mul_assoc, ← Int.mul_add, show (1073741824 : Int) = 2 ^ 30 from rfl,
    Int.mul_ediv_cancel_left _ (by decide)] at hd
  generalize (2 : Int) ^ (32 * (n + 1)) = P at hd ⊢
  push_cast at hd
  grind

/-! ## `mac` -/

/-- `[o] = [a] + k [b]` (`mac`), `K` digits, `k < 2^32` in `a5`; `o` equal to
`a` and to `b`, or apart from them. -/
theorem mac_ok {s : State} {B : Addr} {Z w N n : Nat} (h : Ctx s B Z w N n) {o a b K : Nat}
    {cnt : List Instr} (hcnt : ∀ t, Ctx t B Z w N n → WP isa (.block cnt) t fun x =>
      (x.gpr .t3 = BitVec.ofNat 64 K ∧ x.mem = t.mem) ∧ Keep [.t3] t x)
    (hK1 : 1 ≤ K) (hK : K ≤ n + 1) (ho : o < N) (ha : a < N) (hb : b < N) (hN : N ≤ 256)
    (hk : (s.gpr .a5).toNat < 2 ^ 32) :
    WP isa (mac o a b cnt) s fun t => Ctx t B Z w N n ∧ Keys.Frame B w [o] [] s.mem t.mem ∧
      val32 t.mem B (arr w o) K + 2 ^ (32 * K) * (t.gpr .t4).toNat =
        val32 s.mem B (arr w a) K + (s.gpr .a5).toNat * val32 s.mem B (arr w b) K ∧
      (t.gpr .t4).toNat < 2 ^ 32 ∧ t.gpr .t0 = off B (arr w o + 4 * K) ∧ t.gpr .a5 = s.gpr .a5 ∧
      Outside B (arr w o) (4 * K) s.mem t.mem ∧ Keep kRegs s t := by
  have fo := h.ws.arr_fit ho
  have fa := h.ws.arr_fit ha
  have fb := h.ws.arr_fit hb
  have hS : S w = 8 * (w + 2) := rfl
  have := h.nw
  have := h.ws.wle
  have := arr_al4 w o
  have := arr_al4 w a
  have := arr_al4 w b
  rw [mac, macSetup, WP.seq_iff]
  refine WP.mono (setup_ok h hcnt (by omega) (by omega) (by omega)) fun t1 ⟨h1, m1, p0, p1, p2, p3, p4, k1⟩ => ?_
  have k5 : t1.gpr .a5 = s.gpr .a5 := k1.gpr (by decide)
  refine WP.mono (macLoop_ok h1.ws.scr p0 p1 p2 p3 (by rw [p4]; decide) (by rw [k5]; exact hk) hK1 (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (ahead_any w o a K (by omega)) (ahead_any w o b K (by omega)))
    fun t2 ⟨q4, qeq, q0, out2, k2⟩ => ?_
  have k : Keep kRegs s t2 := Keep.trans' (k1.mono (by decide)) (k2.mono (by decide))
  rw [m1, k5, p4] at qeq
  rw [m1] at out2
  refine ⟨h.of_keep k, Keys.Frame.of_arr (d := 0) (by simpa only [Nat.add_zero] using out2)
    (by omega) (by simp), by simpa using qeq, q4, q0, (k2.gpr (by decide)).trans k5, out2, k⟩

/-! ## `csub` -/

/-- The mask `0 - y` of a borrow `y`. -/
theorem mask_of_borrow (y : BitVec 64) (hy : y.toNat ≤ 1) :
    BitVec.ofNat 64 0 - y = if decide (y.toNat = 1) then BitVec.allOnes 64 else 0 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hy with e | e
  · have : y = 0#64 := BitVec.eq_of_toNat_eq e
    subst this; rfl
  · have : y = 1#64 := BitVec.eq_of_toNat_eq e
    subst this; rfl

/-- `[o] = [x] - m` where it does not borrow, else `[x]` (`csub`), `n + 1`
digits, through `[sc]`. -/
theorem csub_ok {s : State} {B : Addr} {Z w N n : Nat} (h : Ctx s B Z w N n) {o x sc : Nat}
    (ho : o < N) (hx : x < N) (hsc : sc < N) (hm : aMz < N) (hN : N ≤ 256) (hsx : sc ≠ x)
    (hsm : sc ≠ aMz) (hos : o ≠ sc) {p X : Nat} (hp : val32 s.mem B (arr w aMz) (n + 1) = p)
    (hX : val32 s.mem B (arr w x) (n + 1) = X) :
    WP isa (csub o x sc) s fun t => Ctx t B Z w N n ∧ Keys.Frame B w [o, sc] [] s.mem t.mem ∧
      val32 t.mem B (arr w o) (n + 1) = (if p ≤ X then X - p else X) ∧ Keep kRegs s t := by
  have fo := h.ws.arr_fit ho
  have fx := h.ws.arr_fit hx
  have fs := h.ws.arr_fit hsc
  have fm := h.ws.arr_fit hm
  have hS : S w = 8 * (w + 2) := rfl
  have := h.nw
  have := h.npos
  have := h.ws.wle
  have hnw := h.ws.nowrap
  have := arr_al4 w o
  have := arr_al4 w x
  have := arr_al4 w sc
  have := arr_al4 w aMz
  rw [csub]; simp only [seqs]; rw [WP.seq_iff]
  refine WP.mono (setup_ok h (fun t ht => cntN1_ok ht) (by omega) (by omega) (by omega))
    fun t1 ⟨h1, m1, p0, p1, p2, p3, p4, k1⟩ => ?_
  rw [WP.seq_iff]
  refine WP.mono (subLoop_ok h1.ws.scr p0 p1 p2 p3 (by rw [p4]; decide)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (ahead_k hsx (by omega)) (ahead_k hsm (by omega)))
    fun t2 ⟨b4, veq, out2, k2⟩ => ?_
  have h2 := h1.of_keep (k2.mono (by decide))
  rw [m1, p4, show (0 : BitVec 64).toNat = 0 from rfl, Nat.add_zero] at veq
  rw [m1] at out2
  rw [WP.seq_iff]
  -- The mask of the borrow.
  have hb2 : WP isa (.block (ptr .t0 o ++ ptr .t1 sc ++ ptr .t2 x ++ cntN1 ++
      ([.li .t5 0, .sub .t4 .t5 .t4] : List Instr))) t2 fun t => Ctx t B Z w N n ∧ t.mem = t2.mem ∧
      t.gpr .t0 = off B (arr w o) ∧ t.gpr .t1 = off B (arr w sc) ∧ t.gpr .t2 = off B (arr w x) ∧
      t.gpr .t3 = BitVec.ofNat 64 (n + 1) ∧ t.gpr .t4 = BitVec.ofNat 64 0 - t2.gpr .t4 ∧ Keep kRegs t2 t := by
    rw [show ptr .t0 o ++ ptr .t1 sc ++ ptr .t2 x ++ cntN1 ++ ([.li .t5 0, .sub .t4 .t5 .t4] : List Instr) =
      VG.Impl.Rsa.RISCV64.Keys.ptrs o sc x ++ (cntN1 ++ ([.li .t5 0, .sub .t4 .t5 .t4] : List Instr)) by
        simp only [VG.Impl.Rsa.RISCV64.Keys.ptrs, List.append_assoc]]
    refine ptrs_ok h2.ws (by omega) (by omega) (by omega) fun t q0 q1 q2 kt mt => ?_
    have ht := h2.of_keep (kt.mono (by decide))
    rw [WP.block_append_iff]
    refine WP.mono (cntN1_ok ht) fun y ⟨⟨y3, ym⟩, ky⟩ => ?_
    have y4 : y.gpr .t4 = t2.gpr .t4 := (ky.gpr (by decide)).trans (kt.gpr (by decide))
    refine WP.mono (WP.keep [.t5, .t4] (Q := fun z => z.gpr .t4 = BitVec.ofNat 64 0 - t2.gpr .t4 ∧ z.mem = y.mem)
      (by brun [y4, fin64_exec_li_zero]; try rfl) (by rfl) (by rfl)) fun z ⟨⟨z4, zm⟩, kz⟩ => ?_
    have k0 : Keep kRegs t2 z := ((kt.trans ky).trans kz).mono (by decide)
    refine ⟨h2.of_keep k0, zm.trans (ym.trans mt), ?_, ?_, ?_, ?_, z4, k0⟩
    · rw [kz.gpr (by decide), ky.gpr (by decide)]; exact q0
    · rw [kz.gpr (by decide), ky.gpr (by decide)]; exact q1
    · rw [kz.gpr (by decide), ky.gpr (by decide)]; exact q2
    · rw [kz.gpr (by decide)]; exact y3
  refine WP.mono hb2 fun t3 ⟨h3, m3, r0, r1, r2, r3, r4, k3⟩ => ?_
  refine WP.mono (selLoop_ok (b := decide ((t2.gpr .t4).toNat = 1)) h3.ws.scr
    r0 r1 r2 r3 (by rw [r4]; exact mask_of_borrow _ b4) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega)
    (ahead_k hos (by omega)) (ahead_any w o x (n + 1) (by omega))) fun t4 ⟨seq, out4, k4, _⟩ => ?_
  have k : Keep kRegs s t4 :=
    Keep.trans' (Keep.trans' (Keep.trans' (k1.mono (by decide)) (k2.mono (by decide))) k3) (k4.mono (by decide))
  refine ⟨h.of_keep k, ?_, ?_, k⟩
  · rw [m3] at out4
    exact (Keys.Frame.of_arr (o := sc) (d := 0) (by simpa only [Nat.add_zero] using out2) (by omega)
      (by simp)).trans (Keys.Frame.of_arr (o := o) (d := 0) (by simpa only [Nat.add_zero] using out4)
        (by omega) (by simp))
  · have vx : val32 t2.mem B (arr w x) (n + 1) = X := by
      rw [out2.val32 (by have := arr_disj (w := w) hsx; omega) (by omega)]; exact hX
    rw [seq, m3, vx]
    have hpR := val32_lt s.mem B (arr w aMz) (n + 1)
    have hXR := val32_lt s.mem B (arr w x) (n + 1)
    have hSR := val32_lt t2.mem B (arr w sc) (n + 1)
    rw [hp] at hpR veq
    rw [hX] at hXR veq
    generalize 2 ^ (32 * (n + 1)) = R at hpR hXR hSR veq
    by_cases e : (t2.gpr .t4).toNat = 1
    · rw [e] at veq; simp only [e, decide_true, ↓reduceIte]
      have : ¬ p ≤ X := by omega
      simp only [this, ↓reduceIte]
    · have e0 : (t2.gpr .t4).toNat = 0 := by omega
      rw [e0] at veq; simp only [e, decide_false, Bool.false_eq_true, ↓reduceIte]
      have : p ≤ X := by omega
      simp only [this, ↓reduceIte]; omega

theorem val32_zero {m : Mem} {B : Addr} {d : Nat} :
    ∀ {k : Nat}, (∀ i < k, w32 m B (d + 4 * i) = 0) → val32 m B d k = 0
  | 0, _ => rfl
  | k + 1, h => by
    rw [val32_succ, val32_zero (fun i hi => h i (by omega)), h k (by omega), Nat.mul_zero]

/-- An array's `w` words, as digits. -/
theorem num_eq (m : Mem) (B : Addr) (w j : Nat) : num m B w j = val32 m B (arr w j) (2 * w) :=
  wordsVal_eq_val32 _ _ _ _

/-- `zeroW j`: `[j]`'s `2 w + 2` digits zeroed. -/
theorem zeroW_ok {s : State} {B : Addr} {Z w N n j : Nat} (h : Ctx s B Z w N n) (hj : j < N) (hN : N ≤ 256) :
    WP isa (zeroW j) s fun t => Ctx t B Z w N n ∧ Keys.Frame B w [j] [] s.mem t.mem ∧
      Outside B (arr w j) (4 * (2 * w + 2)) s.mem t.mem ∧
      (∀ i < 2 * w + 2, w32 t.mem B (arr w j + 4 * i) = 0) ∧ Keep kRegs s t := by
  have fj := h.ws.arr_fit hj
  have hS : S w = 8 * (w + 2) := rfl
  have := h.ws.wle
  have := arr_al4 w j
  rw [zeroW, WP.seq_iff]
  refine ptr_ok h.ws (by decide) (by decide) (by omega) ?_
  refine WP.mono (WP.keep [.t3] (Q := fun u => u.gpr .t3 = BitVec.ofNat 64 (2 * w + 2) ∧
    u.gpr .t0 = off B (arr w j) ∧ u.mem = s.mem) ?_ (by rfl) (by rfl)) fun u ⟨⟨u3, u0, um⟩, ku⟩ => ?_
  · brun [h.ws.s9]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have k1 : Keep kRegs s u := ((Keep.write _ .t0 _).trans ku).mono (by decide)
  rw [zeros, WP.seq_iff]
  refine WP.mono (WP.keep [.t5] (Q := fun y => y.gpr .t5 = 0 ∧ y.mem = u.mem) (by brun [fin64_exec_li_zero])
    (by rfl) (by rfl)) fun y ⟨⟨y5, ym⟩, ky⟩ => ?_
  have k2 : Keep kRegs s y := Keep.trans' k1 (ky.mono (by decide))
  refine WP.mono (zeroLoop_ok (dO := arr w j) (n := 2 * w + 2) (h.of_keep k2).ws.scr (by rw [ky.gpr (by decide)]; exact u0)
    (by rw [ky.gpr (by decide)]; exact u3) y5 (by omega) (by omega) (by omega) (by omega)) fun t ⟨z, out, kt⟩ => ?_
  rw [ym, um] at out
  exact ⟨h.of_keep (Keep.trans' k2 (kt.mono (by decide))), Keys.Frame.of_arr (d := 0)
    (by simpa only [Nat.add_zero] using out) (by omega) (by simp), out, z, Keep.trans' k2 (kt.mono (by decide))⟩

end VG.Proof.Rsa.RISCV64.InvBatch
