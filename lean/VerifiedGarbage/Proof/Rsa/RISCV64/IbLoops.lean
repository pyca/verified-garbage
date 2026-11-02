module

public import VerifiedGarbage.Impl.Rsa.RISCV64.InvBatch
public import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Rsa.RISCV64.KeyLoops
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The digit loops of the batched inverse on RISC-V

As PPC64LE's (`Proof/Rsa/PPC64LE/Loops.lean`): each loop runs over `n`
digits of 32 bits at byte offsets of the working space (`Scr s B Z`),
multiples of 4, its pointers in `t0`–`t2` and its count in `t3`
(`countLoop .t3 body`), and changes only `Loops.loopRegs`:

* `subLoop_ok`: `[o] := [a] - [b]`, the borrow in and out in `t4`;
* `selLoop_ok`: `[o] := mask ? [b] : [a]`, the mask in `t4`;
* `copyLoop_ok`: `[o] := [a]`;
* `eqLoop_ok`: `t4 = 0` exactly when `[a] = [b]`;
* `zeroLoop_ok`: `n` digits from `t0` := 0.

The output may be an input, or come before it, or be apart from it
(`Ahead`): a digit is read before any digit at or after it is written.
-/

@[expose] public section

namespace VG.Proof.Rsa.RISCV64.InvBatch

open VG VG.RISCV64 VG.Proof.Mont VG.Proof.Bignum.RISCV64 VG.Impl.Bignum.RISCV64
open VG.Impl.Rsa.RISCV64.InvBatch (subBody selBody copyBody eqBody)
open VG.Proof.Rsa.RISCV64.Loops (loopRegs split_eq_iff)

/-- A digit of the working space at an offset that is a multiple of 4 is
aligned. -/
theorem Scr.al4 {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {d : Nat}
    (hd : d + 4 ≤ size) (h4 : d % 4 = 0) : (off base d).toNat % 4 = 0 := by
  have hn := hs.nowrap
  have ha := hs.al
  have e : (off base d).toNat = base.toNat + d := by
    simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (a := d) (by omega), Nat.mod_eq_of_lt (by omega)]
  rw [e]
  omega

theorem toNat_ext32 (v : BitVec 32) : (v.setWidth 64).toNat = v.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans v.isLt (by decide))]

/-- A store of digit `j` of a number of `j + 1` digits. -/
theorem val32_write_top (m : Mem) (B : Addr) (d j : Nat) (v : BitVec 32) (h : d + 4 * j + 4 ≤ 2 ^ 64) :
    val32 (m.writeW (off B (d + 4 * j)) v) B d (j + 1) = val32 m B d j + 2 ^ (32 * j) * v.toNat := by
  rw [val32_succ, (writeW32_outside m B v (by omega_arith)).val32 (by omega_arith) (by omega_arith), w32_write_self]

theorem pow32_mul (j : Nat) : 2 ^ 32 * 2 ^ (32 * j) = 2 ^ (32 * (j + 1)) := by
  rw [← Nat.pow_add]; congr 1; omega_arith

/-- A digit of a subtraction, on bit vectors: `d = t - m - c` in 64 bits,
whose sign bit is the borrow and whose low 32 bits are the digit. -/
theorem sub_arith (t m : BitVec 32) (c : BitVec 64) (hc : c.toNat ≤ 1) :
    let D := t.setWidth 64 - m.setWidth 64 - c
    (D >>> 63).toNat ≤ 1 ∧
      c.toNat + (D.setWidth 32).toNat + m.toNat = t.toNat + 2 ^ 32 * (D >>> 63).toNat := by
  intro D
  have ht := t.isLt
  have hm := m.isLt
  have vD : D.toNat = (2 ^ 64 - c.toNat + ((2 ^ 64 - m.toNat) + t.toNat) % 2 ^ 64) % 2 ^ 64 := by
    simp only [D, BitVec.toNat_sub, toNat_ext32]
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_setWidth, vD]
  omega_arith

/-- A digit of the selection, on bit vectors. -/
theorem select_arith (x y : BitVec 32) (b : Bool) :
    (((y.setWidth 64 ^^^ x.setWidth 64) &&& (if b then BitVec.allOnes 64 else 0)) ^^^ x.setWidth 64).setWidth 32 =
      if b then y else x := by
  cases b
  · rw [ite_eq_right Bool.false_ne_true, ite_eq_right Bool.false_ne_true, show (0 : BitVec 64) = 0#64 from rfl,
      BitVec.and_zero, BitVec.zero_xor]
    exact lo32_ext x
  · simp only [ite_true, BitVec.and_allOnes, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
    exact lo32_ext y

/-- Array `a` (at `dA`) is read after `o` (at `dO`) is written up to the
same digit: it is `o` or after it, or apart from it. -/
def Ahead (dO dA n : Nat) : Prop := dO ≤ dA ∨ dA + 4 * n ≤ dO

/-- A digit at `dA + 4 i` is outside the digits written before it. -/
theorem Ahead.outside {dO dA n i : Nat} (h : Ahead dO dA n) (hi : i < n) :
    dA + 4 * i + 4 ≤ dO ∨ dO + 4 * i ≤ dA + 4 * i := by
  unfold Ahead at h; omega

/-- A digit of `[o]` written, as the top digit of a number of `i + 1` digits. -/
theorem out_step32 {s t : State} {B : Addr} {dO i : Nat} (v : BitVec 32)
    (h : Outside B dO (4 * i) s.mem t.mem) (hnw : dO + 4 * i + 4 ≤ 2 ^ 64) :
    Outside B dO (4 * (i + 1)) s.mem (t.mem.writeW (off B (dO + 4 * i)) v) :=
  (h.mono (Nat.le_refl _) (by omega_arith)).trans
    ((writeW32_outside _ B (d := dO + 4 * i) _ hnw).mono (by omega_arith) (by omega_arith))

/-- `[o] := [a] - [b]` over `n` digits (`countLoop .t3 subBody`), from the
borrow `c` in `t4`: the difference and the borrow out. -/
theorem subLoop_ok {s : State} {B : Addr} {Z dO dA dB n : Nat} (hs : Scr s B Z)
    (h0 : s.gpr .t0 = off B dO) (h1 : s.gpr .t1 = off B dA) (h2 : s.gpr .t2 = off B dB)
    (h3 : s.gpr .t3 = BitVec.ofNat 64 n) (h4 : (s.gpr .t4).toNat ≤ 1) (hn : 1 ≤ n) (hn' : n < 2 ^ 32)
    (hO4 : dO % 4 = 0) (hA4 : dA % 4 = 0) (hB4 : dB % 4 = 0)
    (hO : dO + 4 * n ≤ Z) (hA : dA + 4 * n ≤ Z) (hB : dB + 4 * n ≤ Z)
    (aA : Ahead dO dA n) (aB : Ahead dO dB n) :
    WP isa (countLoop .t3 subBody) s fun t =>
      (t.gpr .t4).toNat ≤ 1 ∧
      val32 t.mem B dO n + val32 s.mem B dB n + (s.gpr .t4).toNat =
        val32 s.mem B dA n + 2 ^ (32 * n) * (t.gpr .t4).toNat ∧
      Outside B dO (4 * n) s.mem t.mem ∧ Keep loopRegs s t := by
  have hnw := hs.nowrap
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .t0 = off B (dO + 4 * i) ∧ t.gpr .t1 = off B (dA + 4 * i) ∧ t.gpr .t2 = off B (dB + 4 * i) ∧
      (t.gpr .t4).toNat ≤ 1 ∧ Outside B dO (4 * i) s.mem t.mem ∧
      val32 t.mem B dO i + val32 s.mem B dB i + (s.gpr .t4).toNat =
        val32 s.mem B dA i + 2 ^ (32 * i) * (t.gpr .t4).toNat ∧
      Keep loopRegs s t
  refine WP.mono (wp_countdown (body := .block (subBody ++ ([.addi .t3 .t3 (-1)] : List Instr)))
    (cnt := .t3) (N := n) (by omega_arith) (by omega_arith) Inv
    (fun i hi t ⟨j0, j1, j2, j4, jout, jeq, jk⟩ hc => ?_)
    ⟨by rw [h0]; rfl, by rw [h1]; rfl, by rw [h2]; rfl, h4, Outside.refl _ _ _ _,
      by simp [val32], Keep.refl _ _⟩ h3)
    fun t ⟨_, _, _, j4, jout, jeq, jk⟩ => ⟨j4, jeq, jout, jk⟩
  have hs' := hs.congr jk.2.2
  have hst := (show WP isa (.block (subBody ++ ([.addi .t3 .t3 (-1)] : List Instr))) t fun t' =>
      let D := (t.mem.readW (off B (dA + 4 * i)) 32).setWidth 64 -
        (t.mem.readW (off B (dB + 4 * i)) 32).setWidth 64 - t.gpr .t4
      (t'.gpr .t0 = off B (dO + 4 * i + 4) ∧ t'.gpr .t1 = off B (dA + 4 * i + 4) ∧
        t'.gpr .t2 = off B (dB + 4 * i + 4) ∧ t'.gpr .t4 = D >>> 63 ∧
        t'.gpr .t3 = t.gpr .t3 - BitVec.ofNat 64 1 ∧
        t'.mem = t.mem.writeW (off B (dO + 4 * i)) (D.setWidth 32)) ∧ Keep loopRegs t t' from by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [subBody, j0, j1, j2, exec_load_w, exec_store_w,
      hs'.ld (show dA + 4 * i + 4 ≤ Z by omega_arith), hs'.ld (show dB + 4 * i + 4 ≤ Z by omega_arith),
      hs'.st (show dO + 4 * i + 4 ≤ Z by omega_arith),
      Scr.al4 hs' (show dA + 4 * i + 4 ≤ Z by omega_arith) (by omega_arith),
      Scr.al4 hs' (show dB + 4 * i + 4 ≤ Z by omega_arith) (by omega_arith),
      Scr.al4 hs' (show dO + 4 * i + 4 ≤ Z by omega_arith) (by omega_arith)])
  refine WP.mono hst fun t' ⟨⟨l0, l1, l2, l4, l3, lm⟩, lk⟩ => ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, Keep.trans' jk lk⟩, l3⟩
  · rw [l0, show dO + 4 * i + 4 = dO + 4 * (i + 1) by omega_arith]
  · rw [l1, show dA + 4 * i + 4 = dA + 4 * (i + 1) by omega_arith]
  · rw [l2, show dB + 4 * i + 4 = dB + 4 * (i + 1) by omega_arith]
  · rw [l4]; exact (sub_arith _ _ _ j4).1
  · rw [lm]; exact out_step32 _ jout (by omega_arith)
  · have wa : w32 t.mem B (dA + 4 * i) = w32 s.mem B (dA + 4 * i) :=
      jout.w32 (by have := aA.outside hi; omega_arith) (by omega_arith)
    have wb : w32 t.mem B (dB + 4 * i) = w32 s.mem B (dB + 4 * i) :=
      jout.w32 (by have := aB.outside hi; omega_arith) (by omega_arith)
    have k := (sub_arith (t.mem.readW (off B (dA + 4 * i)) 32) (t.mem.readW (off B (dB + 4 * i)) 32) _ j4).2
    rw [lm, l4, val32_write_top _ _ _ _ _ (by omega_arith), val32_succ s.mem B dB i, val32_succ s.mem B dA i,
      ← pow32_mul i]
    change _ + _ + (_ + _ * w32 s.mem B (dB + 4 * i)) + _ = _ + _ * w32 s.mem B (dA + 4 * i) + _
    rw [← wa, ← wb]
    change (t.gpr .t4).toNat + _ + w32 t.mem B (dB + 4 * i) = w32 t.mem B (dA + 4 * i) + _ at k
    grind

/-- `[o] := b ? [b] : [a]` over `n` digits (`countLoop .t3 selBody`), the
mask of `b` in `t4`. -/
theorem selLoop_ok {s : State} {B : Addr} {Z dO dA dB n : Nat} (hs : Scr s B Z) {b : Bool}
    (h0 : s.gpr .t0 = off B dO) (h1 : s.gpr .t1 = off B dA) (h2 : s.gpr .t2 = off B dB)
    (h3 : s.gpr .t3 = BitVec.ofNat 64 n)
    (h4 : s.gpr .t4 = if b then BitVec.allOnes 64 else 0) (hn : 1 ≤ n) (hn' : n < 2 ^ 32)
    (hO4 : dO % 4 = 0) (hA4 : dA % 4 = 0) (hB4 : dB % 4 = 0)
    (hO : dO + 4 * n ≤ Z) (hA : dA + 4 * n ≤ Z) (hB : dB + 4 * n ≤ Z)
    (aA : Ahead dO dA n) (aB : Ahead dO dB n) :
    WP isa (countLoop .t3 selBody) s fun t =>
      val32 t.mem B dO n = (if b then val32 s.mem B dB n else val32 s.mem B dA n) ∧
      Outside B dO (4 * n) s.mem t.mem ∧ Keep loopRegs s t ∧ t.gpr .t4 = s.gpr .t4 := by
  have hnw := hs.nowrap
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .t0 = off B (dO + 4 * i) ∧ t.gpr .t1 = off B (dA + 4 * i) ∧ t.gpr .t2 = off B (dB + 4 * i) ∧
      Outside B dO (4 * i) s.mem t.mem ∧
      val32 t.mem B dO i = (if b then val32 s.mem B dB i else val32 s.mem B dA i) ∧
      Keep loopRegs s t ∧ t.gpr .t4 = s.gpr .t4
  refine WP.mono (wp_countdown (body := .block (selBody ++ ([.addi .t3 .t3 (-1)] : List Instr)))
    (cnt := .t3) (N := n) (by omega_arith) (by omega_arith) Inv
    (fun i hi t ⟨j0, j1, j2, jout, jeq, jk, j4⟩ hc => ?_)
    ⟨by rw [h0]; rfl, by rw [h1]; rfl, by rw [h2]; rfl, Outside.refl _ _ _ _,
      by simp only [val32]; split <;> rfl, Keep.refl _ _, rfl⟩ h3)
    fun t ⟨_, _, _, jout, jeq, jk, j4⟩ => ⟨jeq, jout, jk, j4⟩
  have hs' := hs.congr jk.2.2
  have hst : WP isa (.block (selBody ++ ([.addi .t3 .t3 (-1)] : List Instr))) t fun t' =>
      (t'.gpr .t0 = off B (dO + 4 * i + 4) ∧ t'.gpr .t1 = off B (dA + 4 * i + 4) ∧
        t'.gpr .t2 = off B (dB + 4 * i + 4) ∧ t'.gpr .t3 = t.gpr .t3 - BitVec.ofNat 64 1 ∧
        t'.gpr .t4 = t.gpr .t4 ∧
        t'.mem = t.mem.writeW (off B (dO + 4 * i))
          (if b then t.mem.readW (off B (dB + 4 * i)) 32 else t.mem.readW (off B (dA + 4 * i)) 32)) ∧
      Keep loopRegs t t' := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [selBody, j0, j1, j2, j4, h4, exec_load_w, exec_store_w,
      hs'.ld (show dA + 4 * i + 4 ≤ Z by omega_arith), hs'.ld (show dB + 4 * i + 4 ≤ Z by omega_arith),
      hs'.st (show dO + 4 * i + 4 ≤ Z by omega_arith),
      Scr.al4 hs' (show dA + 4 * i + 4 ≤ Z by omega_arith) (by omega_arith),
      Scr.al4 hs' (show dB + 4 * i + 4 ≤ Z by omega_arith) (by omega_arith),
      Scr.al4 hs' (show dO + 4 * i + 4 ≤ Z by omega_arith) (by omega_arith), select_arith]
  refine WP.mono hst fun t' ⟨⟨l0, l1, l2, l3, l4, lm⟩, lk⟩ =>
    ⟨⟨?_, ?_, ?_, ?_, ?_, Keep.trans' jk lk, l4.trans j4⟩, l3⟩
  · rw [l0, show dO + 4 * i + 4 = dO + 4 * (i + 1) by omega_arith]
  · rw [l1, show dA + 4 * i + 4 = dA + 4 * (i + 1) by omega_arith]
  · rw [l2, show dB + 4 * i + 4 = dB + 4 * (i + 1) by omega_arith]
  · rw [lm]; exact out_step32 _ jout (by omega_arith)
  · have wa : w32 t.mem B (dA + 4 * i) = w32 s.mem B (dA + 4 * i) :=
      jout.w32 (by have := aA.outside hi; omega_arith) (by omega_arith)
    have wb : w32 t.mem B (dB + 4 * i) = w32 s.mem B (dB + 4 * i) :=
      jout.w32 (by have := aB.outside hi; omega_arith) (by omega_arith)
    rw [lm, val32_write_top _ _ _ _ _ (by omega_arith), jeq, val32_succ s.mem B dA i, val32_succ s.mem B dB i]
    cases b
    · simp only [Bool.false_eq_true, ite_false]; rw [← wa]
    · simp only [ite_true]; rw [← wb]

/-- `[o] := [a]` over `n` digits (`countLoop .t3 copyBody`). -/
theorem copyLoop_ok {s : State} {B : Addr} {Z dO dA n : Nat} (hs : Scr s B Z)
    (h0 : s.gpr .t0 = off B dO) (h1 : s.gpr .t1 = off B dA) (h3 : s.gpr .t3 = BitVec.ofNat 64 n)
    (hn : 1 ≤ n) (hn' : n < 2 ^ 32) (hO4 : dO % 4 = 0) (hA4 : dA % 4 = 0)
    (hO : dO + 4 * n ≤ Z) (hA : dA + 4 * n ≤ Z) (aA : Ahead dO dA n) :
    WP isa (countLoop .t3 copyBody) s fun t =>
      val32 t.mem B dO n = val32 s.mem B dA n ∧ Outside B dO (4 * n) s.mem t.mem ∧ Keep loopRegs s t := by
  have hnw := hs.nowrap
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .t0 = off B (dO + 4 * i) ∧ t.gpr .t1 = off B (dA + 4 * i) ∧
      Outside B dO (4 * i) s.mem t.mem ∧ val32 t.mem B dO i = val32 s.mem B dA i ∧ Keep loopRegs s t
  refine WP.mono (wp_countdown (body := .block (copyBody ++ ([.addi .t3 .t3 (-1)] : List Instr)))
    (cnt := .t3) (N := n) (by omega_arith) (by omega_arith) Inv
    (fun i hi t ⟨j0, j1, jout, jeq, jk⟩ hc => ?_)
    ⟨by rw [h0]; rfl, by rw [h1]; rfl, Outside.refl _ _ _ _, rfl, Keep.refl _ _⟩ h3)
    fun t ⟨_, _, jout, jeq, jk⟩ => ⟨jeq, jout, jk⟩
  have hs' := hs.congr jk.2.2
  have hst : WP isa (.block (copyBody ++ ([.addi .t3 .t3 (-1)] : List Instr))) t fun t' =>
      (t'.gpr .t0 = off B (dO + 4 * i + 4) ∧ t'.gpr .t1 = off B (dA + 4 * i + 4) ∧
        t'.gpr .t3 = t.gpr .t3 - BitVec.ofNat 64 1 ∧
        t'.mem = t.mem.writeW (off B (dO + 4 * i)) (t.mem.readW (off B (dA + 4 * i)) 32)) ∧
      Keep loopRegs t t' := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [copyBody, j0, j1, exec_load_w, exec_store_w, hs'.ld (show dA + 4 * i + 4 ≤ Z by omega_arith),
      hs'.st (show dO + 4 * i + 4 ≤ Z by omega_arith),
      Scr.al4 hs' (show dA + 4 * i + 4 ≤ Z by omega_arith) (by omega_arith),
      Scr.al4 hs' (show dO + 4 * i + 4 ≤ Z by omega_arith) (by omega_arith), lo32_ext]
  refine WP.mono hst fun t' ⟨⟨l0, l1, l3, lm⟩, lk⟩ => ⟨⟨?_, ?_, ?_, ?_, Keep.trans' jk lk⟩, l3⟩
  · rw [l0, show dO + 4 * i + 4 = dO + 4 * (i + 1) by omega_arith]
  · rw [l1, show dA + 4 * i + 4 = dA + 4 * (i + 1) by omega_arith]
  · rw [lm]; exact out_step32 _ jout (by omega_arith)
  · have wa : w32 t.mem B (dA + 4 * i) = w32 s.mem B (dA + 4 * i) :=
      jout.w32 (by have := aA.outside hi; omega_arith) (by omega_arith)
    rw [lm, val32_write_top _ _ _ _ _ (by omega_arith), jeq, val32_succ s.mem B dA i, ← wa]

/-- A digit of the comparison, on bit vectors. -/
theorem eq_arith (r : BitVec 64) (x y : BitVec 32) (hr : r.toNat < 2 ^ 32) :
    (r ||| (x.setWidth 64 ^^^ y.setWidth 64) = 0 ↔ r = 0 ∧ x = y) ∧
      (r ||| (x.setWidth 64 ^^^ y.setWidth 64)).toNat < 2 ^ 32 := by
  refine ⟨?_, ?_⟩
  · change (r ||| (x.setWidth 64 ^^^ y.setWidth 64)) = 0#64 ↔ r = 0#64 ∧ x = y
    rw [BitVec.or_eq_zero_iff, BitVec.xor_eq_zero_iff]
    refine and_congr_right fun _ => ⟨fun h => BitVec.eq_of_toNat_eq ?_, fun h => h ▸ rfl⟩
    have := congrArg BitVec.toNat h
    rwa [toNat_ext32, toNat_ext32] at this
  · rw [BitVec.toNat_or, BitVec.toNat_xor, toNat_ext32, toNat_ext32]
    exact Nat.or_lt_two_pow hr (Nat.xor_lt_two_pow x.isLt y.isLt)

/-- Whether `[a] = [b]` over `n` digits (`countLoop .t3 eqBody`), from `t4 = 0`:
`t4` is zero exactly when they are equal. -/
theorem eqLoop_ok {s : State} {B : Addr} {Z dA dB n : Nat} (hs : Scr s B Z)
    (h1 : s.gpr .t1 = off B dA) (h2 : s.gpr .t2 = off B dB) (h3 : s.gpr .t3 = BitVec.ofNat 64 n)
    (h4 : s.gpr .t4 = 0) (hn : 1 ≤ n) (hn' : n < 2 ^ 32) (hA4 : dA % 4 = 0) (hB4 : dB % 4 = 0)
    (hA : dA + 4 * n ≤ Z) (hB : dB + 4 * n ≤ Z) :
    WP isa (countLoop .t3 eqBody) s fun t =>
      (t.gpr .t4 = 0 ↔ val32 s.mem B dA n = val32 s.mem B dB n) ∧ (t.gpr .t4).toNat < 2 ^ 32 ∧
      t.mem = s.mem ∧ Keep loopRegs s t := by
  have hnw := hs.nowrap
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .t1 = off B (dA + 4 * i) ∧ t.gpr .t2 = off B (dB + 4 * i) ∧ t.mem = s.mem ∧
      (t.gpr .t4 = 0 ↔ val32 s.mem B dA i = val32 s.mem B dB i) ∧ (t.gpr .t4).toNat < 2 ^ 32 ∧
      Keep loopRegs s t
  refine WP.mono (wp_countdown (body := .block (eqBody ++ ([.addi .t3 .t3 (-1)] : List Instr)))
    (cnt := .t3) (N := n) (by omega_arith) (by omega_arith) Inv
    (fun i hi t ⟨j1, j2, jm, jeq, j4, jk⟩ hc => ?_)
    ⟨by rw [h1]; rfl, by rw [h2]; rfl, rfl, by simp [val32, h4], by rw [h4]; decide, Keep.refl _ _⟩ h3)
    fun t ⟨_, _, jm, jeq, j4, jk⟩ => ⟨jeq, j4, jm, jk⟩
  have hs' := hs.congr jk.2.2
  have hst : WP isa (.block (eqBody ++ ([.addi .t3 .t3 (-1)] : List Instr))) t fun t' =>
      (t'.gpr .t1 = off B (dA + 4 * i + 4) ∧ t'.gpr .t2 = off B (dB + 4 * i + 4) ∧
        t'.gpr .t3 = t.gpr .t3 - BitVec.ofNat 64 1 ∧
        t'.gpr .t4 = t.gpr .t4 ||| ((t.mem.readW (off B (dA + 4 * i)) 32).setWidth 64 ^^^
          (t.mem.readW (off B (dB + 4 * i)) 32).setWidth 64) ∧ t'.mem = t.mem) ∧
      Keep loopRegs t t' := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [eqBody, j1, j2, exec_load_w, hs'.ld (show dA + 4 * i + 4 ≤ Z by omega_arith),
      hs'.ld (show dB + 4 * i + 4 ≤ Z by omega_arith),
      Scr.al4 hs' (show dA + 4 * i + 4 ≤ Z by omega_arith) (by omega_arith),
      Scr.al4 hs' (show dB + 4 * i + 4 ≤ Z by omega_arith) (by omega_arith)]
  refine WP.mono hst fun t' ⟨⟨l1, l2, l3, l4, lm⟩, lk⟩ => ⟨⟨?_, ?_, lm.trans jm, ?_, ?_, Keep.trans' jk lk⟩, l3⟩
  · rw [l1, show dA + 4 * i + 4 = dA + 4 * (i + 1) by omega_arith]
  · rw [l2, show dB + 4 * i + 4 = dB + 4 * (i + 1) by omega_arith]
  · rw [l4, (eq_arith _ _ _ j4).1, jeq, jm, val32_succ s.mem B dA i, val32_succ s.mem B dB i,
      split_eq_iff (Nat.two_pow_pos _) (val32_lt _ _ _ _) (val32_lt _ _ _ _)]
    refine and_congr_right fun _ => ⟨fun h => congrArg BitVec.toNat h, fun h => BitVec.eq_of_toNat_eq h⟩
  · rw [l4]; exact (eq_arith _ _ _ j4).2

/-- `[o]`'s `n` digits := 0 (`countLoop .t3 [sw t5, 0(t0); addi t0, t0, 4]`, `t5 = 0`). -/
theorem zeroLoop_ok {s : State} {B : Addr} {Z dO n : Nat} (hs : Scr s B Z)
    (h0 : s.gpr .t0 = off B dO) (h3 : s.gpr .t3 = BitVec.ofNat 64 n) (h5 : s.gpr .t5 = 0)
    (hn : 1 ≤ n) (hn' : n < 2 ^ 32) (hO4 : dO % 4 = 0) (hO : dO + 4 * n ≤ Z) :
    WP isa (countLoop .t3 [.store .w .t5 .t0 0, .addi .t0 .t0 4]) s fun t =>
      (∀ j < n, w32 t.mem B (dO + 4 * j) = 0) ∧ Outside B dO (4 * n) s.mem t.mem ∧
      Keep [.t0, .t3] s t := by
  have hnw := hs.nowrap
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .t0 = off B (dO + 4 * i) ∧ Outside B dO (4 * i) s.mem t.mem ∧
      (∀ j < i, w32 t.mem B (dO + 4 * j) = 0) ∧ Keep [.t0, .t3] s t
  refine WP.mono (wp_countdown (body := .block ([.store .w .t5 .t0 0, .addi .t0 .t0 4] ++
      ([.addi .t3 .t3 (-1)] : List Instr)))
    (cnt := .t3) (N := n) (by omega_arith) (by omega_arith) Inv
    (fun i hi t ⟨j0, jout, jz, jk⟩ hc => ?_)
    ⟨by rw [h0]; rfl, Outside.refl _ _ _ _, fun _ h => absurd h (Nat.not_lt_zero _), Keep.refl _ _⟩ h3)
    fun t ⟨_, jout, jz, jk⟩ => ⟨jz, jout, jk⟩
  have hs' := hs.congr jk.2.2
  have t5 : t.gpr .t5 = 0 := (jk.gpr (by decide)).trans h5
  have hst : WP isa (.block [.store .w .t5 .t0 0, .addi .t0 .t0 4, .addi .t3 .t3 (-1)]) t
      fun t' => (t'.gpr .t0 = off B (dO + 4 * i + 4) ∧ t'.gpr .t3 = t.gpr .t3 - BitVec.ofNat 64 1 ∧
        t'.mem = t.mem.writeW (off B (dO + 4 * i)) (0 : BitVec 32)) ∧ Keep [.t0, .t3] t t' := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [j0, t5, exec_store_w, hs'.st (show dO + 4 * i + 4 ≤ Z by omega_arith),
      Scr.al4 hs' (show dO + 4 * i + 4 ≤ Z by omega_arith) (by omega_arith)]
    rfl
  refine WP.mono hst fun t' ⟨⟨l0, l3, lm⟩, lk⟩ => ⟨⟨?_, ?_, ?_, Keep.trans' jk lk⟩, l3⟩
  · rw [l0, show dO + 4 * i + 4 = dO + 4 * (i + 1) by omega_arith]
  · rw [lm]; exact out_step32 _ jout (by omega_arith)
  · intro j hj
    rw [lm]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [((writeW32_outside _ B (d := dO + 4 * i) (0 : BitVec 32) (by omega_arith))).w32
        (by omega_arith) (by omega_arith)]
      exact jz j hj
    · exact w32_write_self _ _ _ _

end VG.Proof.Rsa.RISCV64.InvBatch
