module

public import VerifiedGarbage.Impl.Rsa.PPC64LE.KeyWs
public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFinish
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontRound
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontStep
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The digit loops of the RSA key operations on PPC64LE

Each loop runs over `n` digits of 32 bits at byte offsets of the working
space (`Scr s B Z`), its pointers in `r5`–`r7` and its count in `r8`
(`countLoop .r8 body`):

* `subLoop_ok`: `[o] := [a] - [b]`, the borrow in `r9`;
* `selLoop_ok`: `[o] := mask ? [b] : [a]`, the mask in `r9`;
* `copyLoop_ok`: `[o] := [a]`.

The output may be an input (`o = a`, as the division's selection is), or
come before it, or be apart from it: a digit is read before any digit at or
after it is written.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.Loops

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Impl.Rsa.PPC64LE.Keys

/-- The registers the digit loops change. -/
abbrev loopRegs : List Reg := [.r0, .r3, .r5, .r6, .r7, .r8, .r9]

/-- The registers the selection changes: it keeps the mask. -/
abbrev selRegs : List Reg := [.r0, .r3, .r5, .r6, .r7, .r8]

/-- Array `a` (at `dA`) is read after `o` (at `dO`) is written up to the
same digit: it is `o` or after it, or apart from it. -/
def Ahead (dO dA n : Nat) : Prop := dO ≤ dA ∨ dA + 4 * n ≤ dO

/-- A digit at `dA + 4 i` is outside the digits written before it. -/
theorem Ahead.outside {dO dA n i : Nat} (h : Ahead dO dA n) (hi : i < n) :
    dA + 4 * i + 4 ≤ dO ∨ dO + 4 * i ≤ dA + 4 * i := by
  unfold Ahead at h; omega

/-- `[o] := [a] - [b]` over `n` digits (`countLoop .r8 subBody`), from the
borrow `c` in `r9`: the difference and the borrow out. -/
theorem subLoop_ok {s : State} {B : Addr} {Z dO dA dB n : Nat} (hs : Scr s B Z)
    (h5 : s.gpr .r5 = off B dO) (h6 : s.gpr .r6 = off B dA) (h7 : s.gpr .r7 = off B dB)
    (h8 : s.gpr .r8 = BitVec.ofNat 64 n) (h9 : (s.gpr .r9).toNat ≤ 1) (hn : 1 ≤ n) (hn' : n < 2 ^ 32)
    (hO : dO + 4 * n ≤ Z) (hA : dA + 4 * n ≤ Z) (hB : dB + 4 * n ≤ Z)
    (aA : Ahead dO dA n) (aB : Ahead dO dB n) :
    WP isa (countLoop .r8 subBody) s fun t =>
      (t.gpr .r9).toNat ≤ 1 ∧
      val32 t.mem B dO n + val32 s.mem B dB n + (s.gpr .r9).toNat =
        val32 s.mem B dA n + 2 ^ (32 * n) * (t.gpr .r9).toNat ∧
      Outside B dO (4 * n) s.mem t.mem ∧ Keep loopRegs s t := by
  have hnw := hs.nowrap
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .r5 = off B (dO + 4 * i) ∧ t.gpr .r6 = off B (dA + 4 * i) ∧ t.gpr .r7 = off B (dB + 4 * i) ∧
      (t.gpr .r9).toNat ≤ 1 ∧ Outside B dO (4 * i) s.mem t.mem ∧
      val32 t.mem B dO i + val32 s.mem B dB i + (s.gpr .r9).toNat =
        val32 s.mem B dA i + 2 ^ (32 * i) * (t.gpr .r9).toNat ∧
      Keep loopRegs s t
  refine WP.mono (wp_countdown (body := .block (subBody ++ ([.subi .r8 .r8 1] : List Instr)))
    (cnt := .r8) (N := n) (by omega_arith) (by omega_arith) Inv
    (fun i hi t ⟨j5, j6, j7, j9, jout, jeq, jk⟩ hc => ?_)
    ⟨by rw [h5]; rfl, by rw [h6]; rfl, by rw [h7]; rfl, h9, Outside.refl _ _ _ _,
      by simp [val32], Keep.refl _ _⟩ h8)
    fun t ⟨_, _, _, j9, jout, jeq, jk⟩ => ⟨j9, jeq, jout, jk⟩
  have hst := (show WP isa (.block (subBody ++ ([.subi .r8 .r8 1] : List Instr))) t fun t' =>
      let D := (t.mem.readW (off B (dA + 4 * i)) 32).setWidth 64 -
        (t.mem.readW (off B (dB + 4 * i)) 32).setWidth 64 - t.gpr .r9
      (t'.gpr .r5 = off B (dO + 4 * i + 4) ∧ t'.gpr .r6 = off B (dA + 4 * i + 4) ∧
        t'.gpr .r7 = off B (dB + 4 * i + 4) ∧ t'.gpr .r9 = D >>> 63 ∧
        t'.gpr .r8 = t.gpr .r8 - BitVec.ofNat 64 1 ∧
        t'.mem = t.mem.writeW (off B (dO + 4 * i)) (D.setWidth 32)) ∧ Keep loopRegs t t' from by
    refine WP.keep _ ?_ (by decide)
    prun [subBody, j5, j6, j7, (hs.congr jk.wr).ld (show dA + 4 * i + 4 ≤ Z by omega_arith),
      (hs.congr jk.wr).ld (show dB + 4 * i + 4 ≤ Z by omega_arith),
      (hs.congr jk.wr).st (show dO + 4 * i + 4 ≤ Z by omega_arith)])
  refine WP.mono hst fun t' ⟨⟨l5, l6, l7, l9, l8, lm⟩, lk⟩ => ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, jk.trans' lk⟩, l8⟩
  · rw [l5, show dO + 4 * i + 4 = dO + 4 * (i + 1) by omega_arith]
  · rw [l6, show dA + 4 * i + 4 = dA + 4 * (i + 1) by omega_arith]
  · rw [l7, show dB + 4 * i + 4 = dB + 4 * (i + 1) by omega_arith]
  · rw [l9]; exact (sub_arith _ _ _ j9).1
  · rw [lm]
    exact (jout.mono (Nat.le_refl _) (by omega_arith)).trans
      ((writeW32_outside _ B (d := dO + 4 * i) _ (by omega_arith)).mono (by omega_arith) (by omega_arith))
  · have wa : w32 t.mem B (dA + 4 * i) = w32 s.mem B (dA + 4 * i) :=
      jout.w32 (by have := aA.outside hi; omega_arith) (by omega_arith)
    have wb : w32 t.mem B (dB + 4 * i) = w32 s.mem B (dB + 4 * i) :=
      jout.w32 (by have := aB.outside hi; omega_arith) (by omega_arith)
    have k := (sub_arith (t.mem.readW (off B (dA + 4 * i)) 32) (t.mem.readW (off B (dB + 4 * i)) 32) _ j9).2
    rw [lm, l9, val32_write_top _ _ _ _ _ (by omega_arith), val32_succ s.mem B dB i, val32_succ s.mem B dA i,
      ← pow32_mul i]
    change _ + _ + (_ + _ * w32 s.mem B (dB + 4 * i)) + _ = _ + _ * w32 s.mem B (dA + 4 * i) + _
    rw [← wa, ← wb]
    change (t.gpr .r9).toNat + _ + w32 t.mem B (dB + 4 * i) = w32 t.mem B (dA + 4 * i) + _ at k
    grind

/-- `[o] := b ? [b] : [a]` over `n` digits (`countLoop .r8 selBody`), the
mask of `b` in `r9`. -/
theorem selLoop_ok {s : State} {B : Addr} {Z dO dA dB n : Nat} (hs : Scr s B Z) {b : Bool}
    (h5 : s.gpr .r5 = off B dO) (h6 : s.gpr .r6 = off B dA) (h7 : s.gpr .r7 = off B dB)
    (h8 : s.gpr .r8 = BitVec.ofNat 64 n)
    (h9 : s.gpr .r9 = BitVec.ofNat 64 0 - BitVec.ofNat 64 (if b then 1 else 0)) (hn : 1 ≤ n)
    (hn' : n < 2 ^ 32) (hO : dO + 4 * n ≤ Z) (hA : dA + 4 * n ≤ Z) (hB : dB + 4 * n ≤ Z)
    (aA : Ahead dO dA n) (aB : Ahead dO dB n) :
    WP isa (countLoop .r8 selBody) s fun t =>
      val32 t.mem B dO n = (if b then val32 s.mem B dB n else val32 s.mem B dA n) ∧
      Outside B dO (4 * n) s.mem t.mem ∧ Keep selRegs s t := by
  have hnw := hs.nowrap
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .r5 = off B (dO + 4 * i) ∧ t.gpr .r6 = off B (dA + 4 * i) ∧ t.gpr .r7 = off B (dB + 4 * i) ∧
      Outside B dO (4 * i) s.mem t.mem ∧
      val32 t.mem B dO i = (if b then val32 s.mem B dB i else val32 s.mem B dA i) ∧
      Keep selRegs s t
  refine WP.mono (wp_countdown (body := .block (selBody ++ ([.subi .r8 .r8 1] : List Instr)))
    (cnt := .r8) (N := n) (by omega_arith) (by omega_arith) Inv
    (fun i hi t ⟨j5, j6, j7, jout, jeq, jk⟩ hc => ?_)
    ⟨by rw [h5]; rfl, by rw [h6]; rfl, by rw [h7]; rfl, Outside.refl _ _ _ _,
      by simp only [val32]; split <;> rfl, Keep.refl _ _⟩ h8)
    fun t ⟨_, _, _, jout, jeq, jk⟩ => ⟨jeq, jout, jk⟩
  have r9 : t.gpr .r9 = s.gpr .r9 := jk.gpr _ (by decide)
  have hst : WP isa (.block (selBody ++ ([.subi .r8 .r8 1] : List Instr))) t fun t' =>
      (t'.gpr .r5 = off B (dO + 4 * i + 4) ∧ t'.gpr .r6 = off B (dA + 4 * i + 4) ∧
        t'.gpr .r7 = off B (dB + 4 * i + 4) ∧ t'.gpr .r8 = t.gpr .r8 - BitVec.ofNat 64 1 ∧
        t'.mem = t.mem.writeW (off B (dO + 4 * i))
          (if b then t.mem.readW (off B (dB + 4 * i)) 32 else t.mem.readW (off B (dA + 4 * i)) 32)) ∧
      Keep selRegs t t' := by
    refine WP.keep _ ?_ (by decide)
    prun [selBody, j5, j6, j7, r9, h9, (hs.congr jk.wr).ld (show dA + 4 * i + 4 ≤ Z by omega_arith),
      (hs.congr jk.wr).ld (show dB + 4 * i + 4 ≤ Z by omega_arith),
      (hs.congr jk.wr).st (show dO + 4 * i + 4 ≤ Z by omega_arith), select_arith]
  refine WP.mono hst fun t' ⟨⟨l5, l6, l7, l8, lm⟩, lk⟩ => ⟨⟨?_, ?_, ?_, ?_, ?_, jk.trans' lk⟩, l8⟩
  · rw [l5, show dO + 4 * i + 4 = dO + 4 * (i + 1) by omega_arith]
  · rw [l6, show dA + 4 * i + 4 = dA + 4 * (i + 1) by omega_arith]
  · rw [l7, show dB + 4 * i + 4 = dB + 4 * (i + 1) by omega_arith]
  · rw [lm]
    exact (jout.mono (Nat.le_refl _) (by omega_arith)).trans
      ((writeW32_outside _ B (d := dO + 4 * i) _ (by omega_arith)).mono (by omega_arith) (by omega_arith))
  · have wa : w32 t.mem B (dA + 4 * i) = w32 s.mem B (dA + 4 * i) :=
      jout.w32 (by have := aA.outside hi; omega_arith) (by omega_arith)
    have wb : w32 t.mem B (dB + 4 * i) = w32 s.mem B (dB + 4 * i) :=
      jout.w32 (by have := aB.outside hi; omega_arith) (by omega_arith)
    rw [lm, val32_write_top _ _ _ _ _ (by omega_arith), jeq, val32_succ s.mem B dA i, val32_succ s.mem B dB i]
    cases b
    · simp only [Bool.false_eq_true, ite_false]; rw [← wa]
    · simp only [ite_true]; rw [← wb]

/-- `[o] := [a]` over `n` digits (`countLoop .r8 copyBody`). -/
theorem copyLoop_ok {s : State} {B : Addr} {Z dO dA n : Nat} (hs : Scr s B Z)
    (h5 : s.gpr .r5 = off B dO) (h6 : s.gpr .r6 = off B dA) (h8 : s.gpr .r8 = BitVec.ofNat 64 n)
    (hn : 1 ≤ n) (hn' : n < 2 ^ 32) (hO : dO + 4 * n ≤ Z) (hA : dA + 4 * n ≤ Z) (aA : Ahead dO dA n) :
    WP isa (countLoop .r8 copyBody) s fun t =>
      val32 t.mem B dO n = val32 s.mem B dA n ∧ Outside B dO (4 * n) s.mem t.mem ∧ Keep loopRegs s t := by
  have hnw := hs.nowrap
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .r5 = off B (dO + 4 * i) ∧ t.gpr .r6 = off B (dA + 4 * i) ∧
      Outside B dO (4 * i) s.mem t.mem ∧ val32 t.mem B dO i = val32 s.mem B dA i ∧ Keep loopRegs s t
  refine WP.mono (wp_countdown (body := .block (copyBody ++ ([.subi .r8 .r8 1] : List Instr)))
    (cnt := .r8) (N := n) (by omega_arith) (by omega_arith) Inv
    (fun i hi t ⟨j5, j6, jout, jeq, jk⟩ hc => ?_)
    ⟨by rw [h5]; rfl, by rw [h6]; rfl, Outside.refl _ _ _ _, rfl, Keep.refl _ _⟩ h8)
    fun t ⟨_, _, jout, jeq, jk⟩ => ⟨jeq, jout, jk⟩
  have hst : WP isa (.block (copyBody ++ ([.subi .r8 .r8 1] : List Instr))) t fun t' =>
      (t'.gpr .r5 = off B (dO + 4 * i + 4) ∧ t'.gpr .r6 = off B (dA + 4 * i + 4) ∧
        t'.gpr .r8 = t.gpr .r8 - BitVec.ofNat 64 1 ∧
        t'.mem = t.mem.writeW (off B (dO + 4 * i)) (t.mem.readW (off B (dA + 4 * i)) 32)) ∧
      Keep loopRegs t t' := by
    refine WP.keep _ ?_ (by decide)
    prun [copyBody, j5, j6, (hs.congr jk.wr).ld (show dA + 4 * i + 4 ≤ Z by omega_arith),
      (hs.congr jk.wr).st (show dO + 4 * i + 4 ≤ Z by omega_arith), lo32_ext]
  refine WP.mono hst fun t' ⟨⟨l5, l6, l8, lm⟩, lk⟩ => ⟨⟨?_, ?_, ?_, ?_, jk.trans' lk⟩, l8⟩
  · rw [l5, show dO + 4 * i + 4 = dO + 4 * (i + 1) by omega_arith]
  · rw [l6, show dA + 4 * i + 4 = dA + 4 * (i + 1) by omega_arith]
  · rw [lm]
    exact (jout.mono (Nat.le_refl _) (by omega_arith)).trans
      ((writeW32_outside _ B (d := dO + 4 * i) _ (by omega_arith)).mono (by omega_arith) (by omega_arith))
  · have wa : w32 t.mem B (dA + 4 * i) = w32 s.mem B (dA + 4 * i) :=
      jout.w32 (by have := aA.outside hi; omega_arith) (by omega_arith)
    rw [lm, val32_write_top _ _ _ _ _ (by omega_arith), jeq, val32_succ s.mem B dA i, ← wa]

/-- Two numbers of a low part below `K` and a high part are equal exactly
when both parts are. -/
theorem split_eq_iff {x y a b K : Nat} (hK : 0 < K) (hx : x < K) (hy : y < K) :
    x + K * a = y + K * b ↔ x = y ∧ a = b := by
  constructor
  · intro h
    have hm := congrArg (· % K) h
    have hd := congrArg (· / K) h
    simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at hm
    simp only [Nat.add_mul_div_left _ _ hK, Nat.div_eq_of_lt hx, Nat.div_eq_of_lt hy,
      Nat.zero_add] at hd
    exact ⟨hm, hd⟩
  · rintro ⟨rfl, rfl⟩; rfl

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

/-- Whether `[a] = [b]` over `n` digits (`countLoop .r8 eqBody`), from `r9 = 0`:
`r9` is zero exactly when they are equal. -/
theorem eqLoop_ok {s : State} {B : Addr} {Z dA dB n : Nat} (hs : Scr s B Z)
    (h6 : s.gpr .r6 = off B dA) (h7 : s.gpr .r7 = off B dB) (h8 : s.gpr .r8 = BitVec.ofNat 64 n)
    (h9 : s.gpr .r9 = 0) (hn : 1 ≤ n) (hn' : n < 2 ^ 32) (hA : dA + 4 * n ≤ Z) (hB : dB + 4 * n ≤ Z) :
    WP isa (countLoop .r8 eqBody) s fun t =>
      (t.gpr .r9 = 0 ↔ val32 s.mem B dA n = val32 s.mem B dB n) ∧ (t.gpr .r9).toNat < 2 ^ 32 ∧
      t.mem = s.mem ∧ Keep loopRegs s t := by
  have hnw := hs.nowrap
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .r6 = off B (dA + 4 * i) ∧ t.gpr .r7 = off B (dB + 4 * i) ∧ t.mem = s.mem ∧
      (t.gpr .r9 = 0 ↔ val32 s.mem B dA i = val32 s.mem B dB i) ∧ (t.gpr .r9).toNat < 2 ^ 32 ∧
      Keep loopRegs s t
  refine WP.mono (wp_countdown (body := .block (eqBody ++ ([.subi .r8 .r8 1] : List Instr)))
    (cnt := .r8) (N := n) (by omega_arith) (by omega_arith) Inv
    (fun i hi t ⟨j6, j7, jm, jeq, j9, jk⟩ hc => ?_)
    ⟨by rw [h6]; rfl, by rw [h7]; rfl, rfl, by simp [val32, h9], by rw [h9]; decide, Keep.refl _ _⟩ h8)
    fun t ⟨_, _, jm, jeq, j9, jk⟩ => ⟨jeq, j9, jm, jk⟩
  have hst : WP isa (.block (eqBody ++ ([.subi .r8 .r8 1] : List Instr))) t fun t' =>
      (t'.gpr .r6 = off B (dA + 4 * i + 4) ∧ t'.gpr .r7 = off B (dB + 4 * i + 4) ∧
        t'.gpr .r8 = t.gpr .r8 - BitVec.ofNat 64 1 ∧
        t'.gpr .r9 = t.gpr .r9 ||| ((t.mem.readW (off B (dA + 4 * i)) 32).setWidth 64 ^^^
          (t.mem.readW (off B (dB + 4 * i)) 32).setWidth 64) ∧ t'.mem = t.mem) ∧
      Keep loopRegs t t' := by
    refine WP.keep _ ?_ (by decide)
    prun [eqBody, j6, j7, (hs.congr jk.wr).ld (show dA + 4 * i + 4 ≤ Z by omega_arith),
      (hs.congr jk.wr).ld (show dB + 4 * i + 4 ≤ Z by omega_arith)]
  refine WP.mono hst fun t' ⟨⟨l6, l7, l8, l9, lm⟩, lk⟩ => ⟨⟨?_, ?_, lm.trans jm, ?_, ?_, jk.trans' lk⟩, l8⟩
  · rw [l6, show dA + 4 * i + 4 = dA + 4 * (i + 1) by omega_arith]
  · rw [l7, show dB + 4 * i + 4 = dB + 4 * (i + 1) by omega_arith]
  · rw [l9, (eq_arith _ _ _ j9).1, jeq, jm, val32_succ s.mem B dA i, val32_succ s.mem B dB i,
      split_eq_iff (Nat.two_pow_pos _) (val32_lt _ _ _ _) (val32_lt _ _ _ _)]
    refine and_congr_right fun _ => ⟨fun h => congrArg BitVec.toNat h, fun h => BitVec.eq_of_toNat_eq h⟩
  · rw [l9]; exact (eq_arith _ _ _ j9).2

/-- `[o]`'s `n` digits := 0 (`countLoop .r8 [stw r0, 0(r5); addi r5, r5, 4]`, `r0 = 0`). -/
theorem zeroLoop_ok {s : State} {B : Addr} {Z dO n : Nat} (hs : Scr s B Z)
    (h5 : s.gpr .r5 = off B dO) (h8 : s.gpr .r8 = BitVec.ofNat 64 n) (h0 : s.gpr .r0 = 0)
    (hn : 1 ≤ n) (hn' : n < 2 ^ 32) (hO : dO + 4 * n ≤ Z) :
    WP isa (countLoop .r8 [.store .w .r0 .r5 0, .addi .r5 .r5 4]) s fun t =>
      (∀ j < n, w32 t.mem B (dO + 4 * j) = 0) ∧ Outside B dO (4 * n) s.mem t.mem ∧
      Keep [.r5, .r8] s t := by
  have hnw := hs.nowrap
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .r5 = off B (dO + 4 * i) ∧ Outside B dO (4 * i) s.mem t.mem ∧
      (∀ j < i, w32 t.mem B (dO + 4 * j) = 0) ∧ Keep [.r5, .r8] s t
  refine WP.mono (wp_countdown (body := .block ([.store .w .r0 .r5 0, .addi .r5 .r5 4] ++
      ([.subi .r8 .r8 1] : List Instr)))
    (cnt := .r8) (N := n) (by omega_arith) (by omega_arith) Inv
    (fun i hi t ⟨j5, jout, jz, jk⟩ hc => ?_)
    ⟨by rw [h5]; rfl, Outside.refl _ _ _ _, fun _ h => absurd h (Nat.not_lt_zero _), Keep.refl _ _⟩ h8)
    fun t ⟨_, jout, jz, jk⟩ => ⟨jz, jout, jk⟩
  have r0 : t.gpr .r0 = 0 := (jk.gpr _ (by decide)).trans h0
  have hst : WP isa (.block ([.store .w .r0 .r5 0, .addi .r5 .r5 4] ++ ([.subi .r8 .r8 1] : List Instr))) t
      fun t' => (t'.gpr .r5 = off B (dO + 4 * i + 4) ∧ t'.gpr .r8 = t.gpr .r8 - BitVec.ofNat 64 1 ∧
        t'.mem = t.mem.writeW (off B (dO + 4 * i)) (0 : BitVec 32)) ∧ Keep [.r5, .r8] t t' := by
    refine WP.keep _ ?_ (by decide)
    prun [j5, r0, (hs.congr jk.wr).st (show dO + 4 * i + 4 ≤ Z by omega_arith)]
    rfl
  refine WP.mono hst fun t' ⟨⟨l5, l8, lm⟩, lk⟩ => ⟨⟨?_, ?_, ?_, jk.trans' lk⟩, l8⟩
  · rw [l5, show dO + 4 * i + 4 = dO + 4 * (i + 1) by omega_arith]
  · rw [lm]
    exact (jout.mono (Nat.le_refl _) (by omega_arith)).trans
      ((writeW32_outside _ B (d := dO + 4 * i) _ (by omega_arith)).mono (by omega_arith) (by omega_arith))
  · intro j hj
    rw [lm]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [((writeW32_outside _ B (d := dO + 4 * i) (0 : BitVec 32) (by omega_arith))).w32
        (by omega_arith) (by omega_arith)]
      exact jz j hj
    · exact w32_write_self _ _ _ _

end VG.Proof.Rsa.PPC64LE.Loops
