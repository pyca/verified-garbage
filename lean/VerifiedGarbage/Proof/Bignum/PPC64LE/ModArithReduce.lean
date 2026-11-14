module

import VerifiedGarbage.Proof.Bignum.PPC64LE.MontRound
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFinish
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreDouble
import VerifiedGarbage.Proof.Bignum.Math
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Impl.Bignum.PPC64LE.ModArith
public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Bignum.PPC64LE.Double64
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMont
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubPower
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubE
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCheck
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCore

/-! ### `Bignum.PPC64LE.ModArithDouble`, which only this module used -/

section

/-!
# Modular arithmetic on PPC64LE: doubling with a bit

`doubleBit_ok`: the accumulator's `n + 1` digits := `2 x + b`, `b` the top bit
of `r24`. `doubleBitMod_ok`: `x := 2 x + b mod m`, in arrays 0–3.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.ModArith

open VG VG.PPC64LE VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.Precompute
open VG.Impl.Bignum.PPC64LE.ModArith VG.Proof.Bignum.PPC64LE

/-- `doubleBit`, `x` (`n` digits) at `dX`, the accumulator at `dA` and `b` the
top bit of `r24`: the accumulator's `n + 1` digits are `2 x + b`, and `r24` is
shifted left. -/
theorem doubleBit_ok {s : State} {B : Addr} {Z dA dX n : Nat} (hs : Scr s B Z)
    (h8 : s.gpr .r8 = off B dA) (h5 : s.gpr .r5 = off B dX) (h11 : s.gpr .r11 = BitVec.ofNat 64 n)
    (hn : 1 ≤ n) (hn' : n < 2 ^ 32) (hA : dA + 4 * (n + 1) ≤ Z) (hX : dX + 4 * n ≤ Z)
    (dXA : dX + 4 * n ≤ dA ∨ dA + 4 * (n + 1) ≤ dX) :
    WP isa doubleBit s fun s' =>
      val32 s'.mem B dA (n + 1) = 2 * val32 s.mem B dX n + (s.gpr .r24 >>> 63).toNat ∧
      s'.gpr .r24 = s.gpr .r24 <<< 1 ∧
      Mont.Outside B dA (4 * (n + 1)) s.mem s'.mem ∧ Keep [.r0, .r14, .r15, .r17, .r20, .r24] s s' := by
  have hnw := hs.nowrap
  unfold doubleBit
  refine WP.seq ?_
  have hpre : WP isa (.block [.addi .r14 .r8 0, .addi .r15 .r5 0, .addi .r17 .r11 0, .lsr .d .r20 .r24 63,
      .lsl .r24 .r24 1]) s
      fun s₁ => (s₁.gpr .r14 = off B dA ∧ s₁.gpr .r15 = off B dX ∧ s₁.gpr .r17 = BitVec.ofNat 64 n ∧
        s₁.gpr .r20 = s.gpr .r24 >>> 63 ∧ s₁.gpr .r24 = s.gpr .r24 <<< 1 ∧ s₁.mem = s.mem) ∧
        Keep [.r0, .r14, .r15, .r17, .r20, .r24] s s₁ := by
    refine WP.keep _ ?_ (by decide)
    prun [h8, h5, h11, BitVec.add_zero]
  refine WP.mono hpre fun s₁ ⟨⟨i14, i15, i17, i20, i24, im⟩, k₁⟩ => ?_
  have hb : (s.gpr .r24 >>> 63).toNat ≤ 1 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; have := (s.gpr .r24).isLt; omega_arith
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .r14 = off B (dA + 4 * i) ∧ t.gpr .r15 = off B (dX + 4 * i) ∧
      (t.gpr .r20).toNat ≤ 1 ∧ Mont.Outside B dA (4 * i) s.mem t.mem ∧
      val32 t.mem B dA i + 2 ^ (32 * i) * (t.gpr .r20).toNat = 2 * val32 s.mem B dX i + (s.gpr .r24 >>> 63).toNat ∧
      t.gpr .r24 = s.gpr .r24 <<< 1 ∧ Keep [.r0, .r14, .r15, .r17, .r20, .r24] s t
  refine WP.seq (WP.mono (wp_countdown (body := .block ([.load .w .r0 .r15 0, .add .r0 .r0 .r0,
      .add .r0 .r0 .r20, .store .w .r0 .r14 0, .lsr .d .r20 .r0 32, .addi .r14 .r14 4,
      .addi .r15 .r15 4] ++ ([.subi .r17 .r17 1] : List Instr)))
    (cnt := .r17) (N := n) (by omega_arith) (by omega_arith) Inv (fun i hi t ⟨j14, j15, j20, jout, jeq, j24, jk⟩ hc => ?_)
    ⟨by rw [i14]; rfl, by rw [i15]; rfl, by rw [i20]; exact hb,
      by rw [← im]; exact Mont.Outside.refl _ _ _ _, by simp [val32, i20], i24, k₁⟩ i17)
    fun t ⟨j14, _, j20, jout, jeq, j24, jk⟩ => ?_)
  · have hst := (show WP isa (.block [.load .w .r0 .r15 0, .add .r0 .r0 .r0, .add .r0 .r0 .r20,
        .store .w .r0 .r14 0, .lsr .d .r20 .r0 32, .addi .r14 .r14 4, .addi .r15 .r15 4,
        .subi .r17 .r17 1]) t fun t' =>
        let D := (t.mem.readW (off B (dX + 4 * i)) 32).setWidth 64 +
          (t.mem.readW (off B (dX + 4 * i)) 32).setWidth 64 + t.gpr .r20
        t'.gpr .r14 = off B (dA + 4 * i + 4) ∧ t'.gpr .r15 = off B (dX + 4 * i + 4) ∧
          t'.gpr .r20 = D >>> 32 ∧ t'.gpr .r17 = t.gpr .r17 - BitVec.ofNat 64 1 ∧
          t'.mem = t.mem.writeW (off B (dA + 4 * i)) (D.setWidth 32) ∧
          Keep [.r0, .r14, .r15, .r17, .r20] t t' from by
      refine WP.mono (WP.keep [.r0, .r14, .r15, .r17, .r20] (Q := fun t' =>
        let D := (t.mem.readW (off B (dX + 4 * i)) 32).setWidth 64 +
          (t.mem.readW (off B (dX + 4 * i)) 32).setWidth 64 + t.gpr .r20
        t'.gpr .r14 = off B (dA + 4 * i + 4) ∧ t'.gpr .r15 = off B (dX + 4 * i + 4) ∧
          t'.gpr .r20 = D >>> 32 ∧ t'.gpr .r17 = t.gpr .r17 - BitVec.ofNat 64 1 ∧
          t'.mem = t.mem.writeW (off B (dA + 4 * i)) (D.setWidth 32)) ?_ (by decide))
        fun t' ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2, k⟩
      prun [j14, j15, (hs.congr jk.wr).ld (show dX + 4 * i + 4 ≤ Z by omega_arith),
        (hs.congr jk.wr).st (show dA + 4 * i + 4 ≤ Z by omega_arith)])
    refine WP.mono hst fun t' ⟨l14, l15, l20, l17, lm, lk⟩ =>
      ⟨⟨?_, ?_, ?_, ?_, ?_, by rw [lk.gpr .r24 (by decide)]; exact j24, jk.trans' lk.mono⟩, l17⟩
    · rw [l14, show dA + 4 * i + 4 = dA + 4 * (i + 1) by omega_arith]
    · rw [l15, show dX + 4 * i + 4 = dX + 4 * (i + 1) by omega_arith]
    · rw [l20]; exact (dbl_arith _ _ j20).1
    · rw [lm]
      exact (jout.mono (Nat.le_refl _) (by omega_arith)).trans
        ((writeW32_outside _ B (d := dA + 4 * i) _ (by omega_arith)).mono (by omega_arith) (by omega_arith))
    · have wx : w32 t.mem B (dX + 4 * i) = w32 s.mem B (dX + 4 * i) := jout.w32 (by omega_arith) (by omega_arith)
      have k := (dbl_arith (t.mem.readW (off B (dX + 4 * i)) 32) _ j20).2
      rw [lm, l20, val32_write_top _ _ _ _ _ (by omega_arith), val32_succ s.mem B dX i, ← pow32_mul i]
      rw [← wx]
      change _ + 2 ^ 32 * _ = 2 * w32 t.mem B (dX + 4 * i) + (t.gpr .r20).toNat at k
      change _ = 2 * (_ + _ * w32 t.mem B (dX + 4 * i)) + _
      grind
  · have hfin : WP isa (.block [.store .w .r20 .r14 0]) t fun t' =>
        t'.mem = t.mem.writeW (off B (dA + 4 * n)) ((t.gpr .r20).setWidth 32) ∧ Keep [] t t' := by
      refine WP.mono (WP.keep [] (Q := fun t' => t'.mem = t.mem.writeW (off B (dA + 4 * n))
        ((t.gpr .r20).setWidth 32)) ?_ (by decide)) fun t' ⟨h, k⟩ => ⟨h, k⟩
      prun [j14, (hs.congr jk.wr).st (show dA + 4 * n + 4 ≤ Z by omega_arith)]
    refine WP.mono hfin fun t' ⟨lm, lk⟩ => ⟨?_, by rw [lk.gpr .r24 (by decide)]; exact j24, ?_,
      jk.trans' lk.mono⟩
    · rw [lm, val32_write_top _ _ _ _ _ (by omega_arith), ← jeq]
      congr 2
      rw [BitVec.toNat_setWidth]
      omega_arith
    · rw [lm]
      exact (jout.mono (Nat.le_refl _) (by omega_arith)).trans
        ((writeW32_outside _ B (d := dA + 4 * n) _ (by omega_arith)).mono (by omega_arith) (by omega_arith))

theorem doubleBitMod_ok {s : State} {B : Addr} {Z w : Nat} (hs : Scr s B Z)
    (h8 : s.gpr .r8 = off B (slot w 2)) (h9 : s.gpr .r9 = off B (slot w 3))
    (h10 : s.gpr .r10 = off B (slot w 0)) (h5 : s.gpr .r5 = off B (slot w 1))
    (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w)) (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hZ : slot w 4 ≤ Z)
    (hx : val32 s.mem B (slot w 1) (2 * w) < val32 s.mem B (slot w 0) (2 * w)) :
    WP isa doubleBitMod s fun t =>
      val32 t.mem B (slot w 1) (2 * w) =
        (2 * val32 s.mem B (slot w 1) (2 * w) + (s.gpr .r24 >>> 63).toNat) % val32 s.mem B (slot w 0) (2 * w) ∧
      t.gpr .r24 = s.gpr .r24 <<< 1 ∧
      Mont.Outside B (slot w 1) (24 * (w + 2)) s.mem t.mem ∧
      Keep [.r0, .r3, .r14, .r15, .r16, .r17, .r20, .r24] s t := by
  have hnw := hs.nowrap
  have e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  have e0 := e 0; have e1 := e 1; have e2 := e 2; have e3 := e 3; have e4 := e 4
  unfold doubleBitMod
  have hb : (s.gpr .r24 >>> 63).toNat ≤ 1 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; have := (s.gpr .r24).isLt; omega_arith
  refine WP.seq (WP.mono (doubleBit_ok (n := 2 * w) (dA := slot w 2) (dX := slot w 1) hs h8 h5 h11 (by omega_arith)
    (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)) fun s₂ ⟨hd, a24, out₂, k₂⟩ => ?_)
  have hs₂ := hs.congr k₂.wr
  have m₂ : val32 s₂.mem B (slot w 0) (2 * w) = val32 s.mem B (slot w 0) (2 * w) :=
    out₂.val32 (by omega_arith) (by omega_arith)
  refine WP.seq (WP.mono (subMod_ok (n := 2 * w) (dA := slot w 2) (dT := slot w 3) (dM := slot w 0) hs₂
    (by rw [k₂.gpr .r8 (by decide), h8]) (by rw [k₂.gpr .r9 (by decide), h9])
    (by rw [k₂.gpr .r10 (by decide), h10]) (by rw [k₂.gpr .r11 (by decide), h11])
    (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith))
    fun s₃ ⟨⟨c, hc, hD, h20⟩, out₃, k₃⟩ => ?_)
  rw [m₂] at hD
  have hs₃ := hs₂.congr k₃.wr
  have k23 := k₂.trans k₃
  have accA : val32 s₃.mem B (slot w 2) (2 * w) = val32 s₂.mem B (slot w 2) (2 * w) :=
    out₃.val32 (by omega_arith) (by omega_arith)
  refine WP.mono (selectAcc_ok (n := 2 * w) (dA := slot w 2) (dT := slot w 3) (dO := slot w 1)
    (b := decide (w32 s₂.mem B (slot w 2 + 4 * (2 * w)) < c)) hs₃
    (by rw [k23.gpr .r8 (by decide), h8]) (by rw [k23.gpr .r9 (by decide), h9])
    (by rw [k23.gpr .r5 (by decide), h5]) (by rw [k23.gpr .r11 (by decide), h11])
    (by rw [h20]; simp only [decide_eq_true_eq])
    (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith))
    fun t ⟨hv, out₄, k₄⟩ => ⟨?_, by rw [k₄.gpr .r24 (by decide), k₃.gpr .r24 (by decide)]; exact a24, ?_,
      (k23.trans k₄).mono⟩
  · rw [accA] at hv
    have hM := val32_lt s.mem B (slot w 0) (2 * w)
    rw [val32_succ] at hd
    rw [hv, ← hd, ← Nat.add_zero (w32 s₂.mem B (slot w 2 + 4 * (2 * w))),
      ← Nat.mul_zero (2 ^ 64),
      ← VG.Proof.Bignum.csub_result hM (val32_lt _ _ _ _) hc (val32_lt _ _ _ _) (by rw [Nat.mul_zero, Nat.add_zero]; omega_arith) hD]
    by_cases h : w32 s₂.mem B (slot w 2 + 4 * (2 * w)) < c <;> simp [h]
  · exact ((out₂.mono (by omega_arith) (by omega_arith)).trans (out₃.mono (by omega_arith) (by omega_arith))).trans
      (out₄.mono (by omega_arith) (by omega_arith))

end VG.Proof.Bignum.PPC64LE.ModArith

end

end


/-!
# Modular arithmetic on PPC64LE: reduction

`reduce_ok`: `x mod m` into array 1, for the `L ≥ 1` bytes of `x` at `D`
(`r30`, `r31`), most significant first, apart from the working space; and
`reduce64_ok`, the same by `doubleBitMod64`. Both are `reduceWith_ok`, for
any step that does what `doubleBitMod_ok` says (`DbmOk`).
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.ModArith

open VG VG.PPC64LE VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.PublicChecked
open VG.Impl.Bignum.PPC64LE.ModArith VG.Proof.Bignum.PPC64LE

/-- The registers the reduction writes. -/
def redRegs : List Reg := [.r0, .r3, .r14, .r15, .r16, .r17, .r20, .r24, .r25, .r30, .r31]

/-- Between the bits of the scan from `s`: the arrays' bases in place, and the
accumulator (array 1) is `c mod N`, with only arrays 1–3 changed. -/
def RInv (s : State) (B : Addr) (w N c : Nat) (t : State) : Prop :=
  Keep redRegs s t ∧ Mont.Outside B (slot w 1) (24 * (w + 2)) s.mem t.mem ∧
    val32 t.mem B (slot w 1) (2 * w) = c % N ∧ t.gpr .r5 = off B (slot w 1) ∧ t.gpr .r8 = off B (slot w 2) ∧
    t.gpr .r9 = off B (slot w 3)

/-- What a step of the reduction does: `doubleBitMod_ok`'s statement. -/
def DbmOk (dbm : Prog isa) : Prop :=
  ∀ {s : State} {B : Addr} {Z w : Nat}, Scr s B Z → s.gpr .r8 = off B (slot w 2) → s.gpr .r9 = off B (slot w 3) →
    s.gpr .r10 = off B (slot w 0) → s.gpr .r5 = off B (slot w 1) → s.gpr .r11 = BitVec.ofNat 64 (2 * w) →
    1 ≤ w → w < 2 ^ 31 → slot w 4 ≤ Z →
    val32 s.mem B (slot w 1) (2 * w) < val32 s.mem B (slot w 0) (2 * w) →
    WP isa dbm s fun t =>
      val32 t.mem B (slot w 1) (2 * w) =
        (2 * val32 s.mem B (slot w 1) (2 * w) + (s.gpr .r24 >>> 63).toNat) % val32 s.mem B (slot w 0) (2 * w) ∧
      t.gpr .r24 = s.gpr .r24 <<< 1 ∧
      Mont.Outside B (slot w 1) (24 * (w + 2)) s.mem t.mem ∧
      Keep [.r0, .r3, .r14, .r15, .r16, .r17, .r20, .r24] s t

theorem mod_double_bit (c N b : Nat) : (2 * (c % N) + b) % N = (2 * c + b) % N := by
  rw [Nat.add_mod, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod]

/-- `reduceByteWith`: the eight bits of the byte at `r30` scanned, `c := 256 c + b`. -/
theorem reduceByteWith_ok {dbm : Prog isa} (hd : DbmOk dbm) {s t : State} {B D : Addr} {Z w N c i : Nat} (hs : Scr s B Z) (hw : 1 ≤ w)
    (hw' : w < 2 ^ 31) (hZ : slot w 4 ≤ Z) (h10 : s.gpr .r10 = off B (slot w 0))
    (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w)) (hNd : val32 s.mem B (slot w 0) (2 * w) = N) (hN : 0 < N)
    (ht : RInv s B w N c t) (h30 : t.gpr .r30 = off D i) (hrd : InRegions (t.rd ++ t.wr) (off D i) 1) :
    WP isa (reduceByteWith dbm) t fun t' =>
      RInv s B w N (256 * c + (t.mem (off D i)).toNat) t' ∧ t'.gpr .r30 = off D (i + 1) ∧
        t'.gpr .r31 = t.gpr .r31 := by
  have hnw := hs.nowrap
  have e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  have e0 := e 0; have e1 := e 1; have e4 := e 4
  have hh : hdrBytes = 256 := rfl
  obtain ⟨kt, ot, tv, t5, t8, t9⟩ := ht
  generalize hb : (t.mem (off D i)).toNat = b
  have hb256 : b < 256 := by rw [← hb]; exact (t.mem (off D i)).isLt
  unfold reduceByteWith
  refine WP.seq (WP.mono (WP.keep [.r24, .r30, .r25] (Q := fun t₁ =>
    t₁.gpr .r24 = BitVec.ofNat 64 b <<< 56 ∧ t₁.gpr .r30 = off D (i + 1) ∧ t₁.gpr .r25 = BitVec.ofNat 64 8 ∧
      t₁.mem = t.mem) ?_ (by decide)) fun t₁ ⟨⟨a24, a30, a25, m1⟩, k1⟩ => ?_)
  · prun [h30, exec_lbz' (show Reg.r30 ≠ .r0 by decide) (show 0 < 2 ^ 15 by decide), hrd, read_byte64, hb]
  let Inv : Nat → State → Prop := fun j u =>
    (∃ c', c' * 2 ^ 64 + (u.gpr .r24).toNat = (256 * c + b) * 2 ^ 56 * 2 ^ j ∧ RInv s B w N c' u) ∧
      u.gpr .r30 = off D (i + 1) ∧ u.gpr .r31 = t.gpr .r31
  refine WP.mono (wp_countdown (cnt := .r25) (N := 8) (by decide) (by decide) Inv
    (fun j _ u ⟨⟨c', hc, ku, ou, uv, u5, u8, u9⟩, u30, u31⟩ _ => ?_)
    ⟨⟨c, ?_, kt.trans' k1.mono, by rw [m1]; exact ot, by rw [m1]; exact tv, by rw [k1.gpr .r5 (by decide)]; exact t5,
      by rw [k1.gpr .r8 (by decide)]; exact t8, by rw [k1.gpr .r9 (by decide)]; exact t9⟩, a30,
      k1.gpr .r31 (by decide)⟩ a25)
    fun u ⟨⟨c', hc, hu⟩, u30, u31⟩ => ⟨?_, u30, u31⟩
  · have g : ∀ r ∈ [Reg.r10, .r11], u.gpr r = s.gpr r := fun r hr => ku.gpr r (by revert r; decide)
    refine WP.seq (WP.mono (hd (hs.congr ku.wr) u8 u9 ((g .r10 (by simp)).trans h10) u5
      ((g .r11 (by simp)).trans h11) hw hw' hZ
      (by rw [uv, (ou.val32 (by omega_arith) (by omega_arith)).trans hNd]; exact Nat.mod_lt _ hN))
      fun u₁ ⟨hv, a24', out₁, k'⟩ => ?_)
    refine WP.mono (subi_ok u₁ .r25 (by decide)) fun u₂ e => ?_
    subst e
    have hN₁ : val32 u.mem B (slot w 0) (2 * w) = N := (ou.val32 (by omega_arith) (by omega_arith)).trans hNd
    refine ⟨⟨⟨2 * c' + (u.gpr .r24 >>> 63).toNat, ?_, (ku.trans (k'.trans (Keep.write _ _ _))).mono,
      ou.trans out₁, by rw [mem_write, hv, hN₁, uv, mod_double_bit], ?_, ?_, ?_⟩, ?_, ?_⟩, ?_⟩
    · simp only [gpr_write, reduceCtorEq, ↓reduceIte]
      have e24 : (u.gpr .r24 >>> 63).toNat = if decide (2 ^ 63 ≤ (u.gpr .r24).toNat) then 1 else 0 := by
        rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
        have := (u.gpr .r24).isLt
        split <;> simp_all <;> omega_arith
      rw [a24', Pub.r24_step, e24, show (2 : Nat) ^ (j + 1) = 2 ^ j * 2 from Nat.pow_succ 2 j, ← Nat.mul_assoc]
      have hlt := (u.gpr .r24).isLt
      generalize (u.gpr .r24).toNat = r at hc hlt ⊢
      generalize (256 * c + b) * 2 ^ 56 * 2 ^ j = Y at hc ⊢
      split
      · rename_i hb; simp only [decide_eq_true_eq] at hb
        omega_using [hc, hlt, hb]
      · omega_using [hc, hlt]
    · simp only [gpr_write, reduceCtorEq, ↓reduceIte]; rw [k'.gpr .r5 (by decide)]; exact u5
    · simp only [gpr_write, reduceCtorEq, ↓reduceIte]; rw [k'.gpr .r8 (by decide)]; exact u8
    · simp only [gpr_write, reduceCtorEq, ↓reduceIte]; rw [k'.gpr .r9 (by decide)]; exact u9
    · simp only [gpr_write, reduceCtorEq, ↓reduceIte]; rw [k'.gpr .r30 (by decide)]; exact u30
    · simp only [gpr_write, reduceCtorEq, ↓reduceIte]; rw [k'.gpr .r31 (by decide)]; exact u31
    · simp only [gpr_write, ↓reduceIte]; rw [k'.gpr .r25 (by decide)]
  · rw [a24, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat]
    omega_arith
  · have hc' : c' = 256 * c + b := by
      have := (u.gpr .r24).isLt
      rw [show (256 * c + b) * 2 ^ 56 * 2 ^ 8 = (256 * c + b) * 2 ^ 64 by rw [Nat.mul_assoc]] at hc
      omega_arith
    rw [← hc']; exact hu

/-- `reduceScanWith`: the `L ≥ 1` bytes at `D` (`r30`, `r31`) scanned, most
significant first, apart from the working space. -/
theorem reduceScanWith_ok {dbm : Prog isa} (hd : DbmOk dbm) {s t : State} {B D : Addr} {Z w N L : Nat} (hs : Scr s B Z) (hw : 1 ≤ w)
    (hw' : w < 2 ^ 31) (hZ : slot w 4 ≤ Z) (h10 : s.gpr .r10 = off B (slot w 0))
    (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w)) (hNd : val32 s.mem B (slot w 0) (2 * w) = N) (hN : 0 < N)
    (hL : 1 ≤ L) (hL' : L < 2 ^ 63) (hrd : ∀ i < L, InRegions (s.rd ++ s.wr) (off D i) 1)
    (hsep : ∀ i < L, ∀ x, ofs B x < Z → off D i ≠ x)
    (ht : RInv s B w N 0 t) (h30 : t.gpr .r30 = off D 0) (h31 : t.gpr .r31 = BitVec.ofNat 64 L) :
    WP isa (reduceScanWith dbm) t (RInv s B w N (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem D L))) := by
  have hnw := hs.nowrap
  have e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  have e1 := e 1; have e4 := e 4
  let Inv : Nat → State → Prop := fun i u =>
    RInv s B w N (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem D i)) u ∧ u.gpr .r30 = off D i
  refine WP.mono (wp_countdown (cnt := .r31) (N := L) (by omega_arith) (by omega_arith) Inv
    (fun i hi u ⟨hu, u30⟩ _ => ?_) ⟨ht, h30⟩ h31) fun u h => h.1
  have hb : u.mem (off D i) = s.mem (off D i) := by
    refine hu.2.1 _ (Or.inr ?_)
    by_contra hc
    exact hsep i hi (off D i) (by simp only [Mont.ofs, ofs] at hc ⊢; omega_arith) rfl
  refine WP.seq (WP.mono (reduceByteWith_ok hd hs hw hw' hZ h10 h11 hNd hN hu u30
    (by rw [hu.1.rd, hu.1.wr]; exact hrd i hi)) fun u₁ ⟨hu₁, a30, a31⟩ => ?_)
  refine WP.mono (subi_ok u₁ .r31 (by decide)) fun u₂ e => ?_
  subst e
  obtain ⟨k₁, o₁, v₁, u5, u8, u9⟩ := hu₁
  refine ⟨⟨⟨(k₁.trans (Keep.write _ _ _)).mono, o₁, ?_, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
  · rw [mem_write, v₁, hb, Pub.bytesAt_succ, VG.Proof.Rsa.os2ip_snoc]
  · simp only [gpr_write, reduceCtorEq, ↓reduceIte]; exact u5
  · simp only [gpr_write, reduceCtorEq, ↓reduceIte]; exact u8
  · simp only [gpr_write, reduceCtorEq, ↓reduceIte]; exact u9
  · simp only [gpr_write, reduceCtorEq, ↓reduceIte]; exact a30
  · simp only [gpr_write, ↓reduceIte]; rw [a31]

/-- `reduceWith`: `x mod m` into array 1, for `m` (not zero) in array 0 and
the `L ≥ 1` bytes of `x` at `D` (`r30`, `r31`), most significant first, apart
from the working space; only arrays 1–3 change. -/
theorem reduceWith_ok {dbm : Prog isa} (hd : DbmOk dbm) {s : State} {B D : Addr} {Z w L : Nat} (hs : Scr s B Z) (hw : 1 ≤ w)
    (hw' : w < 2 ^ 31) (hZ : slot w 4 ≤ Z) (h10 : s.gpr .r10 = off B (slot w 0))
    (h29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2))) (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w))
    (hN : 0 < val32 s.mem B (slot w 0) (2 * w))
    (h30 : s.gpr .r30 = off D 0) (h31 : s.gpr .r31 = BitVec.ofNat 64 L) (hL : 1 ≤ L) (hL' : L < 2 ^ 63)
    (hrd : ∀ i < L, InRegions (s.rd ++ s.wr) (off D i) 1)
    (hsep : ∀ i < L, ∀ x, ofs B x < Z → off D i ≠ x) :
    WP isa (reduceWith dbm) s fun t =>
      (val32 t.mem B (slot w 1) (2 * w) =
          Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem D L) % val32 s.mem B (slot w 0) (2 * w) ∧
        Mont.Outside B (slot w 1) (24 * (w + 2)) s.mem t.mem) ∧ Keep (redRegs ++ ([.r5, .r8, .r9] : List Reg)) s t := by
  have hnw := hs.nowrap
  have e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  have e0 := e 0; have e1 := e 1; have e4 := e 4
  have hh : hdrBytes = 256 := rfl
  unfold reduceWith
  refine WP.seq (WP.mono (Pub.base_ok (rd := .r14) (by decide) (by decide) h10 h29 1) fun s₁ ⟨⟨a14, m1⟩, k1⟩ => ?_)
  refine WP.seq (WP.mono (zeroWords_ok (hs.congr k1.wr) a14 ((k1.gpr _ (by decide)).trans h11) hw hw'
    (by omega_arith)) fun s₂ ⟨⟨_, hz, out₂⟩, k₂⟩ => ?_)
  have k12 := k1.trans k₂
  rw [m1] at out₂
  refine WP.seq ?_
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .r5) (by decide) (by decide) ((k12.gpr _ (by decide)).trans h10)
    ((k12.gpr _ (by decide)).trans h29) 1) fun s₃ ⟨⟨a5, m3⟩, k3⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .r8) (by decide) (by decide)
    ((k3.gpr _ (by decide)).trans ((k12.gpr _ (by decide)).trans h10))
    ((k3.gpr _ (by decide)).trans ((k12.gpr _ (by decide)).trans h29)) 2) fun s₄ ⟨⟨a8, m4⟩, k4⟩ => ?_
  have k14 := (k12.trans k3).trans k4
  refine WP.mono (Pub.base_ok (rd := .r9) (by decide) (by decide) ((k14.gpr _ (by decide)).trans h10)
    ((k14.gpr _ (by decide)).trans h29) 3) fun s₅ ⟨⟨a9, m5⟩, k5⟩ => ?_
  have k15 := k14.trans k5
  have m25 : s₅.mem = s₂.mem := m5.trans (m4.trans m3)
  have o25 : Mont.Outside B (slot w 1) (24 * (w + 2)) s.mem s₅.mem := by
    rw [m25]; exact fun x hx => out₂ x (by simp only [Mont.ofs] at hx ⊢; omega_arith)
  have hNd : val32 s₅.mem B (slot w 0) (2 * w) = val32 s.mem B (slot w 0) (2 * w) :=
    o25.val32 (by omega_arith) (by omega_arith)
  have hrd5 : ∀ i < L, InRegions (s₅.rd ++ s₅.wr) (off D i) 1 := by
    rw [k15.rd, k15.wr]; exact hrd
  have hsep5 : ∀ i < L, ∀ x, ofs B x < Z → off D i ≠ x := hsep
  have hz5 : val32 s₅.mem B (slot w 1) (2 * w) = 0 := by
    rw [m25, Pre.val32_eq_wv]
    exact (wv_eq_zero_iff _ _ _ _).mpr hz
  refine WP.mono (reduceScanWith_ok hd (s := s₅) (hs.congr k15.wr) hw hw' hZ ((k5.gpr _ (by decide)).trans
    ((k14.gpr _ (by decide)).trans h10)) ((k15.gpr _ (by decide)).trans h11) hNd hN hL hL' hrd5 hsep5
    ⟨Keep.refl _ _, Mont.Outside.refl _ _ _ _, by rw [hz5, Nat.zero_mod], (k5.gpr _ (by decide)).trans ((k4.gpr _ (by decide)).trans a5),
      (k5.gpr _ (by decide)).trans a8, a9⟩ ((k15.gpr _ (by decide)).trans h30) ((k15.gpr _ (by decide)).trans h31))
    fun t ⟨kt, ot, tv, _, _, _⟩ => ⟨⟨?_, o25.trans ot⟩, (k15.trans kt).mono⟩
  have hbytes : Spec.Rsa.bytesAt s₅.mem D L = Spec.Rsa.bytesAt s.mem D L := by
    refine List.map_congr_left fun i hi => ?_
    have hi := List.mem_range.mp hi
    show s₅.mem (off D i) = s.mem (off D i)
    refine o25 _ (Or.inr ?_)
    by_contra hc
    exact hsep i hi (off D i) (by simp only [Mont.ofs, ofs] at hc ⊢; omega_arith) rfl
  rw [tv, hbytes]

/-- `reduceWith_ok` by `doubleBitMod`. -/
theorem reduce_ok {s : State} {B D : Addr} {Z w L : Nat} (hs : Scr s B Z) (hw : 1 ≤ w)
    (hw' : w < 2 ^ 31) (hZ : slot w 4 ≤ Z) (h10 : s.gpr .r10 = off B (slot w 0))
    (h29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2))) (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w))
    (hN : 0 < val32 s.mem B (slot w 0) (2 * w))
    (h30 : s.gpr .r30 = off D 0) (h31 : s.gpr .r31 = BitVec.ofNat 64 L) (hL : 1 ≤ L) (hL' : L < 2 ^ 63)
    (hrd : ∀ i < L, InRegions (s.rd ++ s.wr) (off D i) 1)
    (hsep : ∀ i < L, ∀ x, ofs B x < Z → off D i ≠ x) :
    WP isa reduce s fun t =>
      (val32 t.mem B (slot w 1) (2 * w) =
          Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem D L) % val32 s.mem B (slot w 0) (2 * w) ∧
        Mont.Outside B (slot w 1) (24 * (w + 2)) s.mem t.mem) ∧ Keep (redRegs ++ ([.r5, .r8, .r9] : List Reg)) s t :=
  reduceWith_ok (fun {_ _ _ _} => doubleBitMod_ok) hs hw hw' hZ h10 h29 h11 hN h30 h31 hL hL' hrd hsep

/-- `reduceWith_ok` by `doubleBitMod64`. -/
theorem reduce64_ok {s : State} {B D : Addr} {Z w L : Nat} (hs : Scr s B Z) (hw : 1 ≤ w)
    (hw' : w < 2 ^ 31) (hZ : slot w 4 ≤ Z) (h10 : s.gpr .r10 = off B (slot w 0))
    (h29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2))) (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w))
    (hN : 0 < val32 s.mem B (slot w 0) (2 * w))
    (h30 : s.gpr .r30 = off D 0) (h31 : s.gpr .r31 = BitVec.ofNat 64 L) (hL : 1 ≤ L) (hL' : L < 2 ^ 63)
    (hrd : ∀ i < L, InRegions (s.rd ++ s.wr) (off D i) 1)
    (hsep : ∀ i < L, ∀ x, ofs B x < Z → off D i ≠ x) :
    WP isa reduce64 s fun t =>
      (val32 t.mem B (slot w 1) (2 * w) =
          Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem D L) % val32 s.mem B (slot w 0) (2 * w) ∧
        Mont.Outside B (slot w 1) (24 * (w + 2)) s.mem t.mem) ∧ Keep (redRegs ++ ([.r5, .r8, .r9] : List Reg)) s t :=
  reduceWith_ok (fun {_ _ _ _} => doubleBitMod64_ok) hs hw hw' hZ h10 h29 h11 hN h30 h31 hL hL' hrd hsep

end VG.Proof.Bignum.PPC64LE.ModArith
