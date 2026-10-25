module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.WinBase
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubPower
import VerifiedGarbage.Proof.Bignum.Math

/-!
# Four-bit windows on PPC64LE: the table

`table_ok`: from `x` in array 4 and `R² mod m` in array 1, table entry `j`
(array `8 + j`) holds `x^j R mod m` for every `j < 16`, `a` (array 6) holds
`T_0 = R mod m` and array 7 holds 1.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Win

open VG VG.PPC64LE VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.ModExp
open VG.Proof.Bignum.PPC64LE
open VG.Impl.Bignum.PPC64LE.PublicChecked (base montOp)

/-- A Montgomery product of powers of `x` in Montgomery form. -/
theorem mont_pow {o a b X i j R N : Nat} (hR : Nat.Coprime R N) (ha : a % N = X ^ i * R % N)
    (hb : b % N = X ^ j * R % N) (h : o * R % N = a * b % N) : o % N = X ^ (i + j) * R % N := by
  refine VG.Proof.Bignum.mont_cancel hR ?_
  rw [h, Nat.mul_mod, ha, hb, ← Nat.mul_mod, Nat.pow_add]
  congr 1
  ac_rfl

/-- The table's entries below `j`, if `R² mod m` is right. -/
def TabUpTo (m : Mem) (B : Addr) (w N X RR j : Nat) : Prop :=
  ∀ i < j, A m B w (8 + i) < N ∧ (RR = 2 ^ (64 * w) * 2 ^ (64 * w) % N →
    A m B w (8 + i) % N = X ^ i * 2 ^ (64 * w) % N)

/-- The registers the table writes. -/
def tabRegs : List Reg := Pub.montRegs ++ copyRegs ++ [.r0, .r14, .r17, .r19, .r24, .r4]

/-- `table`. -/
theorem table_ok {s : State} {B : Addr} {Z w N : Nat} (h : WCtx s B Z w N) (hN : 2 ≤ N) (hodd : N % 2 = 1)
    (hRR : A s.mem B w 1 < N) :
    WP isa table s fun t =>
      (WCtx t B Z w N ∧ Outs B (win w) s.mem t.mem ∧ A t.mem B w 1 = A s.mem B w 1 ∧
        A t.mem B w 4 = A s.mem B w 4 ∧ A t.mem B w 7 = 1 ∧ A t.mem B w 6 = A t.mem B w 8 ∧
        TabUpTo t.mem B w N (A s.mem B w 4) (A s.mem B w 1) 16) ∧ Keep tabRegs s t := by
  have hn := h.nw
  have hR := VG.Proof.Bignum.coprime_pow2 hodd (64 * w)
  generalize hX : A s.mem B w 4 = X
  generalize hRRd : A s.mem B w 1 = RR at hRR
  unfold table
  -- 1 in array 7.
  refine WP.seq (WP.mono (Pub.oneP_ok h.scr (by have := h.w2; omega) h.w31
    (Nat.le_trans (by unfold slot; omega) h.hZ) h.r10 h.r29 h.r11) fun s₁ ⟨⟨h7, out1⟩, k1⟩ => ?_)
  replace h7 : A s₁.mem B w 7 = 1 := h7
  have o1 : Outside B (slot w 7) (8 * (w + 2)) s.mem s₁.mem := out1.mono (Nat.le_refl _) (by omega)
  have c1 := h.of k1 (by decide) (win_of_out o1 (by decide) (by decide))
  have R1 : A s₁.mem B w 1 = RR := by rw [arr_out o1 (by decide) (by decide) hn, hRRd]
  have X1 : A s₁.mem B w 4 = X := by rw [arr_out o1 (by decide) (by decide) hn, hX]
  -- `T_0 = R mod m`.
  refine WP.seq (WP.mono (c1.mont (o := 8) (a := 1) (b := 7) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by rw [h7]; omega)) fun s₂ ⟨⟨c2, lt2, e2, v2, o2⟩, k2⟩ => ?_)
  rw [h7, Nat.mul_one, R1] at e2
  have T0 : RR = 2 ^ (64 * w) * 2 ^ (64 * w) % N → A s₂.mem B w 8 % N = X ^ 0 * 2 ^ (64 * w) % N :=
    fun hE => by
      rw [Nat.pow_zero, Nat.one_mul]
      exact VG.Proof.Bignum.mont_cancel hR (by rw [e2, hE, Nat.mod_mod])
  have R2 : A s₂.mem B w 1 = RR := by rw [v2 1 (by decide) (by decide) (by decide) (by decide), R1]
  have X2 : A s₂.mem B w 4 = X := by rw [v2 4 (by decide) (by decide) (by decide) (by decide), X1]
  have S2 : A s₂.mem B w 7 = 1 := by rw [v2 7 (by decide) (by decide) (by decide) (by decide), h7]
  -- `T_1 = x R mod m`.
  refine WP.seq (WP.mono (c2.mont (o := 9) (a := 4) (b := 1) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by rw [R2]; exact hRR))
    fun s₃ ⟨⟨c3, lt3, e3, v3, o3⟩, k3⟩ => ?_)
  rw [X2, R2] at e3
  have T1 : RR = 2 ^ (64 * w) * 2 ^ (64 * w) % N → A s₃.mem B w 9 % N = X ^ 1 * 2 ^ (64 * w) % N := fun hE => by
    refine VG.Proof.Bignum.mont_cancel hR ?_
    rw [e3, hE, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, Nat.pow_one, Nat.mul_assoc]
  have R3 : A s₃.mem B w 1 = RR := by rw [v3 1 (by decide) (by decide) (by decide) (by decide), R2]
  have X3 : A s₃.mem B w 4 = X := by rw [v3 4 (by decide) (by decide) (by decide) (by decide), X2]
  have S3 : A s₃.mem B w 7 = 1 := by rw [v3 7 (by decide) (by decide) (by decide) (by decide), S2]
  have E3 : A s₃.mem B w 8 = A s₂.mem B w 8 := v3 8 (by decide) (by decide) (by decide) (by decide)
  -- `a := T_1`.
  refine WP.seq (WP.mono (copy_ok c3 (o := 6) (a := 9) (by decide) (by decide) (by decide))
    fun s₄ ⟨⟨a4, o4⟩, k4⟩ => ?_)
  have c4 := c3.of k4 (by decide) (win_of_out o4 (by decide) (by decide))
  refine WP.seq (WP.mono (WP.keep [.r24] (Q := fun t => t.gpr .r24 = BitVec.ofNat 64 2 ∧ t.mem = s₄.mem)
    (by prun) (by decide)) fun s₅ ⟨⟨a24, m5⟩, k5⟩ => ?_)
  have c5 := c4.regs k5 (by decide) m5
  have O5 : Outs B (win w) s.mem s₅.mem := by
    rw [m5]
    exact (((win_of_out o1 (by decide) (by decide)).trans o2).trans o3).trans (win_of_out o4 (by decide) (by decide))
  have K : ∀ j, j < 24 → j ≠ 6 → A s₅.mem B w j = A s₃.mem B w j := fun j hj h6 => by
    rw [m5]; exact arr_out o4 hj h6 hn
  have tab2 : TabUpTo s₅.mem B w N X RR 2 := by
    intro i hi
    rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
    · rw [K 8 (by decide) (by decide), E3]; exact ⟨lt2, T0⟩
    · rw [K 9 (by decide) (by decide)]; exact ⟨lt3, T1⟩
  have a5 : A s₅.mem B w 6 = A s₃.mem B w 9 := by rw [m5, a4]
  -- The loop: entries 2 to 15.
  refine WP.seq (WP.mono (count_loop (n := 14) (cr := .r4) (by decide)
      (fun k t => WCtx t B Z w N ∧ Outs B (win w) s.mem t.mem ∧ t.gpr .r24 = BitVec.ofNat 64 (2 + k) ∧
        A t.mem B w 1 = RR ∧ A t.mem B w 4 = X ∧ A t.mem B w 7 = 1 ∧ A t.mem B w 9 = A s₃.mem B w 9 ∧
        TabUpTo t.mem B w N X RR (2 + k) ∧ A t.mem B w 6 < N ∧
        (RR = 2 ^ (64 * w) * 2 ^ (64 * w) % N → A t.mem B w 6 % N = X ^ (1 + k) * 2 ^ (64 * w) % N) ∧
        Keep tabRegs s t)
      (fun k hk t ⟨ct, ot, t24, t1, t4, t7, t9, ttab, t6l, t6, kt⟩ => ?_)
      ⟨c5, O5, a24, by rw [K 1 (by decide) (by decide), R3], by rw [K 4 (by decide) (by decide), X3],
        by rw [K 7 (by decide) (by decide), S3], K 9 (by decide) (by decide), tab2,
        by rw [a5]; exact lt3, fun hE => by rw [a5]; exact T1 hE,
        ((((k1.trans k2).trans k3).trans k4).trans k5).mono⟩)
    fun t ⟨ct, ot, _, t1, t4, t7, _, ttab, _, _, kt⟩ => ?_)
  · refine WP.seq (WP.mono (ct.mont (o := 6) (a := 6) (b := 9) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by rw [t9]; exact lt3))
      fun u ⟨⟨cu, lu, eu, vu, ou⟩, ku⟩ => ?_)
    have hblk : WP isa (.block [.addi .r19 .r24 0]) u fun v =>
        (v.gpr .r19 = BitVec.ofNat 64 (2 + k) ∧ v.mem = u.mem) ∧ Keep [.r19] u v := by
      refine WP.keep _ ?_ (by decide)
      prun [(ku.gpr .r24 (by decide)).trans t24, BitVec.add_zero]
    refine WP.seq (WP.mono hblk fun v ⟨⟨v19, vm⟩, kv⟩ => ?_)
    have cv := cu.regs kv (by decide) vm
    refine WP.seq (WP.mono (toEntry_ok cv v19 (by omega)) fun x ⟨⟨xe, xo⟩, kx⟩ => ?_)
    have cx := cv.of kx (by decide) (win_of_out xo (by omega) (by omega))
    have hend : WP isa (.block [.addi .r24 .r24 1, .subi .r4 .r24 16]) x fun y =>
        (y.gpr .r24 = BitVec.ofNat 64 (2 + k) + BitVec.ofNat 64 1 ∧
          y.gpr .r4 = BitVec.ofNat 64 (2 + k) + BitVec.ofNat 64 1 - BitVec.ofNat 64 16 ∧ y.mem = x.mem) ∧
          Keep [.r24, .r4] x y := by
      refine WP.keep _ ?_ (by decide)
      prun [(kx.gpr .r24 (by decide)).trans ((kv.gpr .r24 (by decide)).trans ((ku.gpr .r24 (by decide)).trans t24))]
    have M : ∀ j, j < 24 → j ≠ 2 → j ≠ 3 → j ≠ 6 → j ≠ 8 + (2 + k) → A x.mem B w j = A t.mem B w j :=
      fun j hj h2 h3 h6 he => by rw [arr_out xo hj he hn, vm, vu j hj h2 h3 h6]
    have pw : RR = 2 ^ (64 * w) * 2 ^ (64 * w) % N → A u.mem B w 6 % N = X ^ (2 + k) * 2 ^ (64 * w) % N :=
      fun hE => by
        rw [mont_pow hR (t6 hE) (by rw [t9]; exact T1 hE) eu, show 1 + k + 1 = 2 + k by omega]
    refine WP.mono hend fun y ⟨⟨y24, y4, ym⟩, ky⟩ =>
      ⟨⟨cx.regs ky (by decide) ym, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [ym]; exact (ot.trans ou).trans (by rw [← vm]; exact win_of_out xo (by omega) (by omega))
    · rw [y24, ← BitVec.ofNat_add, Nat.add_assoc]
    · rw [ym, M 1 (by decide) (by decide) (by decide) (by decide) (by omega), t1]
    · rw [ym, M 4 (by decide) (by decide) (by decide) (by decide) (by omega), t4]
    · rw [ym, M 7 (by decide) (by decide) (by decide) (by decide) (by omega), t7]
    · rw [ym, M 9 (by decide) (by decide) (by decide) (by decide) (by omega), t9]
    · intro i hi
      rw [ym]
      rcases Nat.lt_succ_iff_lt_or_eq.mp (show i < 2 + k + 1 by omega) with hi | rfl
      · rw [M (8 + i) (by omega) (by omega) (by omega) (by omega) (by omega)]
        exact ttab i hi
      · rw [xe, vm]
        exact ⟨lu, pw⟩
    · rw [ym, arr_out xo (by decide) (by omega) hn, vm]; exact lu
    · intro hE
      rw [ym, arr_out xo (by decide) (by omega) hn, vm, pw hE, show 2 + k = 1 + (k + 1) by omega]
    · exact ((((kt.trans ku).trans kv).trans kx).trans ky).mono
    · rw [y4, ← BitVec.ofNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      omega
  · -- `a := T_0`.
    refine WP.mono (copy_ok ct (o := 6) (a := 8) (by decide) (by decide) (by decide)) fun u ⟨⟨ua, uo⟩, ku⟩ =>
      ⟨⟨ct.of ku (by decide) (win_of_out uo (by decide) (by decide)),
        ot.trans (win_of_out uo (by decide) (by decide)), by rw [arr_out uo (by decide) (by decide) hn, t1],
        by rw [arr_out uo (by decide) (by decide) hn, t4], by rw [arr_out uo (by decide) (by decide) hn, t7],
        by rw [ua, arr_out uo (by decide) (by decide) hn], fun i hi => ?_⟩, (kt.trans ku).mono⟩
    rw [arr_out uo (by omega) (by omega) hn]
    exact ttab i hi

end VG.Proof.Bignum.PPC64LE.Win
