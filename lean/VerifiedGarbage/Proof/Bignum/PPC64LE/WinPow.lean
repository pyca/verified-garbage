module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.WinBase
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubPower
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCheck
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubE
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontRound

/-! ### `Bignum.PPC64LE.WinTable`, which only this module used -/

section

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
  obtain hR := VG.Proof.Bignum.coprime_pow2 hodd (64 * w)
  generalize hX : A s.mem B w 4 = X
  generalize hRRd : A s.mem B w 1 = RR at hRR
  unfold table
  -- 1 in array 7.
  refine WP.seq (WP.mono (Pub.oneP_ok h.scr (by have := h.w2; omega_arith) h.w31
    (Nat.le_trans (by unfold slot; omega_arith) h.hZ) h.r10 h.r29 h.r11) fun s₁ ⟨⟨h7, out1⟩, k1⟩ => ?_)
  replace h7 : A s₁.mem B w 7 = 1 := h7
  obtain o1 : Outside B (slot w 7) (8 * (w + 2)) s.mem s₁.mem := out1.mono (Nat.le_refl _) (by omega_arith)
  obtain c1 := h.of k1 (by decide) (win_of_out o1 (by decide) (by decide))
  obtain R1 : A s₁.mem B w 1 = RR := by rw [arr_out o1 (by decide) (by decide) hn, hRRd]
  obtain X1 : A s₁.mem B w 4 = X := by rw [arr_out o1 (by decide) (by decide) hn, hX]
  -- `T_0 = R mod m`.
  refine WP.seq (WP.mono (c1.mont (o := 8) (a := 1) (b := 7) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by rw [h7]; omega_arith)) fun s₂ ⟨⟨c2, lt2, e2, v2, o2⟩, k2⟩ => ?_)
  rw [h7, Nat.mul_one, R1] at e2
  obtain T0 : RR = 2 ^ (64 * w) * 2 ^ (64 * w) % N → A s₂.mem B w 8 % N = X ^ 0 * 2 ^ (64 * w) % N :=
    fun hE => by
      rw [Nat.pow_zero, Nat.one_mul]
      exact VG.Proof.Bignum.mont_cancel hR (by rw [e2, hE, Nat.mod_mod])
  obtain R2 : A s₂.mem B w 1 = RR := by rw [v2 1 (by decide) (by decide) (by decide) (by decide), R1]
  obtain X2 : A s₂.mem B w 4 = X := by rw [v2 4 (by decide) (by decide) (by decide) (by decide), X1]
  obtain S2 : A s₂.mem B w 7 = 1 := by rw [v2 7 (by decide) (by decide) (by decide) (by decide), h7]
  -- `T_1 = x R mod m`.
  refine WP.seq (WP.mono (c2.mont (o := 9) (a := 4) (b := 1) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by rw [R2]; exact hRR))
    fun s₃ ⟨⟨c3, lt3, e3, v3, o3⟩, k3⟩ => ?_)
  rw [X2, R2] at e3
  obtain T1 : RR = 2 ^ (64 * w) * 2 ^ (64 * w) % N → A s₃.mem B w 9 % N = X ^ 1 * 2 ^ (64 * w) % N := fun hE => by
    refine VG.Proof.Bignum.mont_cancel hR ?_
    rw [e3, hE, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, Nat.pow_one, Nat.mul_assoc]
  obtain R3 : A s₃.mem B w 1 = RR := by rw [v3 1 (by decide) (by decide) (by decide) (by decide), R2]
  obtain X3 : A s₃.mem B w 4 = X := by rw [v3 4 (by decide) (by decide) (by decide) (by decide), X2]
  obtain S3 : A s₃.mem B w 7 = 1 := by rw [v3 7 (by decide) (by decide) (by decide) (by decide), S2]
  obtain E3 : A s₃.mem B w 8 = A s₂.mem B w 8 := v3 8 (by decide) (by decide) (by decide) (by decide)
  -- `a := T_1`.
  refine WP.seq (WP.mono (copy_ok c3 (o := 6) (a := 9) (by decide) (by decide) (by decide))
    fun s₄ ⟨⟨a4, o4⟩, k4⟩ => ?_)
  obtain c4 := c3.of k4 (by decide) (win_of_out o4 (by decide) (by decide))
  refine WP.seq (WP.mono (WP.keep [.r24] (Q := fun t => t.gpr .r24 = BitVec.ofNat 64 2 ∧ t.mem = s₄.mem)
    (by prun) (by decide)) fun s₅ ⟨⟨a24, m5⟩, k5⟩ => ?_)
  obtain c5 := c4.regs k5 (by decide) m5
  obtain O5 : Outs B (win w) s.mem s₅.mem := by
    rw [m5]
    exact (((win_of_out o1 (by decide) (by decide)).trans o2).trans o3).trans (win_of_out o4 (by decide) (by decide))
  obtain K : ∀ j, j < 24 → j ≠ 6 → A s₅.mem B w j = A s₃.mem B w j := fun j hj h6 => by
    rw [m5]; exact arr_out o4 hj h6 hn
  obtain tab2 : TabUpTo s₅.mem B w N X RR 2 := by
    intro i hi
    rcases (show i = 0 ∨ i = 1 by omega_arith) with rfl | rfl
    · rw [K 8 (by decide) (by decide), E3]; exact ⟨lt2, T0⟩
    · rw [K 9 (by decide) (by decide)]; exact ⟨lt3, T1⟩
  obtain a5 : A s₅.mem B w 6 = A s₃.mem B w 9 := by rw [m5, a4]
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
    obtain hblk : WP isa (.block [.addi .r19 .r24 0]) u fun v =>
        (v.gpr .r19 = BitVec.ofNat 64 (2 + k) ∧ v.mem = u.mem) ∧ Keep [.r19] u v := by
      refine WP.keep _ ?_ (by decide)
      prun [(ku.gpr .r24 (by decide)).trans t24, BitVec.add_zero]
    refine WP.seq (WP.mono hblk fun v ⟨⟨v19, vm⟩, kv⟩ => ?_)
    obtain cv := cu.regs kv (by decide) vm
    refine WP.seq (WP.mono (toEntry_ok cv v19 (by omega_arith)) fun x ⟨⟨xe, xo⟩, kx⟩ => ?_)
    obtain cx := cv.of kx (by decide) (win_of_out xo (by omega_arith) (by omega_arith))
    obtain hend : WP isa (.block [.addi .r24 .r24 1, .subi .r4 .r24 16]) x fun y =>
        (y.gpr .r24 = BitVec.ofNat 64 (2 + k) + BitVec.ofNat 64 1 ∧
          y.gpr .r4 = BitVec.ofNat 64 (2 + k) + BitVec.ofNat 64 1 - BitVec.ofNat 64 16 ∧ y.mem = x.mem) ∧
          Keep [.r24, .r4] x y := by
      refine WP.keep _ ?_ (by decide)
      prun [(kx.gpr .r24 (by decide)).trans ((kv.gpr .r24 (by decide)).trans ((ku.gpr .r24 (by decide)).trans t24))]
    obtain M : ∀ j, j < 24 → j ≠ 2 → j ≠ 3 → j ≠ 6 → j ≠ 8 + (2 + k) → A x.mem B w j = A t.mem B w j :=
      fun j hj h2 h3 h6 he => by rw [arr_out xo hj he hn, vm, vu j hj h2 h3 h6]
    obtain pw : RR = 2 ^ (64 * w) * 2 ^ (64 * w) % N → A u.mem B w 6 % N = X ^ (2 + k) * 2 ^ (64 * w) % N :=
      fun hE => by
        rw [mont_pow hR (t6 hE) (by rw [t9]; exact T1 hE) eu, show 1 + k + 1 = 2 + k by omega_arith]
    refine WP.mono hend fun y ⟨⟨y24, y4, ym⟩, ky⟩ =>
      ⟨⟨cx.regs ky (by decide) ym, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [ym]; exact (ot.trans ou).trans (by rw [← vm]; exact win_of_out xo (by omega_arith) (by omega_arith))
    · rw [y24, ← BitVec.ofNat_add, Nat.add_assoc]
    · rw [ym, M 1 (by decide) (by decide) (by decide) (by decide) (by omega_arith), t1]
    · rw [ym, M 4 (by decide) (by decide) (by decide) (by decide) (by omega_arith), t4]
    · rw [ym, M 7 (by decide) (by decide) (by decide) (by decide) (by omega_arith), t7]
    · rw [ym, M 9 (by decide) (by decide) (by decide) (by decide) (by omega_arith), t9]
    · intro i hi
      rw [ym]
      rcases Nat.lt_succ_iff_lt_or_eq.mp (show i < 2 + k + 1 by omega_arith) with hi | rfl
      · rw [M (8 + i) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)]
        exact ttab i hi
      · rw [xe, vm]
        exact ⟨lu, pw⟩
    · rw [ym, arr_out xo (by decide) (by omega_arith) hn, vm]; exact lu
    · intro hE
      rw [ym, arr_out xo (by decide) (by omega_arith) hn, vm, pw hE, show 2 + k = 1 + (k + 1) by omega_arith]
    · exact ((((kt.trans ku).trans kv).trans kx).trans ky).mono
    · rw [y4, ← BitVec.ofNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      omega_arith
  · -- `a := T_0`.
    refine WP.mono (copy_ok ct (o := 6) (a := 8) (by decide) (by decide) (by decide)) fun u ⟨⟨ua, uo⟩, ku⟩ =>
      ⟨⟨ct.of ku (by decide) (win_of_out uo (by decide) (by decide)),
        ot.trans (win_of_out uo (by decide) (by decide)), by rw [arr_out uo (by decide) (by decide) hn, t1],
        by rw [arr_out uo (by decide) (by decide) hn, t4], by rw [arr_out uo (by decide) (by decide) hn, t7],
        by rw [ua, arr_out uo (by decide) (by decide) hn], fun i hi => ?_⟩, (kt.trans ku).mono⟩
    rw [arr_out uo (by omega_arith) (by omega_arith) hn]
    exact ttab i hi

end VG.Proof.Bignum.PPC64LE.Win

end

end

/-! ### `Bignum.PPC64LE.WinSel`, which only this module used -/

section

/-!
# Four-bit windows on PPC64LE: selecting `T_d`

`select_ok`: array 5 := table entry `d` (array `8 + d`), for the digit `d`
in `r18`, by a scan of the whole table, word-major: for each group of up to
four words, each accumulator starts as all ones and takes `&= T_j[c] | m_j`
for every entry `j`, with `m_j = 0` if `j = d` and all ones otherwise
(`accVal_step`), so that it ends as `T_d[c]` and no address depends on `d`.
`selEntry_ok` is an entry, `selGroup_ok` a group, `selGroups_ok` a loop of
groups.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Win

open VG VG.PPC64LE VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.ModExp
open VG.Proof.Bignum.PPC64LE
open VG.Impl.Bignum.PPC64LE.PublicChecked (base montOp)

theorem sub1_sign {x : BitVec 64} (hx : x.toNat < 2 ^ 32) :
    (x - BitVec.ofNat 64 1) >>> 63 = BitVec.ofNat 64 (if x = 0 then 1 else 0) := by
  apply BitVec.eq_of_toNat_eq
  have : x = 0 ↔ x.toNat = 0 := ⟨fun h => by rw [h]; rfl, fun h => BitVec.eq_of_toNat_eq h⟩
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    this]
  split <;> omega_arith

/-- `notDigit`: `r20 :=` 0 if `j = d`, else all ones. -/
theorem notDigit_ok {s : State} {j d : Nat} (h19 : s.gpr .r19 = BitVec.ofNat 64 j)
    (h18 : s.gpr .r18 = BitVec.ofNat 64 d) (hj : j < 16) (hd : d < 16) :
    WP isa (.block notDigit) s fun t =>
      (t.gpr .r20 = (if j = d then 0 else BitVec.allOnes 64) ∧ t.mem = s.mem) ∧ Keep [.r3, .r20] s t := by
  obtain hx : (BitVec.ofNat 64 j ^^^ BitVec.ofNat 64 d).toNat < 2 ^ 32 := by
    rw [BitVec.toNat_xor, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith),
      Nat.mod_eq_of_lt (by omega_arith)]
    exact Nat.xor_lt_two_pow (by omega_arith) (by omega_arith)
  obtain he : (BitVec.ofNat 64 j ^^^ BitVec.ofNat 64 d = 0) ↔ j = d := by
    rw [show (0 : BitVec 64) = 0#64 from rfl, BitVec.xor_eq_zero_iff]
    constructor
    · intro e
      have := congrArg BitVec.toNat e
      rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
        at this
    · rintro rfl; rfl
  refine WP.keep _ ?_ (by decide)
  unfold notDigit
  prun [h19, h18, sub1_sign hx]
  by_cases e : j = d
  · subst e; simp only [BitVec.xor_self, ite_true]; rfl
  · simp only [e, show ¬ (BitVec.ofNat 64 j ^^^ BitVec.ofNat 64 d = 0) from fun h => e (he.mp h), ite_false]; rfl

/-- What accumulator `c` of the group at word `i` holds once the entries
below `j` are gathered: its word of `T_d` if `d < j`, else all ones. -/
abbrev accVal (m : Mem) (B : Addr) (w d i j c : Nat) : BitVec 64 :=
  if d < j then word m B (slot w (8 + d) + 8 * (i + c)) else BitVec.allOnes 64

theorem accVal_step (m : Mem) (B : Addr) (w d i j c : Nat) :
    accVal m B w d i j c &&& (word m B (slot w (8 + j) + 8 * (i + c)) ||| (if j = d then 0 else BitVec.allOnes 64)) =
      accVal m B w d i (j + 1) c := by
  by_cases e : j = d
  · subst e
    simp only [accVal, Nat.lt_irrefl, ite_false, Nat.lt_succ_self, ite_true, BitVec.allOnes_and]
    exact BitVec.or_zero
  · have : (d < j + 1) ↔ d < j := ⟨fun h => by omega_arith, fun h => by omega_arith⟩
    simp only [accVal, e, ite_false, BitVec.or_allOnes, BitVec.and_allOnes, this]

theorem acc_inj : ∀ c < 4, ∀ c' < 4, acc c = acc c' → c = c' := by decide

theorem acc_ne : ∀ c < 4, acc c ≠ .r0 ∧ acc c ≠ .r3 ∧ acc c ≠ .r5 ∧ acc c ≠ .r8 ∧ acc c ≠ .r19 ∧
    acc c ≠ .r20 ∧ acc c ≠ .r4 ∧ acc c ≠ .r9 ∧ acc c ≠ .r18 ∧ acc c ≠ .r10 ∧ acc c ≠ .r11 ∧
    acc c ≠ .r12 ∧ acc c ≠ .r29 := by decide

theorem acc_mem : ∀ c < 4, acc c ∈ [.r14, .r15, .r16, .r17] := by decide

theorem keep_pick {s t : State} {c : Nat} (hc : c < 4) (h : Keep [.r0, acc c] s t) :
    Keep [.r0, .r14, .r15, .r16, .r17] s t :=
  h.mono fun r hr => by
    have := acc_mem c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr this ⊢
    rcases hr with rfl | rfl
    · exact .inl rfl
    · exact .inr this

theorem keep_one {s t : State} {c : Nat} (hc : c < 4) (h : Keep [acc c] s t) : Keep [.r14, .r15, .r16, .r17] s t :=
  h.mono fun r hr => by
    have := acc_mem c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr this
    rw [hr]
    simpa only [List.mem_cons, List.not_mem_nil, or_false] using this

/-- `pick c`: accumulator `c &=` the word at `r8 + 8 c` `| r20`. -/
theorem pick_ok {s : State} {B : Addr} {Z x : Nat} (hs : Scr s B Z) (h8 : s.gpr .r8 = off B x) :
    ∀ c < 4, x + 8 * c + 8 ≤ Z → WP isa (.block (pick c)) s fun t =>
      (t.gpr (acc c) = s.gpr (acc c) &&& (word s.mem B (x + 8 * c) ||| s.gpr .r20) ∧ t.mem = s.mem) ∧
        Keep [.r0, acc c] s t
  | 0, _, hx => WP.keep _ (by unfold pick; prun [h8, hs.ld (d := x) (n := 8) (by omega_arith), show acc 0 = .r14 from rfl]) (by decide)
  | 1, _, hx => WP.keep _ (by unfold pick; prun [h8, hs.ld (d := x + 8) (n := 8) (by omega_arith), show acc 1 = .r15 from rfl]) (by decide)
  | 2, _, hx => WP.keep _ (by unfold pick; prun [h8, hs.ld (d := x + 16) (n := 8) (by omega_arith), show acc 2 = .r16 from rfl]) (by decide)
  | 3, _, hx => WP.keep _ (by unfold pick; prun [h8, hs.ld (d := x + 24) (n := 8) (by omega_arith), show acc 3 = .r17 from rfl]) (by decide)

/-- The picks of the `k ≤ 4` words of a group, the mask `v` in `r20`. -/
theorem picks_ok {s : State} {B : Addr} {Z x : Nat} (hs : Scr s B Z) (h8 : s.gpr .r8 = off B x) :
    ∀ k ≤ 4, x + 8 * k ≤ Z → WP isa (.block ((List.range k).flatMap pick)) s fun t =>
      ((∀ c < 4, t.gpr (acc c) =
        if c < k then s.gpr (acc c) &&& (word s.mem B (x + 8 * c) ||| s.gpr .r20) else s.gpr (acc c)) ∧
        t.mem = s.mem) ∧ Keep [.r0, .r14, .r15, .r16, .r17] s t
  | 0, _, _ => WP.block_nil ⟨⟨fun c _ => by simp, rfl⟩, (Keep.refl [] s).mono (by decide)⟩
  | k + 1, hk, hx => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (picks_ok hs h8 k (by omega_arith) (by omega_arith)) fun t ⟨⟨ta, tm⟩, tk⟩ => ?_
    obtain ht8 : t.gpr .r8 = off B x := (tk.gpr _ (by decide)).trans h8
    refine WP.mono (pick_ok (hs.congr tk.wr) ht8 k (by omega_arith) (by omega_arith))
      fun u ⟨⟨ua, um⟩, uk⟩ =>
        ⟨⟨fun c hc => ?_, um.trans tm⟩, (tk.trans (keep_pick (by omega_arith) uk)).mono (by decide)⟩
    · by_cases e : c = k
      · subst e
        rw [ua, ta c hc, tm, tk.gpr .r20 (by decide)]
        simp
      · have hne : acc c ≠ acc k := fun h => e (acc_inj c hc k (by omega_arith) h)
        rw [uk.gpr _ (by simp [hne, (acc_ne c hc).1]), ta c hc]
        have : (c < k + 1) ↔ c < k := ⟨fun h => by omega_arith, fun h => by omega_arith⟩
        simp only [this]

/-- The registers an entry of `select` writes. -/
def entryRegs : List Reg := [.r0, .r3, .r8, .r14, .r15, .r16, .r17, .r19, .r20]

/-- `selEntry k`: entry `j` gathered into the accumulators of the group of
`k ≤ 4` words at word `i`. -/
theorem selEntry_ok {k : Nat} (hk : k ≤ 4) {s : State} {B : Addr} {Z w N d i j : Nat} (h : WCtx s B Z w N)
    (h18 : s.gpr .r18 = BitVec.ofNat 64 d) (hd : d < 16) (hj : j < 16) (hi : i + k ≤ w)
    (h19 : s.gpr .r19 = BitVec.ofNat 64 j) (h8 : s.gpr .r8 = off B (slot w (8 + j) + 8 * i))
    (ha : ∀ c < k, s.gpr (acc c) = accVal s.mem B w d i j c) :
    WP isa (.block (selEntry k)) s fun t =>
      (t.gpr .r19 = BitVec.ofNat 64 (j + 1) ∧ t.gpr .r8 = off B (slot w (8 + (j + 1)) + 8 * i) ∧
        (∀ c < k, t.gpr (acc c) = accVal s.mem B w d i (j + 1) c) ∧ t.mem = s.mem) ∧ Keep entryRegs s t := by
  obtain hT := h.sl (j := 8 + j) (by omega_arith)
  unfold selEntry
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (notDigit_ok h19 h18 hj hd) fun t ⟨⟨t20, tm⟩, tk⟩ => ?_
  refine WP.mono (picks_ok (h.scr.congr tk.wr) ((tk.gpr _ (by decide)).trans h8) k hk (by omega_arith))
    fun u ⟨⟨ua, um⟩, uk⟩ => ?_
  obtain hu19 : u.gpr .r19 = BitVec.ofNat 64 j := by rw [uk.gpr _ (by decide), tk.gpr _ (by decide), h19]
  obtain hu8 : u.gpr .r8 = off B (slot w (8 + j) + 8 * i) := by rw [uk.gpr _ (by decide), tk.gpr _ (by decide), h8]
  obtain hu29 : u.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2)) := by
    rw [uk.gpr _ (by decide), tk.gpr _ (by decide), h.r29]
  obtain htail : WP isa (.block [.add .r8 .r8 .r29, .addi .r19 .r19 1]) u fun v =>
      (v.gpr .r19 = BitVec.ofNat 64 (j + 1) ∧ v.gpr .r8 = off B (slot w (8 + (j + 1)) + 8 * i) ∧ v.mem = u.mem) ∧
        Keep [.r8, .r19] u v := by
    refine WP.keep _ ?_ (by decide)
    obtain e : slot w (8 + (j + 1)) + 8 * i = slot w (8 + j) + 8 * i + 8 * (w + 2) := by
      unfold slot; rw [show 8 + (j + 1) = (8 + j) + 1 by omega_arith, Nat.succ_mul]; omega_arith
    prun [hu19, hu8, hu29, e, ← BitVec.ofNat_add]
  refine WP.mono htail fun v ⟨⟨v19, v8, vm⟩, vk⟩ => ⟨⟨v19, v8, fun c hc => ?_, by rw [vm, um, tm]⟩, ?_⟩
  · have hc4 : c < 4 := by omega_arith
    rw [vk.gpr _ (by have := acc_ne c hc4; simp [this.2.2.2.1, this.2.2.2.2.1]), ua c hc4]
    simp only [hc, ↓reduceIte]
    rw [tm, tk.gpr _ (by have := acc_ne c hc4; simp [this.2.1, this.2.2.2.2.2.1]), t20, ha c hc, show slot w (8 + j) + 8 * i + 8 * c = slot w (8 + j) + 8 * (i + c) by omega_arith, accVal_step]
  · exact ((tk.trans uk).trans vk).mono

/-- Entries `0` to `n - 1` gathered. -/
theorem selEntries_ok {k : Nat} (hk : k ≤ 4) {s : State} {B : Addr} {Z w N d i : Nat} (h : WCtx s B Z w N)
    (h18 : s.gpr .r18 = BitVec.ofNat 64 d) (hd : d < 16) (hi : i + k ≤ w)
    (h19 : s.gpr .r19 = BitVec.ofNat 64 0) (h8 : s.gpr .r8 = off B (slot w 8 + 8 * i))
    (ha : ∀ c < k, s.gpr (acc c) = BitVec.allOnes 64) :
    ∀ n ≤ 16, WP isa (.block (List.replicate n (selEntry k)).flatten) s fun t =>
      (t.gpr .r19 = BitVec.ofNat 64 n ∧ t.gpr .r8 = off B (slot w (8 + n) + 8 * i) ∧
        (∀ c < k, t.gpr (acc c) = accVal s.mem B w d i n c) ∧ t.mem = s.mem) ∧ Keep entryRegs s t
  | 0, _ => WP.block_nil ⟨⟨h19, h8, fun c hc => by rw [ha c hc]; simp only [accVal, Nat.not_lt_zero, ite_false],
      rfl⟩, (Keep.refl [] s).mono (by decide)⟩
  | n + 1, hn => by
    rw [List.replicate_succ', List.flatten_append, List.flatten_singleton, WP.block_append_iff]
    refine WP.mono (selEntries_ok hk h h18 hd hi h19 h8 ha n (by omega_arith)) fun t ⟨⟨t19, t8, ta, tm⟩, tk⟩ => ?_
    obtain ht := h.regs tk (by decide) tm
    refine WP.mono (selEntry_ok hk ht (by rw [tk.gpr _ (by decide), h18]) hd (by omega_arith) hi t19 t8
      (fun c hc => by rw [ta c hc, tm])) fun u ⟨⟨u19, u8, ua, um⟩, uk⟩ =>
      ⟨⟨u19, u8, fun c hc => by rw [ua c hc, tm], um.trans tm⟩, (tk.trans uk).mono⟩

/-- The accumulators of `k ≤ 4` words := all ones. -/
theorem accInit_ok {s : State} :
    ∀ k ≤ 4, WP isa (.block ((List.range k).flatMap fun c => [.li (acc c) 0, .subi (acc c) (acc c) 1])) s
      fun t => ((∀ c < k, t.gpr (acc c) = BitVec.allOnes 64) ∧ t.mem = s.mem) ∧ Keep [.r14, .r15, .r16, .r17] s t
  | 0, _ => WP.block_nil ⟨⟨fun c hc => absurd hc (Nat.not_lt_zero _), rfl⟩, (Keep.refl [] s).mono (by decide)⟩
  | k + 1, hk => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (accInit_ok k (by omega_arith)) fun t ⟨⟨ta, tm⟩, tk⟩ => ?_
    obtain one : ∀ c < 4, WP isa (.block [.li (acc c) 0, .subi (acc c) (acc c) 1]) t fun u =>
        (u.gpr (acc c) = BitVec.allOnes 64 ∧ u.mem = t.mem) ∧ Keep [acc c] t u := by
      intro c hc
      match c, hc with
      | 0, _ => exact WP.keep _ (by prun [show acc 0 = .r14 from rfl]; rfl) (by decide)
      | 1, _ => exact WP.keep _ (by prun [show acc 1 = .r15 from rfl]; rfl) (by decide)
      | 2, _ => exact WP.keep _ (by prun [show acc 2 = .r16 from rfl]; rfl) (by decide)
      | 3, _ => exact WP.keep _ (by prun [show acc 3 = .r17 from rfl]; rfl) (by decide)
    refine WP.mono (one k (by omega_arith)) fun u ⟨⟨ua, um⟩, uk⟩ =>
      ⟨⟨fun c hc => ?_, um.trans tm⟩, (tk.trans (keep_one (by omega_arith) uk)).mono (by decide)⟩
    · by_cases e : c = k
      · subst e; exact ua
      · rw [uk.gpr _ (by simpa using fun h => e (acc_inj c (by omega_arith) k (by omega_arith) h)),
          ta c (by omega_arith)]

/-- The `k ≤ 4` accumulators stored at `r5`, the offset `x`. -/
theorem accStore_ok {s : State} {B : Addr} {Z x : Nat} (hs : Scr s B Z) (h5 : s.gpr .r5 = off B x) :
    ∀ k ≤ 4, x + 8 * k ≤ Z → WP isa (.block ((List.range k).flatMap fun c => [.store .d (acc c) .r5 (8 * c)])) s
      fun t => ((∀ c < k, word t.mem B (x + 8 * c) = s.gpr (acc c)) ∧ Outside B x (8 * k) s.mem t.mem) ∧
        Keep [] s t
  | 0, _, _ => WP.block_nil ⟨⟨fun c hc => absurd hc (Nat.not_lt_zero _), Outside.refl _ _ _ _⟩, Keep.refl _ _⟩
  | k + 1, hk, hx => by
    have hnw := hs.nowrap
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (accStore_ok hs h5 k (by omega_arith) (by omega_arith)) fun t ⟨⟨ta, to⟩, tk⟩ => ?_
    obtain one : WP isa (.block [.store .d (acc k) .r5 (8 * k)]) t fun u =>
        (u.mem = t.mem.writeW (off B (x + 8 * k)) (t.gpr (acc k))) ∧ Keep [] t u := by
      refine WP.keep _ ?_ (by rfl)
      prun [(tk.gpr _ (by decide)).trans h5, (hs.congr tk.wr).st (show x + 8 * k + 8 ≤ Z by omega_arith),
        show 8 * k < 2 ^ 15 by omega_arith, show 8 * k % 4 = 0 by omega_arith]
    refine WP.mono one fun u ⟨um, uk⟩ => ⟨⟨fun c hc => ?_, ?_⟩, (tk.trans uk).mono⟩
    · rw [um]
      by_cases e : c = k
      · subst e; rw [word_writeW_self, tk.gpr _ (by simp)]
      · rw [(writeW_outside t.mem B (d := x + 8 * k) _ (by omega_arith)).word (by omega_arith) (by omega_arith),
          ta c (by omega_arith)]
    · rw [um]
      exact (to.mono (Nat.le_refl _) (by omega_arith)).trans
        ((writeW_outside _ B (d := x + 8 * k) _ (by omega_arith)).mono (by omega_arith) (by omega_arith))

/-- The registers a group of `select` writes, but its counter. -/
def groupRegs : List Reg := [.r0, .r3, .r5, .r8, .r14, .r15, .r16, .r17, .r19, .r20]

/-- `selGroup k cnt`: the `k ≤ 4` words of array 5 from word `i` := those
of `T_d`, `r5` past them, `cnt -= 1`. -/
theorem selGroup_ok {k : Nat} (hk : k ≤ 4) {cnt : Reg} (hcnt : cnt = .r4 ∨ cnt = .r9) {s : State} {B : Addr}
    {Z w N d i : Nat} (h : WCtx s B Z w N) (h18 : s.gpr .r18 = BitVec.ofNat 64 d) (hd : d < 16) (hi : i + k ≤ w)
    (h5 : s.gpr .r5 = off B (slot w 5 + 8 * i)) :
    WP isa (.block (selGroup k cnt)) s fun t =>
      (t.gpr .r5 = off B (slot w 5 + 8 * (i + k)) ∧ t.gpr cnt = s.gpr cnt - BitVec.ofNat 64 1 ∧
        (∀ c < k, word t.mem B (slot w 5 + 8 * (i + c)) = word s.mem B (slot w (8 + d) + 8 * (i + c))) ∧
        Outside B (slot w 5 + 8 * i) (8 * k) s.mem t.mem) ∧ Keep (cnt :: groupRegs) s t := by
  obtain hO := h.sl (j := 5) (by decide)
  have hnw := h.scr.nowrap
  unfold selGroup
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (accInit_ok (s := s) k hk) fun t ⟨⟨ta, tm⟩, tk⟩ => ?_
  obtain ht := h.regs tk (by decide) tm
  obtain hpre : WP isa (.block [.li .r19 0, .add .r8 .r5 .r29, .add .r8 .r8 .r29, .add .r8 .r8 .r29]) t fun u =>
      (u.gpr .r19 = BitVec.ofNat 64 0 ∧ u.gpr .r8 = off B (slot w 8 + 8 * i) ∧ u.mem = t.mem) ∧
        Keep [.r19, .r8] t u := by
    refine WP.keep _ ?_ (by decide)
    obtain e : slot w 8 + 8 * i = slot w 5 + 8 * i + 8 * (w + 2) + 8 * (w + 2) + 8 * (w + 2) := by
      unfold slot; omega_arith
    prun [(tk.gpr _ (by decide)).trans h5, ht.r29, e, ← BitVec.ofNat_add]
  refine WP.mono hpre fun u ⟨⟨u19, u8, um⟩, uk⟩ => ?_
  obtain hu := ht.regs uk (by decide) um
  refine WP.mono (selEntries_ok hk hu (by rw [uk.gpr _ (by decide), tk.gpr _ (by decide), h18]) hd hi u19 u8
    (fun c hc => by rw [uk.gpr _ (by have := acc_ne c (by omega_arith); simp [this.2.2.2.1, this.2.2.2.2.1]),
      ta c hc]) 16 (Nat.le_refl _)) fun v ⟨⟨_, _, va, vm⟩, vk⟩ => ?_
  obtain hv5 : v.gpr .r5 = off B (slot w 5 + 8 * i) := by
    rw [vk.gpr _ (by decide), uk.gpr _ (by decide), tk.gpr _ (by decide), h5]
  refine WP.mono (accStore_ok (h.scr.congr (vk.wr.trans (uk.wr.trans tk.wr))) hv5 k hk (by omega_arith))
    fun x ⟨⟨xa, xo⟩, xk⟩ => ?_
  obtain htail : WP isa (.block [.addi .r5 .r5 (8 * k), .subi cnt cnt 1]) x fun y =>
      (y.gpr .r5 = off B (slot w 5 + 8 * (i + k)) ∧ y.gpr cnt = x.gpr cnt - BitVec.ofNat 64 1 ∧ y.mem = x.mem) ∧
        Keep [.r5, cnt] x y := by
    obtain h5x : x.gpr .r5 = off B (slot w 5 + 8 * i) := (xk.gpr _ (by decide)).trans hv5
    obtain e : slot w 5 + 8 * (i + k) = slot w 5 + 8 * i + 8 * k := by omega_arith
    rcases hcnt with rfl | rfl
    · exact WP.keep _ (by prun [h5x, e, ← BitVec.ofNat_add, show 8 * k < 2 ^ 15 by omega_arith]) (by rfl)
    · exact WP.keep _ (by prun [h5x, e, ← BitVec.ofNat_add, show 8 * k < 2 ^ 15 by omega_arith]) (by rfl)
  obtain hc : ∀ {r : Reg}, r = .r4 ∨ r = .r9 → x.gpr r = s.gpr r := fun {r} hr => by
    rcases hr with rfl | rfl <;>
      rw [xk.gpr _ (by decide), vk.gpr _ (by decide), uk.gpr _ (by decide), tk.gpr _ (by decide)]
  refine WP.mono htail fun y ⟨⟨y5, yc, ym⟩, yk⟩ => ⟨⟨y5, by rw [yc, hc hcnt], fun c hc' => ?_, ?_⟩, ?_⟩
  · rw [ym, show slot w 5 + 8 * (i + c) = slot w 5 + 8 * i + 8 * c by omega_arith, xa c hc', va c hc']
    simp only [accVal, hd, ↓reduceIte]
    rw [um, tm]
  · rw [ym]; rw [vm, um, tm] at xo; exact xo
  · rcases hcnt with rfl | rfl <;> exact ((((tk.trans uk).trans vk).trans xk).trans yk).mono (by decide)

/-- `selGroups k cnt`: `n` groups (`cnt = n`) of `k ≤ 4` words of array 5
from word `i`, each word := that of `T_d`. -/
theorem selGroups_ok {k : Nat} (hk : k ≤ 4) {cnt : Reg} (hcnt : cnt = .r4 ∨ cnt = .r9) {s : State} {B : Addr}
    {Z w N d i n : Nat} (h : WCtx s B Z w N) (h18 : s.gpr .r18 = BitVec.ofNat 64 d) (hd : d < 16)
    (hi : i + k * n ≤ w) (hnw' : n ≤ w) (h5 : s.gpr .r5 = off B (slot w 5 + 8 * i))
    (hc : s.gpr cnt = BitVec.ofNat 64 n) :
    WP isa (selGroups k cnt) s fun t =>
      (WCtx t B Z w N ∧ t.gpr .r18 = BitVec.ofNat 64 d ∧ t.gpr .r5 = off B (slot w 5 + 8 * (i + k * n)) ∧
        (∀ c < k * n, word t.mem B (slot w 5 + 8 * (i + c)) = word s.mem B (slot w (8 + d) + 8 * (i + c))) ∧
        Outside B (slot w 5 + 8 * i) (8 * (k * n)) s.mem t.mem) ∧ Keep (cnt :: groupRegs) s t := by
  have hw := h.w31
  obtain hO := h.sl (j := 5) (by decide)
  have hnw := h.nw
  have := slot_lt (w := w) (show 5 < 24 by decide)
  have := slot_lt (w := w) (show 8 + d < 24 by omega_arith)
  obtain hn : n < 2 ^ 64 := by omega_arith
  obtain hcr : ∀ {r : Reg}, r = .r4 ∨ r = .r9 → (r ∈ cnt :: groupRegs ↔ r = cnt) := fun {r} hr => by
    rcases hr with rfl | rfl <;> rcases hcnt with rfl | rfl <;> decide
  unfold selGroups
  refine WP.ite _ (eval_zero_ofNat s cnt hn hc) (fun hz => ?_) (fun hz => ?_)
  · have e : n = 0 := of_decide_eq_true hz
    subst e
    exact WP.block_nil ⟨⟨h, h18, by rw [h5, Nat.mul_zero, Nat.add_zero], fun c hc => absurd hc (by simp),
      Outside.refl _ _ _ _⟩, (Keep.refl [] s).mono (by simp)⟩
  obtain hn0 : 0 < n := Nat.pos_of_ne_zero (of_decide_eq_false hz)
  let Inv : Nat → State → Prop := fun g t =>
    WCtx t B Z w N ∧ t.gpr .r18 = BitVec.ofNat 64 d ∧ t.gpr .r5 = off B (slot w 5 + 8 * (i + k * g)) ∧
      (∀ c < k * g, word t.mem B (slot w 5 + 8 * (i + c)) = word s.mem B (slot w (8 + d) + 8 * (i + c))) ∧
      Outside B (slot w 5 + 8 * i) (8 * (k * g)) s.mem t.mem ∧ Keep (cnt :: groupRegs) s t
  refine WP.mono (wp_countdown (body := .block (selGroup k cnt)) (cnt := cnt) (N := n) hn hn0 Inv
    (fun g hg t ⟨et, t18, t5, tw, to, tk⟩ _ => ?_)
    ⟨h, h18, by rw [h5, Nat.mul_zero, Nat.add_zero], fun c hc => absurd hc (by simp), Outside.refl _ _ _ _,
      (Keep.refl [] s).mono (by simp)⟩ hc) fun t ⟨a, b, c, d, e, f⟩ => ⟨⟨a, b, c, d, e⟩, f⟩
  obtain hkg : k * g + k ≤ k * n := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hg
  refine WP.mono (selGroup_ok hk hcnt et t18 hd (i := i + k * g) (by omega_arith) t5)
    fun u ⟨⟨u5, uc, uw, uo⟩, uk⟩ => ⟨⟨?_, ?_, ?_, fun c hc => ?_, ?_, ?_⟩, uc⟩
  -- What changed is in array 5.
  · have := (uo.mono (o' := slot w 5) (n' := 8 * (w + 2)) (by omega_arith) (by omega_arith))
    exact et.of uk (by rcases hcnt with rfl | rfl <;> decide) (win_of_out this (by decide) (by decide))
  · rw [uk.gpr _ (by rcases hcnt with rfl | rfl <;> decide), t18]
  · rw [u5, Nat.mul_succ, Nat.add_assoc]
  · rw [Nat.mul_succ] at hc
    obtain tT : word t.mem B (slot w (8 + d) + 8 * (i + c)) = word s.mem B (slot w (8 + d) + 8 * (i + c)) := by
      have := slot_lt (w := w) (show 5 < 8 + d by omega_arith)
      have := slot_lt (w := w) (show 8 + d < 24 by omega_arith)
      have := h.sl (j := 8 + d) (by omega_arith)
      exact to.word (by omega_arith) (by omega_arith)
    by_cases hlt : c < k * g
    · rw [uo.word (by omega_arith) (by omega_arith), tw c hlt]
    · obtain ⟨c', rfl⟩ : ∃ c', c = k * g + c' := ⟨c - k * g, by omega_arith⟩
      have := uw c' (by omega_arith)
      rw [show i + (k * g + c') = i + k * g + c' by omega_arith, this, ← show i + (k * g + c') = i + k * g + c' by
        omega_arith, tT]
  · rw [Nat.mul_succ, Nat.mul_add]
    exact (to.mono (Nat.le_refl _) (by omega_arith)).trans (uo.mono (by omega_arith) (by omega_arith))
  · rcases hcnt with rfl | rfl <;> exact (tk.trans uk).mono (by decide)

theorem wordsVal_congr {m m' : Mem} {B : Addr} :
    ∀ (n : Nat) {d d' : Nat}, (∀ c < n, Mont.word m' B (d' + 8 * c) = Mont.word m B (d + 8 * c)) →
      wordsVal m' B d' n = wordsVal m B d n
  | 0, _, _, _ => rfl
  | n + 1, d, d', h => by
    simp only [wordsVal]
    rw [show Mont.word m' B d' = Mont.word m B d by simpa using h 0 (by omega_arith),
      wordsVal_congr n (d := d + 8) (d' := d' + 8) fun c hc => by
        simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm 8] using h (c + 1) (by omega_arith)]

theorem ofNat_shr3 {n : Nat} (hn : n < 2 ^ 62) : BitVec.ofNat 64 (2 * n) >>> 3 = BitVec.ofNat 64 (n / 4) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega_arith

theorem ofNat_and3 (n : Nat) :
    BitVec.ofNat 64 (2 * n) >>> 1 &&& BitVec.ofNat 64 3 = BitVec.ofNat 64 (n % 4) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, show (3 : Nat) % 2 ^ 64 = 2 ^ 2 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
  omega_arith

/-- The registers the selection writes. -/
def selectRegs : List Reg := [.r0, .r3, .r4, .r5, .r8, .r9, .r14, .r15, .r16, .r17, .r19, .r20]

/-- `select`: array 5 := `T_d`, for `d` in `r18`; only array 5 changes. -/
theorem select_ok {s : State} {B : Addr} {Z w N d : Nat} (h : WCtx s B Z w N)
    (h18 : s.gpr .r18 = BitVec.ofNat 64 d) (hd : d < 16) :
    WP isa select s fun t =>
      (A t.mem B w 5 = A s.mem B w (8 + d) ∧ (∀ j < 24, j ≠ 3 → j ≠ 5 → A t.mem B w j = A s.mem B w j) ∧ WCtx t B Z w N ∧
        Outs B (win w) s.mem t.mem) ∧ Keep selectRegs s t := by
  have hw := h.w31
  obtain hO := h.sl (j := 5) (by decide)
  have hnw := h.nw
  unfold select
  refine WP.seq ?_
  rw [WP.block_append_iff]
  obtain hpre : WP isa (.block [.lsr .d .r4 .r11 3, .lsr .d .r0 .r11 1, .li .r9 3, .logic .and .r9 .r0 .r9]) s
      fun t => (t.gpr .r4 = BitVec.ofNat 64 (w / 4) ∧ t.gpr .r9 = BitVec.ofNat 64 (w % 4) ∧ t.mem = s.mem) ∧
        Keep [.r4, .r0, .r9] s t := by
    refine WP.keep _ ?_ (by decide)
    prun [h.r11, ofNat_shr3 (show w < 2 ^ 62 by omega_arith), ofNat_and3 w]
  refine WP.mono hpre fun t ⟨⟨t4, t9, tm⟩, tk⟩ => ?_
  obtain ht := h.regs tk (by decide) tm
  refine WP.mono (Pub.base_ok (rd := .r5) (by decide) (by decide) ht.r10 ht.r29 5) fun u ⟨⟨u5, um⟩, uk⟩ => ?_
  obtain hu := ht.regs uk (by decide) um
  obtain hm : u.mem = s.mem := um.trans tm
  refine WP.seq (WP.mono (selGroups_ok (k := 4) (by decide) (.inl rfl) hu (n := w / 4) (i := 0)
    (by rw [uk.gpr _ (by decide), tk.gpr _ (by decide), h18]) hd (by omega_arith) (by omega_arith) (by rw [u5]; rfl)
    (by rw [uk.gpr _ (by decide), t4])) fun v ⟨⟨ev, v18, v5, vw, vo⟩, vk⟩ => ?_)
  refine WP.mono (selGroups_ok (k := 1) (by decide) (.inr rfl) ev (n := w % 4) (i := 4 * (w / 4)) v18 hd
    (by omega_arith) (by omega_arith) (by rw [v5, Nat.zero_add])
    (by rw [vk.gpr _ (by decide), uk.gpr _ (by decide), t9])) fun x ⟨⟨ex, _, _, xw, xo⟩, xk⟩ => ?_
  obtain hw4 : 4 * (w / 4) + 1 * (w % 4) = w := by omega_arith
  -- Only array 5 changed.
  obtain o5 : Outside B (slot w 5) (8 * (w + 2)) s.mem x.mem := by
    rw [← hm]
    exact (vo.mono (Nat.le_refl _) (by omega_arith)).trans (xo.mono (by omega_arith) (by omega_arith))
  refine ⟨⟨?_, fun j hj _ h5 => arr_out o5 hj h5 hnw, ex, win_of_out o5 (by decide) (by decide)⟩, ?_⟩
  · simp only [A, ← wordsVal_eq_val32]
    refine wordsVal_congr w fun c hc => ?_
    have := slot_lt (w := w) (show 5 < 8 + d by omega_arith)
    have := slot_lt (w := w) (show 8 + d < 24 by omega_arith)
    have := h.sl (j := 8 + d) (by omega_arith)
    by_cases hlt : c < 4 * (w / 4)
    · refine (xo.word (by omega_arith) (by omega_arith)).trans ?_
      have := vw c hlt
      simp only [Nat.zero_add, hm] at this
      exact this
    · obtain ⟨c', rfl⟩ : ∃ c', c = 4 * (w / 4) + c' := ⟨c - 4 * (w / 4), by omega_arith⟩
      refine (xw c' (by omega_arith)).trans ((vo.word (by omega_arith) (by omega_arith)).trans ?_)
      rw [hm]
  · exact ((((tk.trans uk).trans vk).trans xk)).mono (by decide)

end VG.Proof.Bignum.PPC64LE.Win

end

end


/-!
# Four-bit windows on PPC64LE: the power

`window_ok`: four squares of `a` (array 6) and a multiplication by `T_d`
for the digit `d` at the top of `r24`, so that `a ≡ x^c R` becomes `a ≡
x^(16 c + d) R`; `byteWin_ok`: the two windows of a byte; `powWin_ok`:
`x^d mod m` into array 4, stated as `ModExpPow.powSecret_ok` but for a
working space of 24 arrays.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Win

open VG VG.PPC64LE VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.ModExp
open VG.Proof.Bignum.PPC64LE
open VG.Impl.Bignum.PPC64LE.PublicChecked (base montOp)

/-- Every array but 2, 3, 5 and 6 keeps its number. -/
def Fix (B : Addr) (w : Nat) (m m' : Mem) : Prop :=
  ∀ j < 24, j ≠ 2 → j ≠ 3 → j ≠ 5 → j ≠ 6 → A m' B w j = A m B w j

theorem Fix.trans {B : Addr} {w : Nat} {m₁ m₂ m₃ : Mem} (a : Fix B w m₁ m₂) (b : Fix B w m₂ m₃) : Fix B w m₁ m₃ :=
  fun j hj h2 h3 h5 h6 => (b j hj h2 h3 h5 h6).trans (a j hj h2 h3 h5 h6)

/-- The registers a window writes. -/
def winRegs : List Reg := Pub.montRegs ++ selectRegs ++ [.r18, .r24]

/-- A square of `a` in the context. -/
theorem sq_ok {s : State} {B : Addr} {Z w N : Nat} (h : WCtx s B Z w N) (hodd : N % 2 = 1)
    (ha : A s.mem B w 6 < N) {X c : Nat} :
    WP isa (montOp 6 6 6) s fun t =>
      (WCtx t B Z w N ∧ Outs B (win w) s.mem t.mem ∧ Fix B w s.mem t.mem ∧ A t.mem B w 6 < N ∧
        (A s.mem B w 6 % N = X ^ c * 2 ^ (64 * w) % N →
          A t.mem B w 6 % N = X ^ (c + c) * 2 ^ (64 * w) % N)) ∧ Keep Pub.montRegs s t := by
  obtain hR := VG.Proof.Bignum.coprime_pow2 hodd (64 * w)
  exact WP.mono (h.mont (o := 6) (a := 6) (b := 6) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) ha) fun t ⟨⟨ct, lt, e, v, o⟩, k⟩ =>
    ⟨⟨ct, o, fun j hj h2 h3 _ h6 => v j hj h2 h3 h6, lt, fun hA => mont_pow hR hA hA e⟩, k⟩

theorem top_nibble (x : BitVec 64) : x >>> 60 = BitVec.ofNat 64 (x.toNat / 2 ^ 60) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
  have := x.isLt
  omega_arith

/-- `window`. -/
theorem window_ok {s : State} {B : Addr} {Z w N : Nat} (h : WCtx s B Z w N) (hodd : N % 2 = 1)
    (ha : A s.mem B w 6 < N) (htab : ∀ i < 16, A s.mem B w (8 + i) < N) {X c : Nat} :
    WP isa window s fun t =>
      (WCtx t B Z w N ∧ Outs B (win w) s.mem t.mem ∧ Fix B w s.mem t.mem ∧ A t.mem B w 6 < N ∧
        t.gpr .r24 = s.gpr .r24 <<< 4 ∧
        (A s.mem B w 6 % N = X ^ c * 2 ^ (64 * w) % N →
          (∀ i < 16, A s.mem B w (8 + i) % N = X ^ i * 2 ^ (64 * w) % N) →
          A t.mem B w 6 % N = X ^ (16 * c + (s.gpr .r24).toNat / 2 ^ 60) * 2 ^ (64 * w) % N)) ∧
        Keep winRegs s t := by
  obtain hR := VG.Proof.Bignum.coprime_pow2 hodd (64 * w)
  unfold window
  refine WP.seq (WP.mono (sq_ok h hodd ha (X := X) (c := c)) fun s₁ ⟨⟨c1, o1, f1, l1, e1⟩, k1⟩ => ?_)
  refine WP.seq (WP.mono (sq_ok c1 hodd l1 (X := X) (c := c + c)) fun s₂ ⟨⟨c2, o2, f2, l2, e2⟩, k2⟩ => ?_)
  refine WP.seq (WP.mono (sq_ok c2 hodd l2 (X := X) (c := c + c + (c + c)))
    fun s₃ ⟨⟨c3, o3, f3, l3, e3⟩, k3⟩ => ?_)
  refine WP.seq (WP.mono (sq_ok c3 hodd l3 (X := X) (c := c + c + (c + c) + (c + c + (c + c))))
    fun s₄ ⟨⟨c4, o4, f4, l4, e4⟩, k4⟩ => ?_)
  obtain k14 := ((k1.trans k2).trans k3).trans k4
  obtain f14 := (f1.trans f2).trans (f3.trans f4)
  obtain hd := (s.gpr .r24).isLt
  obtain hd16 : (s.gpr .r24).toNat / 2 ^ 60 < 16 := by omega_arith
  refine WP.seq (WP.mono (WP.keep [.r18] (Q := fun t =>
      t.gpr .r18 = BitVec.ofNat 64 ((s.gpr .r24).toNat / 2 ^ 60) ∧ t.mem = s₄.mem)
    (by prun [top_nibble, k14.gpr .r24 (by decide)]) (by decide)) fun s₅ ⟨⟨a18, m5⟩, k5⟩ => ?_)
  obtain c5 := c4.regs k5 (by decide) m5
  refine WP.seq (WP.mono (select_ok c5 a18 hd16) fun s₆ ⟨⟨a6, v6, c6, o6⟩, k6⟩ => ?_)
  obtain tab6 : ∀ i < 16, A s₆.mem B w (8 + i) = A s.mem B w (8 + i) := fun i hi => by
    rw [v6 _ (by omega_arith) (by omega_arith) (by omega_arith), m5, f14 _ (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)]
  obtain A6 : A s₆.mem B w 6 = A s₄.mem B w 6 := by rw [v6 6 (by decide) (by decide) (by decide), m5]
  rw [m5, f14 _ (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)] at a6
  refine WP.seq (WP.mono (c6.mont (o := 6) (a := 6) (b := 5) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by rw [a6]; exact htab _ hd16))
    fun s₇ ⟨⟨c7, l7, e7, v7, o7⟩, k7⟩ => ?_)
  refine WP.mono (WP.keep [.r24] (Q := fun t => t.gpr .r24 = s₇.gpr .r24 <<< 4 ∧ t.mem = s₇.mem)
    (by prun) (by decide)) fun t ⟨⟨a24, mt⟩, kt⟩ => ⟨⟨c7.regs kt (by decide) mt, ?_, ?_, by rw [mt]; exact l7, ?_, ?_⟩,
      ?_⟩
  · rw [mt]
    exact ((((o1.trans o2).trans (o3.trans o4)).trans (by rw [← m5]; exact o6)).trans o7)
  · intro j hj h2 h3 h5 h6
    rw [mt, v7 j hj h2 h3 h6, v6 j hj h3 h5, m5]
    exact f14 j hj h2 h3 h5 h6
  · rw [a24, k7.gpr .r24 (by decide), k6.gpr .r24 (by decide), k5.gpr .r24 (by decide), k14.gpr .r24 (by decide)]
  · intro hA hT
    rw [mt, A6] at *
    rw [A6] at e7
    have := mont_pow hR (e4 (e3 (e2 (e1 hA)))) (by rw [a6]; exact hT _ hd16) e7
    rw [this, show c + c + (c + c) + (c + c + (c + c)) + (c + c + (c + c) + (c + c + (c + c))) = 16 * c by omega_arith]
  · exact ((((k14.trans k5).trans k6).trans k7).trans kt).mono

/-! ## The exponent -/

/-- The registers `powWin` writes. -/
def powWRegs : List Reg := tabRegs ++ winRegs ++ [.r30, .r31]

/-- After the table (`t₀`), with `c` of the exponent scanned: what the
windows keep. -/
structure Run (s₀ t₀ u : State) (B : Addr) (Z w N X RR c : Nat) : Prop where
  ctx : WCtx u B Z w N
  out : Outs B (win w) s₀.mem u.mem
  fix : Fix B w t₀.mem u.mem
  lt : A u.mem B w 6 < N
  pw : RR = 2 ^ (64 * w) * 2 ^ (64 * w) % N → A u.mem B w 6 % N = X ^ c * 2 ^ (64 * w) % N
  keep : Keep powWRegs s₀ u

theorem lbz_ok {u : State} {D : Addr} {i : Nat} (h30 : u.gpr .r30 = off D i)
    (hrd : InRegions (u.rd ++ u.wr) (off D i) 1) :
    WP isa (.block [.lbz .r24 .r30 0, .lsl .r24 .r24 56, .addi .r30 .r30 1]) u fun t =>
      (t.gpr .r24 = BitVec.ofNat 64 (u.mem (off D i)).toNat <<< 56 ∧ t.gpr .r30 = off D (i + 1) ∧
        t.mem = u.mem) ∧ Keep [.r24, .r30] u t := by
  refine WP.keep _ ?_ (by decide)
  prun [h30, exec_lbz' (show Reg.r30 ≠ .r0 by decide) (show 0 < 2 ^ 15 by decide), hrd, read_byte64]

theorem nib_hi {b : Nat} (hb : b < 256) : (BitVec.ofNat 64 b <<< 56).toNat / 2 ^ 60 = b / 16 := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat]
  omega_arith

theorem nib_lo (b : Nat) : (BitVec.ofNat 64 b <<< 56 <<< 4).toNat / 2 ^ 60 = b % 16 := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat]
  omega_arith

/-- `byteWin`: the two windows of the byte `b` at `r30`, `c := 256 c + b`. -/
theorem byteWin_ok {s₀ t₀ u : State} {B D : Addr} {Z w N X RR c i : Nat} (hodd : N % 2 = 1)
    (htab : TabUpTo t₀.mem B w N X RR 16) (h : Run s₀ t₀ u B Z w N X RR c) (h30 : u.gpr .r30 = off D i)
    (hrd : InRegions (u.rd ++ u.wr) (off D i) 1) :
    WP isa byteWin u fun t =>
      Run s₀ t₀ t B Z w N X RR (256 * c + (u.mem (off D i)).toNat) ∧ t.gpr .r30 = off D (i + 1) ∧
        t.gpr .r31 = u.gpr .r31 := by
  generalize hb : (u.mem (off D i)).toNat = b
  obtain hb256 : b < 256 := by rw [← hb]; exact (u.mem (off D i)).isLt
  obtain tab : ∀ {m : Mem}, Fix B w t₀.mem m → ∀ i < 16, A m B w (8 + i) < N ∧
      (RR = 2 ^ (64 * w) * 2 ^ (64 * w) % N → A m B w (8 + i) % N = X ^ i * 2 ^ (64 * w) % N) :=
    fun hf i hi => by rw [hf (8 + i) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)]; exact htab i hi
  unfold byteWin
  refine WP.seq (WP.mono (lbz_ok h30 hrd) fun u₁ ⟨⟨a24, a30, m1⟩, k1⟩ => ?_)
  rw [hb] at a24
  obtain c1 := h.ctx.regs k1 (by decide) m1
  obtain f1 : Fix B w t₀.mem u₁.mem := by rw [m1]; exact h.fix
  refine WP.seq (WP.mono (window_ok c1 hodd (by rw [m1]; exact h.lt) (fun i hi => (tab f1 i hi).1)
    (X := X) (c := c)) fun u₂ ⟨⟨c2, o2, f2, l2, a24', e2⟩, k2⟩ => ?_)
  refine WP.mono (window_ok c2 hodd l2 (fun i hi => (tab (f1.trans f2) i hi).1) (X := X) (c := 16 * c + b / 16))
    fun t ⟨⟨c3, o3, f3, l3, _, e3⟩, k3⟩ => ⟨⟨c3, ?_, f1.trans (f2.trans f3), l3, fun hE => ?_, ?_⟩, ?_, ?_⟩
  · rw [m1] at o2; exact (h.out.trans o2).trans o3
  · have p1 := e2 (by rw [m1]; exact h.pw hE) (fun i hi => (tab f1 i hi).2 hE)
    rw [a24, nib_hi hb256] at p1
    obtain p2 := e3 p1 (fun i hi => (tab (f1.trans f2) i hi).2 hE)
    rw [a24', a24, nib_lo b] at p2
    rw [p2, show 16 * (16 * c + b / 16) + b % 16 = 256 * c + b by omega_arith]
  · refine (h.keep.trans (k1.trans (k2.trans k3))).mono fun r hr => ?_
    simp only [List.mem_append] at hr
    rcases hr with h | h | h | h
    · exact h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl <;> decide
    · exact List.mem_append.mpr (.inl (List.mem_append.mpr (.inr h)))
    · exact List.mem_append.mpr (.inl (List.mem_append.mpr (.inr h)))
  · rw [k3.gpr .r30 (by decide), k2.gpr .r30 (by decide), a30]
  · rw [k3.gpr .r31 (by decide), k2.gpr .r31 (by decide), k1.gpr .r31 (by decide)]

/-- `powWin`: `x^d mod m` into array 4, for `x` in array 4, `m` (odd, at least
2) in array 0, something below `m` in array 1 (if `R² mod m`, the result is
right) and the `L ≥ 1` bytes of `d` at `D` (`r30`, `r31`), apart from the
working space of 24 arrays, which is all it writes. -/
theorem powWin_ok {s : State} {B D : Addr} {Z w L : Nat} (hs : Scr s B Z) (hw2 : 2 ≤ w)
    (hw' : w < 2 ^ 31) (hZ : slot w 24 ≤ Z) (h10 : s.gpr .r10 = off B (slot w 0))
    (h29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2))) (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w))
    (h12 : (s.gpr .r12).toNat < 2 ^ 32)
    (hinv : (w32 s.mem B (slot w 0) * (s.gpr .r12).toNat + 1) % 2 ^ 32 = 0)
    (hN : 2 ≤ val32 s.mem B (slot w 0) (2 * w)) (hodd : val32 s.mem B (slot w 0) (2 * w) % 2 = 1)
    (hRRlt : val32 s.mem B (slot w 1) (2 * w) < val32 s.mem B (slot w 0) (2 * w))
    (h30 : s.gpr .r30 = off D 0) (h31 : s.gpr .r31 = BitVec.ofNat 64 L) (hL : 1 ≤ L) (hL' : L < 2 ^ 63)
    (hrd : ∀ i < L, InRegions (s.rd ++ s.wr) (off D i) 1)
    (hsep : ∀ i < L, ∀ x, ofs B x < Z → off D i ≠ x) :
    WP isa powWin s fun t =>
      ((val32 s.mem B (slot w 1) (2 * w) = 2 ^ (64 * w) * 2 ^ (64 * w) % val32 s.mem B (slot w 0) (2 * w) →
          val32 t.mem B (slot w 4) (2 * w) =
            val32 s.mem B (slot w 4) (2 * w) ^ Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem D L) %
              val32 s.mem B (slot w 0) (2 * w)) ∧
        Outs B (win w) s.mem t.mem) ∧ Keep powWRegs s t := by
  obtain h0 : WCtx s B Z w (A s.mem B w 0) := ⟨hs, hw2, hw', hZ, h10, h29, h11, h12, hinv, rfl⟩
  have hn := h0.nw
  generalize hNd : val32 s.mem B (slot w 0) (2 * w) = N at hN hodd hRRlt ⊢
  replace h0 : WCtx s B Z w N := hNd ▸ h0
  obtain hR := VG.Proof.Bignum.coprime_pow2 hodd (64 * w)
  generalize hXd : val32 s.mem B (slot w 4) (2 * w) = X
  generalize hRRd : val32 s.mem B (slot w 1) (2 * w) = RR at hRRlt ⊢
  unfold powWin
  refine WP.seq (WP.mono (table_ok h0 hN hodd (by rw [show A s.mem B w 1 = RR from hRRd]; exact hRRlt)) fun t₀ ⟨⟨c0, o0, _, _, t7, a6, htab⟩, k0⟩ => ?_)
  rw [show A s.mem B w 4 = X from hXd, show A s.mem B w 1 = RR from hRRd] at htab
  obtain r0 : Run s t₀ t₀ B Z w N X RR 0 := ⟨c0, o0, fun _ _ _ _ _ _ => rfl, by rw [a6]; exact (htab 0 (by decide)).1,
    fun hE => by rw [a6]; exact (htab 0 (by decide)).2 hE, k0.mono⟩
  -- The bytes.
  let Inv : Nat → State → Prop := fun i u =>
    Run s t₀ u B Z w N X RR (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem D i)) ∧ u.gpr .r30 = off D i
  refine WP.seq (WP.mono (wp_countdown (cnt := .r31) (N := L) (by omega_arith) (by omega_arith) Inv
    (fun i hi u ⟨hu, u30⟩ _ => ?_) ⟨by simpa [Spec.Rsa.bytesAt, Spec.Rsa.os2ip] using r0,
      by rw [k0.gpr .r30 (by decide), h30]⟩
    (by rw [k0.gpr .r31 (by decide), h31])) fun u ⟨hu, _⟩ => ?_)
  · have hb : u.mem (off D i) = s.mem (off D i) := by
      refine hu.out _ fun r hr => ?_
      rw [win, List.mem_singleton] at hr
      subst hr
      have := slot_lt (w := w) (show 1 < 24 by decide)
      have := hZ
      right
      by_contra hc
      exact hsep i hi (off D i) (by
        obtain e24 : slot w 24 = slot w 1 + 23 * (8 * (w + 2)) := by unfold slot; omega_arith
        simp only [Mont.ofs, ofs] at hc ⊢; omega_arith) rfl
    refine WP.seq (WP.mono (byteWin_ok hodd htab hu u30 (by rw [hu.keep.rd, hu.keep.wr]; exact hrd i hi))
      fun u₁ ⟨hu₁, a30, a31⟩ => ?_)
    refine WP.mono (subi_ok u₁ .r31 (by decide)) fun u₂ e => ?_
    subst e
    refine ⟨⟨⟨hu₁.ctx.regs (Keep.write _ _ _) (by decide) (by rw [mem_write]), by rw [mem_write]; exact hu₁.out,
        by rw [mem_write]; exact hu₁.fix, by rw [mem_write]; exact hu₁.lt, fun hE => ?_,
        (hu₁.keep.trans (Keep.write _ _ _)).mono⟩, by gsimp; exact a30⟩, by gsimp; rw [a31]⟩
    rw [mem_write, hu₁.pw hE, hb, VG.Proof.Bignum.PPC64LE.Pub.bytesAt_succ, VG.Proof.Rsa.os2ip_snoc]
  -- Out of Montgomery form.
  obtain t7' : A u.mem B w 7 = 1 := by rw [hu.fix 7 (by decide) (by decide) (by decide) (by decide) (by decide), t7]
  refine WP.mono (hu.ctx.mont (o := 4) (a := 6) (b := 7) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by rw [t7']; omega_arith)) fun t ⟨⟨_, lt, e, _, o⟩, k⟩ =>
    ⟨⟨fun hE => ?_, hu.out.trans o⟩, (hu.keep.trans k).mono⟩
  rw [t7', Nat.mul_one] at e
  refine (Nat.mod_eq_of_lt lt).symm.trans ?_
  exact VG.Proof.Bignum.mont_cancel hR (by rw [e, hu.pw hE])

end VG.Proof.Bignum.PPC64LE.Win
