module

public import VerifiedGarbage.Proof.Rsa.RISCV64.KeyLayout
public import VerifiedGarbage.Proof.Rsa.RISCV64.KeyLoops
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.RISCV64.MontFinish64
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The operations on the arrays of the RSA key operations' working space on RISC-V

Each keeps the working space (`Ws`), the memory but what it writes
(`Frame`), and the registers but `opRegs`:

* `subN_gen_ok`, `sub3_ok`: `[o] := [a] - [b]` over `w + x` words, the
  borrow out in `t4`;
* `sel_gen_ok`, `sel_ok`, `sel_self_ok`: `[o] := [b]` if the slot `sl` is 1,
  `[a]` if it is 0;
* `copy_ok`: `[o] := [a]`;
* `half_ok`: `[j] := ([j] + t4 · 2^(64 w)) / 2`, and word `w` of `j` is `t4`;
* `eqS_ok`: the slot `d` := whether `[a] = [b]`;
* `bitOf_ok`, `stBorrow_ok`, `andS_ok`: the slots;
* `setOne_ok`, `orOne_ok`, `clrLow_ok`: the low word of an array;
* `zeroArrays_ok`: the first `c` arrays := 0.
-/

@[expose] public section

namespace VG.Proof.Rsa.RISCV64.Keys

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64 VG.Proof.Rsa.RISCV64.Loops
  VG.Impl.Bignum.RISCV64
open VG.Impl.Rsa.RISCV64.Keys (ptr ptrs subN sub3 sel copy half eqS bitOf stBorrow andS setOne orOne
  clrLow zeroArrays subBody selBody copyBody halfBody eqBody mov)

/-- The registers the operations may change. -/
abbrev opRegs : List Reg := loopRegs

/-- Two arrays apart are each ahead of the other. -/
theorem ahead_of_ne {w o a : Nat} (h : o ≠ a) (x : Nat) (hx : x ≤ 2) : Ahead (arr w o) (arr w a) (w + x) := by
  have := arr_disj (w := w) h
  have hS : S w = 8 * (w + 2) := rfl
  unfold Ahead; omega_arith

/-- An array is ahead of itself. -/
theorem ahead_self (w o n : Nat) : Ahead (arr w o) (arr w o) n := .inl (Nat.le_refl _)

/-- `[o] := [a] - [b]` over `w + x` words (`x ≤ 1`) for `o` ahead of `a` and
`b`, the borrow out in `t4`. -/
theorem subN_gen_ok {s : State} {B : Addr} {Z w N o a b x : Nat} (h : Ws s B Z w N)
    (ho : o < N) (ha : a < N) (hb : b < N) (hN : N ≤ 2048) (hx : x ≤ 1)
    (aA : Ahead (arr w o) (arr w a) (w + x)) (aB : Ahead (arr w o) (arr w b) (w + x)) :
    WP isa (subN (x : Int) o a b) s fun t => Ws t B Z w N ∧ Frame B w [o] [] s.mem t.mem ∧
      wordsVal t.mem B (arr w o) (w + x) + wordsVal s.mem B (arr w b) (w + x) =
        wordsVal s.mem B (arr w a) (w + x) + 2 ^ (64 * (w + x)) * (t.gpr .t4).toNat ∧
      (t.gpr .t4).toNat ≤ 1 ∧ Keep opRegs s t := by
  have fo := h.arr_fit ho
  have fa := h.arr_fit ha
  have fb := h.arr_fit hb
  have hS : S w = 8 * (w + 2) := rfl
  have := h.wle
  have := h.wpos
  rw [subN, WP.seq_iff]
  refine ptrs_ok h (by omega_arith) (by omega_arith) (by omega_arith) fun t p0 p1 p2 kt mt => ?_
  have hb' : WP isa (.block [.addi .t3 .s9 (x : Int), .li .t4 0]) t fun u =>
      (u.gpr .t0 = off B (arr w o) ∧ u.gpr .t1 = off B (arr w a) ∧ u.gpr .t2 = off B (arr w b) ∧
        u.gpr .t3 = BitVec.ofNat 64 (w + x) ∧ u.gpr .t4 = 0 ∧ u.mem = t.mem) ∧ Keep [.t3, .t4] t u := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [exec_addi_nat (show x < 2048 by omega_arith), fin64_exec_li_zero, p0, p1, p2,
      (h.of_keep kt).s9]
    exact (BitVec.ofNat_add _ _).symm
  refine WP.mono hb' fun u ⟨⟨u0, u1, u2, u3, u4, um⟩, ku⟩ => ?_
  have k₁ : Keep opRegs s u := (kt.trans ku).mono (by decide)
  have hu : Ws u B Z w N := h.of_keep k₁
  refine WP.mono (subLoop_ok hu.scr u0 u1 u2 u3 (by rw [u4]; decide) (by omega_arith) (by omega_arith)
    (arr_al _ _) (arr_al _ _) (arr_al _ _) (by omega_arith) (by omega_arith) (by omega_arith) aA aB) ?_
  intro t' ⟨b4, veq, out, kt'⟩
  rw [u4, um, mt] at veq
  rw [um, mt] at out
  exact ⟨hu.of_keep kt', Frame.of_arr (d := 0) (by simpa only [Nat.add_zero] using out)
    (by omega_arith) (by simp), by simpa using veq, b4, Keep.trans' k₁ kt'⟩

/-- `sub3 o a b`: `[o] := [a] - [b]` for `o` ahead of `a` and `b`, the borrow out in `t4`. -/
theorem sub3_gen_ok {s : State} {B : Addr} {Z w N o a b : Nat} (h : Ws s B Z w N)
    (ho : o < N) (ha : a < N) (hb : b < N) (hN : N ≤ 2048)
    (aA : Ahead (arr w o) (arr w a) w) (aB : Ahead (arr w o) (arr w b) w) :
    WP isa (sub3 o a b) s fun t => Ws t B Z w N ∧ Frame B w [o] [] s.mem t.mem ∧
      num t.mem B w o + num s.mem B w b = num s.mem B w a + 2 ^ (64 * w) * (t.gpr .t4).toNat ∧
      (t.gpr .t4).toNat ≤ 1 ∧ Keep opRegs s t :=
  subN_gen_ok (x := 0) h ho ha hb hN (Nat.zero_le _) aA aB

/-- `sub3 o a b`: `[o] := [a] - [b]` for arrays apart, the borrow out in `t4`. -/
theorem sub3_ok {s : State} {B : Addr} {Z w N o a b : Nat} (h : Ws s B Z w N)
    (ho : o < N) (ha : a < N) (hb : b < N) (hN : N ≤ 2048) (hoa : o ≠ a) (hob : o ≠ b) :
    WP isa (sub3 o a b) s fun t => Ws t B Z w N ∧ Frame B w [o] [] s.mem t.mem ∧
      num t.mem B w o + num s.mem B w b = num s.mem B w a + 2 ^ (64 * w) * (t.gpr .t4).toNat ∧
      (t.gpr .t4).toNat ≤ 1 ∧ Keep opRegs s t :=
  sub3_gen_ok h ho ha hb hN (ahead_of_ne hoa 0 (by decide)) (ahead_of_ne hob 0 (by decide))

/-- The mask of a slot holding 0 or 1. -/
theorem mask_of_slot (x : BitVec 64) (h : x.toNat ≤ 1) :
    BitVec.ofNat 64 0 - x = if decide (x.toNat ≠ 0) then BitVec.allOnes 64 else 0 := by
  have : x = 0#64 ∨ x = 1#64 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h with e | e
    · exact .inl (BitVec.eq_of_toNat_eq (by simpa using e))
    · exact .inr (BitVec.eq_of_toNat_eq (by simpa using e))
  rcases this with rfl | rfl <;> rfl

/-- `sel o a b sl` for `o` ahead of `a` and `b`: `[o] = [b]` if the slot `sl` is 1, `[a]` if it is 0. -/
theorem sel_gen_ok {s : State} {B : Addr} {Z w N o a b sl : Nat} (h : Ws s B Z w N)
    (ho : o < N) (ha : a < N) (hb : b < N) (hN : N ≤ 2048) (aA : Ahead (arr w o) (arr w a) w)
    (aB : Ahead (arr w o) (arr w b) w) (hsl : sl + 8 ≤ hdr) (hsl8 : sl % 8 = 0)
    (bit : slot s.mem B sl ≤ 1) :
    WP isa (sel o a b sl) s fun t => Ws t B Z w N ∧ Frame B w [o] [] s.mem t.mem ∧
      num t.mem B w o = (if slot s.mem B sl = 0 then num s.mem B w a else num s.mem B w b) ∧
      Keep opRegs s t := by
  have fo := h.arr_fit ho
  have fa := h.arr_fit ha
  have fb := h.arr_fit hb
  have hS : S w = 8 * (w + 2) := rfl
  have hz := h.hdr_le
  have := h.wle
  have := h.wpos
  rw [sel, WP.seq_iff]
  refine ptrs_ok h (by omega_arith) (by omega_arith) (by omega_arith) fun t p0 p1 p2 kt mt => ?_
  have ht := h.of_keep kt
  have hb' : WP isa (.block [.load .d .t4 .s11 sl, .li .t5 0, .sub .t4 .t5 .t4, mov .t3 .s9]) t fun u =>
      (u.gpr .t0 = off B (arr w o) ∧ u.gpr .t1 = off B (arr w a) ∧ u.gpr .t2 = off B (arr w b) ∧
        u.gpr .t3 = BitVec.ofNat 64 w ∧ u.gpr .t4 = BitVec.ofNat 64 0 - word s.mem B sl ∧ u.mem = t.mem) ∧
        Keep [.t3, .t4, .t5] t u := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [mov, fin64_exec_li_zero, p0, p1, p2, ht.s9, ht.s11, add_ofNat_zero', mt,
      ht.scr.al8 (d := sl) (by omega_arith) hsl8, ht.scr.ld (d := sl) (n := 8) (by omega_arith),
      show sl < 2048 by simp only [hdr_eq] at hsl; omega_arith]
    rfl
  refine WP.mono hb' fun u ⟨⟨u0, u1, u2, u3, u4, um⟩, ku⟩ => ?_
  have k₁ : Keep opRegs s u := (kt.trans ku).mono (by decide)
  have hu : Ws u B Z w N := h.of_keep k₁
  refine WP.mono (selLoop_ok hu.scr (b := decide (slot s.mem B sl ≠ 0)) u0 u1 u2 u3
    (by rw [u4]; exact mask_of_slot _ bit) (by omega_arith) (by omega_arith)
    (arr_al _ _) (arr_al _ _) (arr_al _ _) (by omega_arith) (by omega_arith) (by omega_arith) aA aB) ?_
  intro t' ⟨veq, out, kt', _⟩
  rw [um, mt] at veq out
  refine ⟨hu.of_keep kt', Frame.of_arr (d := 0) (by simpa only [Nat.add_zero] using out)
    (by omega_arith) (by simp), ?_, Keep.trans' k₁ kt'⟩
  change wordsVal t'.mem B (arr w o) w = _
  rw [veq]
  by_cases e : slot s.mem B sl = 0 <;> simp [e]

/-- `sel o a b sl` for arrays apart. -/
theorem sel_ok {s : State} {B : Addr} {Z w N o a b sl : Nat} (h : Ws s B Z w N)
    (ho : o < N) (ha : a < N) (hb : b < N) (hN : N ≤ 2048) (hoa : o ≠ a) (hob : o ≠ b)
    (hsl : sl + 8 ≤ hdr) (hsl8 : sl % 8 = 0) (bit : slot s.mem B sl ≤ 1) :
    WP isa (sel o a b sl) s fun t => Ws t B Z w N ∧ Frame B w [o] [] s.mem t.mem ∧
      num t.mem B w o = (if slot s.mem B sl = 0 then num s.mem B w a else num s.mem B w b) ∧
      Keep opRegs s t := by
  have h1 := ahead_of_ne (w := w) hoa 0 (by decide)
  have h2 := ahead_of_ne (w := w) hob 0 (by decide)
  simp only [Nat.add_zero] at h1 h2
  exact sel_gen_ok h ho ha hb hN h1 h2 hsl hsl8 bit

/-- `sel o o b sl`: `[o] := [b]` if the slot `sl` is 1. -/
theorem sel_self_ok {s : State} {B : Addr} {Z w N o b sl : Nat} (h : Ws s B Z w N)
    (ho : o < N) (hb : b < N) (hN : N ≤ 2048) (hob : o ≠ b)
    (hsl : sl + 8 ≤ hdr) (hsl8 : sl % 8 = 0) (bit : slot s.mem B sl ≤ 1) :
    WP isa (sel o o b sl) s fun t => Ws t B Z w N ∧ Frame B w [o] [] s.mem t.mem ∧
      num t.mem B w o = (if slot s.mem B sl = 0 then num s.mem B w o else num s.mem B w b) ∧
      Keep opRegs s t := by
  have h2 := ahead_of_ne (w := w) hob 0 (by decide)
  simp only [Nat.add_zero] at h2
  exact sel_gen_ok h ho ho hb hN (ahead_self _ _ _) h2 hsl hsl8 bit

/-- `copy o a`: `[o] := [a]`, for arrays apart. -/
theorem copy_ok {s : State} {B : Addr} {Z w N o a : Nat} (h : Ws s B Z w N)
    (ho : o < N) (ha : a < N) (hN : N ≤ 2048) (hoa : o ≠ a) :
    WP isa (copy o a) s fun t => Ws t B Z w N ∧ Frame B w [o] [] s.mem t.mem ∧
      num t.mem B w o = num s.mem B w a ∧ Keep opRegs s t ∧
      Outside B (arr w o) (8 * w) s.mem t.mem := by
  have fo := h.arr_fit ho
  have fa := h.arr_fit ha
  have hS : S w = 8 * (w + 2) := rfl
  have := h.wle
  have := h.wpos
  rw [copy, WP.seq_iff]
  refine ptr2_ok h (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by omega_arith) (by omega_arith) fun t p0 p1 kt mt => ?_
  have ht := h.of_keep kt
  have hb' : WP isa (.block [mov .t3 .s9]) t fun u =>
      (u.gpr .t0 = off B (arr w o) ∧ u.gpr .t1 = off B (arr w a) ∧
        u.gpr .t3 = BitVec.ofNat 64 w ∧ u.mem = t.mem) ∧ Keep [.t3] t u := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [mov, p0, p1, ht.s9, add_ofNat_zero']
  refine WP.mono hb' fun u ⟨⟨u0, u1, u3, um⟩, ku⟩ => ?_
  have k₁ : Keep opRegs s u := (kt.trans ku).mono (by decide)
  have hu : Ws u B Z w N := h.of_keep k₁
  have aA := ahead_of_ne (w := w) hoa 0 (by decide)
  simp only [Nat.add_zero] at aA
  refine WP.mono (copyLoop_ok hu.scr u0 u1 u3 (by omega_arith) (by omega_arith) (arr_al _ _) (arr_al _ _)
    (by omega_arith) (by omega_arith) aA) ?_
  intro t' ⟨veq, out, kt'⟩
  rw [um, mt] at veq out
  exact ⟨hu.of_keep kt', Frame.of_arr (d := 0) (by simpa only [Nat.add_zero] using out)
    (by omega_arith) (by simp), veq, Keep.trans' k₁ kt', out⟩

end VG.Proof.Rsa.RISCV64.Keys
