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

/-! ## Words of an array -/

theorem shl3_ofNat (a : Nat) : BitVec.ofNat 64 a <<< 3 = BitVec.ofNat 64 (8 * a) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega_arith

/-- A number with its low word replaced. -/
theorem wordsVal_write0 (m : Mem) (B : Addr) {d k : Nat} (v : BitVec 64) (fit : d + 8 * (k + 1) ≤ 2 ^ 64) :
    wordsVal (m.writeW (off B d) v) B d (k + 1) = v.toNat + 2 ^ 64 * (wordsVal m B d (k + 1) / 2 ^ 64) := by
  have o := writeW_outside m B (d := d) v (by omega_arith)
  rw [wordsVal, wordsVal, word_writeW_self, o.wordsVal (by omega_arith) (by omega_arith)]
  have := (word m B d).isLt
  rw [Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt this, Nat.zero_add]

/-- The low word of a number. -/
theorem wordsVal_mod64 (m : Mem) (B : Addr) {d k : Nat} (hk : 1 ≤ k) :
    wordsVal m B d k % 2 ^ 64 = (word m B d).toNat := by
  obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega_arith⟩
  rw [wordsVal, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (word m B d).isLt]

theorem wordsVal_mod2 (m : Mem) (B : Addr) {d k : Nat} (hk : 1 ≤ k) :
    wordsVal m B d k % 2 = (word m B d).toNat % 2 := by
  rw [← wordsVal_mod64 m B hk, Nat.mod_mod_of_dvd _ (by decide)]

/-- `half j`: `[j] := ([j] + c 2^(64 w)) / 2`, for `c` 0 or 1 in `t4`, which
is also left as word `w` of `j`. -/
theorem half_ok {s : State} {B : Addr} {Z w N j : Nat} (h : Ws s B Z w N)
    (hj : j < N) (hN : N ≤ 2048) (bit : (s.gpr .t4).toNat ≤ 1) :
    WP isa (half j) s fun t => Ws t B Z w N ∧ Frame B w [j] [] s.mem t.mem ∧
      num t.mem B w j = (num s.mem B w j + 2 ^ (64 * w) * (s.gpr .t4).toNat) / 2 ∧
      word t.mem B (arr w j + 8 * w) = s.gpr .t4 ∧ Keep opRegs s t := by
  have fit := h.arr_fit hj
  have nw := h.nowrap
  have hS : S w = 8 * (w + 2) := rfl
  have := h.wpos
  have := h.wle
  rw [half, WP.seq_iff]
  refine ptr_ok h (by decide) (by decide) (show j < 2048 by omega_arith) ?_
  have hb : WP isa (.block [.shift .sll .d .t5 .s9 3, .add .t5 .t0 .t5, .store .d .t4 .t5 0, mov .t3 .s9])
      (s.write .t0 (off B (arr w j))) fun u =>
      (u.gpr .t0 = off B (arr w j) ∧ u.gpr .t3 = BitVec.ofNat 64 w ∧
        u.mem = s.mem.writeW (off B (arr w j + 8 * w)) (s.gpr .t4)) ∧
        Keep [.t3, .t5] (s.write .t0 (off B (arr w j))) u := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [mov, h.s9, shl3_ofNat, add_ofNat_zero',
      h.scr.st (d := arr w j + 8 * w) (n := 8) (by omega_arith),
      h.scr.al8 (d := arr w j + 8 * w) (by omega_arith) (by have := arr_al w j; omega_arith)]
  refine WP.mono hb fun u ⟨⟨u0, u3, um⟩, ku⟩ => ?_
  have k₁ : Keep opRegs s u := ((Keep.write _ _ _).trans ku).mono (by decide)
  have hu : Ws u B Z w N := h.of_keep k₁
  refine WP.mono (halfLoop_ok hu.scr u0 u3 (by omega_arith) (by omega_arith) (arr_al _ _)
    (by omega_arith)) fun t ⟨veq, out, kt⟩ => ?_
  have o1 := writeW_outside s.mem B (d := arr w j + 8 * w) (s.gpr .t4) (by omega_arith)
  have hW : wordsVal u.mem B (arr w j) w = num s.mem B w j := by
    rw [um]; exact o1.wordsVal (by omega_arith) (by omega_arith)
  have hT : word u.mem B (arr w j + 8 * w) = s.gpr .t4 := by rw [um, word_writeW_self]
  have h0 : (word u.mem B (arr w j)).toNat % 2 = num s.mem B w j % 2 := by
    rw [← hW, wordsVal_mod2 _ _ (by omega_arith)]
  rw [hW, hT, h0] at veq
  refine ⟨hu.of_keep kt, ?_, ?_, ?_, Keep.trans' k₁ kt⟩
  · rw [um] at out
    exact (Frame.of_arr (d := 8 * w) o1 (by omega_arith) (by simp)).trans
      (Frame.of_arr (d := 0) (by simpa only [Nat.add_zero] using out) (by omega_arith) (by simp))
  · have e : (num s.mem B w j + 2 ^ (64 * w) * (s.gpr .t4).toNat) % 2 = num s.mem B w j % 2 := by
      obtain ⟨k, rfl⟩ : ∃ k, w = k + 1 := ⟨w - 1, by omega_arith⟩
      rw [show 64 * (k + 1) = 64 * k + 1 + 63 by omega_arith, Nat.pow_add, Nat.pow_add, Nat.pow_one,
        Nat.mul_assoc, Nat.mul_assoc, Nat.mul_comm (2 ^ (64 * k)), Nat.mul_assoc, Nat.add_mul_mod_self_left]
    have hb1 : (s.gpr .t4).toNat % 2 = (s.gpr .t4).toNat := Nat.mod_eq_of_lt (by omega_arith)
    rw [hb1] at veq
    change wordsVal t.mem B (arr w j) w = _
    generalize 2 ^ (64 * w) * (s.gpr .t4).toNat = P at veq e ⊢
    have := Nat.div_add_mod (num s.mem B w j + P) 2
    omega_arith
  · rw [← hT]; exact out.word (by omega_arith) (by omega_arith)

/-- The comparison's flag. -/
theorem eq_flag (x : BitVec 64) :
    ((if (0 : BitVec 64) < x then (1 : BitVec 64) else 0) ^^^ 1).toNat = if x = 0 then 1 else 0 := by
  by_cases h : x = 0
  · subst h; rfl
  · have : (0 : BitVec 64) < x := by
      rw [BitVec.lt_def]; exact Nat.pos_of_ne_zero fun e => h (BitVec.eq_of_toNat_eq (by simpa using e))
    simp only [this, h, ite_true, ite_false]; rfl

/-- `eqS d a b`: the slot `d` := 1 if `[a] = [b]`, else 0. -/
theorem eqS_ok {s : State} {B : Addr} {Z w N d a b : Nat} (h : Ws s B Z w N)
    (ha : a < N) (hb : b < N) (hN : N ≤ 2048) (hd : d + 8 ≤ hdr) (hd8 : d % 8 = 0) :
    WP isa (eqS d a b) s fun u => Ws u B Z w N ∧ Frame B w [] [d] s.mem u.mem ∧
      slot u.mem B d = (if num s.mem B w a = num s.mem B w b then 1 else 0) ∧ Keep opRegs s u := by
  have fa := h.arr_fit ha
  have fb := h.arr_fit hb
  have nw := h.nowrap
  have hS : S w = 8 * (w + 2) := rfl
  have hz := h.hdr_le
  have := h.wpos
  have := h.wle
  rw [eqS, WP.seq_iff]
  refine ptr2_ok h (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by omega_arith) (by omega_arith) fun t p1 p2 kt mt => ?_
  have ht := h.of_keep kt
  have hb' : WP isa (.block [.li .t4 0, mov .t3 .s9]) t fun u =>
      (u.gpr .t1 = off B (arr w a) ∧ u.gpr .t2 = off B (arr w b) ∧ u.gpr .t3 = BitVec.ofNat 64 w ∧
        u.gpr .t4 = 0 ∧ u.mem = t.mem) ∧ Keep [.t3, .t4] t u := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [mov, fin64_exec_li_zero, p1, p2, ht.s9, add_ofNat_zero']
  refine WP.mono hb' fun u ⟨⟨u1, u2, u3, u4, um⟩, ku⟩ => ?_
  have k₁ : Keep opRegs s u := (kt.trans ku).mono (by decide)
  have hu : Ws u B Z w N := h.of_keep k₁
  rw [WP.seq_iff]
  refine WP.mono (eqLoop_ok hu.scr u1 u2 u3 u4 (by omega_arith) (by omega_arith) (arr_al _ _) (arr_al _ _)
    (by omega_arith) (by omega_arith)) fun v ⟨veq, vm, kv⟩ => ?_
  have k₂ : Keep opRegs s v := Keep.trans' k₁ kv
  have hv : Ws v B Z w N := h.of_keep k₂
  have hf : WP isa (.block [.li .t5 0, .sltu .t5 .t5 .t4, .logicImm .xor .t5 .t5 1, .store .d .t5 .s11 d]) v
      fun x => (x.mem = v.mem.writeW (off B d) ((if (0 : BitVec 64) < v.gpr .t4 then (1 : BitVec 64) else 0) ^^^ 1))
        ∧ Keep [.t5] v x := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [fin64_exec_li_zero, hv.s11, hv.scr.al8 (d := d) (by omega_arith) hd8,
      hv.scr.st (d := d) (n := 8) (by omega_arith), show d < 2048 by simp only [hdr_eq] at hd; omega_arith]
    rfl
  refine WP.mono hf fun x ⟨xm, kx⟩ => ⟨hv.of_keep kx, ?_, ?_, Keep.trans' k₂ (kx.mono (by decide))⟩
  · rw [xm, vm, um, mt]
    exact Frame.of_slot (writeW_outside _ B _ (by omega_arith)) (by simp)
  · have veq' : v.gpr .t4 = 0 ↔ num s.mem B w a = num s.mem B w b := by rw [um, mt] at veq; exact veq
    rw [xm]
    change (word (v.mem.writeW (off B d) _) B d).toNat = _
    rw [word_writeW_self, eq_flag]
    by_cases e : num s.mem B w a = num s.mem B w b
    · simp only [e, veq'.mpr e, ite_true]
    · have hne : ¬ v.gpr .t4 = 0 := fun h' => e (veq'.mp h')
      simp only [e, hne, ite_false]

/-! ## Slots and low words -/

theorem and_one_toNat (x : BitVec 64) : (x &&& 1#64).toNat = x.toNat % 2 := by
  rw [BitVec.toNat_and]; simp [Nat.and_one_is_mod]

theorem shr_shl_toNat (x : BitVec 64) : ((x >>> 1) <<< 1).toNat = x.toNat / 2 * 2 := by
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  have := x.isLt
  omega_arith

theorem clr_eq (x : BitVec 64) : x &&& BitVec.ofInt 64 (-2) = (x >>> 1) <<< 1 := by
  apply BitVec.eq_of_getElem_eq; intro i hi
  have : BitVec.ofInt 64 (-2) = ~~~1#64 := by decide
  rw [this]
  simp only [BitVec.getElem_and, BitVec.getElem_not, BitVec.getElem_shiftLeft, BitVec.getElem_ushiftRight]
  by_cases h : i = 0
  · subst h; simp
  · simp [h, show 1 + (i - 1) = i by omega, BitVec.getLsbD_eq_getElem hi]

theorem or_one_eq (x : BitVec 64) : x ||| 1#64 = (x >>> 1) <<< 1 ||| 1#64 := by
  apply BitVec.eq_of_getElem_eq; intro i hi
  simp only [BitVec.getElem_or, BitVec.getElem_shiftLeft, BitVec.getElem_ushiftRight]
  by_cases h : i = 0
  · subst h; simp
  · simp [h, show 1 + (i - 1) = i by omega, BitVec.getLsbD_eq_getElem hi]

theorem or_one_toNat (x : BitVec 64) : (x ||| 1#64).toNat = x.toNat / 2 * 2 + 1 := by
  have hd : (x >>> 1) <<< 1 &&& 1#64 = 0 := by
    apply BitVec.eq_of_getElem_eq; intro i hi
    simp only [BitVec.getElem_and, BitVec.getElem_shiftLeft]
    by_cases h : i = 0
    · subst h; simp
    · simp [h]
  rw [or_one_eq, ← BitVec.add_eq_or_of_and_eq_zero _ _ hd, BitVec.toNat_add, shr_shl_toNat]
  have := x.isLt
  simp only [BitVec.toNat_ofNat]
  omega_arith

theorem clr_toNat (x : BitVec 64) : (x &&& BitVec.ofInt 64 (-2)).toNat = x.toNat / 2 * 2 := by
  rw [clr_eq, shr_shl_toNat]

/-- A slot written, the frame and its value. -/
theorem slot_write {m : Mem} {B : Addr} {w d : Nat} (v : BitVec 64) (hd : d + 8 ≤ 2 ^ 64) :
    Frame B w [] [d] m (m.writeW (off B d) v) ∧ slot (m.writeW (off B d) v) B d = v.toNat :=
  ⟨Frame.of_slot (writeW_outside _ B _ hd) (by simp), by
    change (word (m.writeW (off B d) v) B d).toNat = _; rw [word_writeW_self]⟩

/-- `bitOf sl j`: the slot `sl` := the low bit of `[j]`. -/
theorem bitOf_ok {s : State} {B : Addr} {Z w N j sl : Nat} (h : Ws s B Z w N)
    (hj : j < N) (hN : N ≤ 2048) (hsl : sl + 8 ≤ hdr) (hsl8 : sl % 8 = 0) :
    WP isa (.block (bitOf sl j)) s fun t => Ws t B Z w N ∧ Frame B w [] [sl] s.mem t.mem ∧
      slot t.mem B sl = num s.mem B w j % 2 ∧ Keep opRegs s t := by
  have fit := h.arr_fit hj
  have nw := h.nowrap
  have hS : S w = 8 * (w + 2) := rfl
  have hz := h.hdr_le
  have := h.wpos
  unfold bitOf
  rw [← List.append_nil (ptr .t0 j ++ _), List.append_assoc]
  refine ptr_ok h (by decide) (by decide) (show j < 2048 by omega_arith) ?_
  have hk : WP isa (.block ([.load .d .t5 .t0 0, .logicImm .and .t5 .t5 1, .store .d .t5 .s11 sl] ++ []))
      (s.write .t0 (off B (arr w j))) fun u =>
        (u.mem = s.mem.writeW (off B sl) (word s.mem B (arr w j) &&& 1#64)) ∧
          Keep [.t5] (s.write .t0 (off B (arr w j))) u := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [h.s11, h.scr.ld (d := arr w j) (n := 8) (by omega_arith),
      h.scr.al8 (d := arr w j) (by omega_arith) (arr_al _ _),
      h.scr.st (d := sl) (n := 8) (by omega_arith), h.scr.al8 (d := sl) (by omega_arith) hsl8,
      show sl < 2048 by simp only [hdr_eq] at hsl; omega_arith]
  refine WP.mono hk fun u ⟨mu, ku⟩ => ?_
  have kt : Keep opRegs s u := ((Keep.write _ _ _).trans ku).mono (by decide)
  have sw := slot_write (m := s.mem) (B := B) (w := w) (d := sl) (word s.mem B (arr w j) &&& 1#64) (by omega_arith)
  rw [← mu] at sw
  refine ⟨h.of_keep kt, sw.1, ?_, kt⟩
  rw [sw.2, and_one_toNat, wordsVal_mod2 _ _ (by omega_arith)]

/-- `stBorrow sl`: the slot `sl` := `t4`. -/
theorem stBorrow_ok {s : State} {B : Addr} {Z w N sl : Nat} (h : Ws s B Z w N)
    (hsl : sl + 8 ≤ hdr) (hsl8 : sl % 8 = 0) :
    WP isa (.block (stBorrow sl)) s fun t => Ws t B Z w N ∧ Frame B w [] [sl] s.mem t.mem ∧
      slot t.mem B sl = (s.gpr .t4).toNat ∧ Keep [] s t := by
  have nw := h.nowrap
  have hz := h.hdr_le
  have hk : WP isa (.block (stBorrow sl)) s fun u => (u.mem = s.mem.writeW (off B sl) (s.gpr .t4)) ∧ Keep [] s u := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [stBorrow, h.s11, h.scr.st (d := sl) (n := 8) (by omega_arith), h.scr.al8 (d := sl) (by omega_arith) hsl8,
      show sl < 2048 by simp only [hdr_eq] at hsl; omega_arith]
  refine WP.mono hk fun u ⟨mu, ku⟩ => ?_
  have sw := slot_write (m := s.mem) (B := B) (w := w) (d := sl) (s.gpr .t4) (by omega_arith)
  rw [← mu] at sw
  exact ⟨h.of_keep ku, sw.1, sw.2, ku⟩

theorem and01 {x y : BitVec 64} (hx : x.toNat ≤ 1) (hy : y.toNat ≤ 1) : (x &&& y).toNat = x.toNat * y.toNat := by
  rw [BitVec.toNat_and]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hx with e | e <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hy with f | f <;> simp [e, f]

/-- `andS d a b`: the slot `d` := the slots `a` and `b` and'ed (each 0 or 1). -/
theorem andS_ok {s : State} {B : Addr} {Z w N d a b : Nat} (h : Ws s B Z w N)
    (hd : d + 8 ≤ hdr) (hd8 : d % 8 = 0) (ha : a + 8 ≤ hdr) (ha8 : a % 8 = 0) (hb : b + 8 ≤ hdr)
    (hb8 : b % 8 = 0) (ba : slot s.mem B a ≤ 1) (bb : slot s.mem B b ≤ 1) :
    WP isa (.block (andS d a b)) s fun t => Ws t B Z w N ∧ Frame B w [] [d] s.mem t.mem ∧
      slot t.mem B d = slot s.mem B a * slot s.mem B b ∧ Keep opRegs s t := by
  have nw := h.nowrap
  have hz := h.hdr_le
  have hk : WP isa (.block (andS d a b)) s fun u =>
      (u.mem = s.mem.writeW (off B d) (word s.mem B a &&& word s.mem B b)) ∧ Keep [.t5, .t6] s u := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [andS, h.s11, h.scr.st (d := d) (n := 8) (by omega_arith), h.scr.al8 (d := d) (by omega_arith) hd8,
      h.scr.ld (d := a) (n := 8) (by omega_arith), h.scr.al8 (d := a) (by omega_arith) ha8,
      h.scr.ld (d := b) (n := 8) (by omega_arith), h.scr.al8 (d := b) (by omega_arith) hb8,
      show d < 2048 by simp only [hdr_eq] at hd; omega_arith, show a < 2048 by simp only [hdr_eq] at ha; omega_arith,
      show b < 2048 by simp only [hdr_eq] at hb; omega_arith]
  refine WP.mono hk fun u ⟨mu, ku⟩ => ?_
  have sw := slot_write (m := s.mem) (B := B) (w := w) (d := d) (word s.mem B a &&& word s.mem B b) (by omega_arith)
  rw [← mu] at sw
  exact ⟨h.of_keep ku, sw.1, by rw [sw.2]; exact and01 ba bb, ku.mono (by decide)⟩

/-- An array's low word written: the frame and its number. -/
theorem low_write {m : Mem} {B : Addr} {w j : Nat} (hw : 0 < w) (fit : arr w j + S w ≤ 2 ^ 64) (v : BitVec 64) :
    Frame B w [j] [] m (m.writeW (off B (arr w j)) v) ∧
      num (m.writeW (off B (arr w j)) v) B w j = v.toNat + 2 ^ 64 * (num m B w j / 2 ^ 64) := by
  have hS : S w = 8 * (w + 2) := rfl
  refine ⟨Frame.of_arr (d := 0) (by simpa using writeW_outside m B (d := arr w j) v (by omega_arith))
    (by omega_arith) (by simp), ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, w = k + 1 := ⟨w - 1, by omega_arith⟩
  exact wordsVal_write0 m B v (by omega_arith)

/-- A low word's change, run after `ptr .t0 j`. -/
theorem low_ok {s : State} {B : Addr} {Z w N j : Nat} (h : Ws s B Z w N) (hj : j < N) (hN : N ≤ 2048)
    {body : List Instr} {f : BitVec 64 → BitVec 64}
    (hk : ∀ s₀, s₀.gpr .t0 = off B (arr w j) → s₀.mem = s.mem → s₀.wr = s.wr → s₀.rd = s.rd →
      WP isa (.block body) s₀ fun u =>
        (u.mem = s.mem.writeW (off B (arr w j)) (f (word s.mem B (arr w j)))) ∧ Keep [.t5] s₀ u) :
    WP isa (.block (ptr .t0 j ++ body)) s fun t => Ws t B Z w N ∧ Frame B w [j] [] s.mem t.mem ∧
      num t.mem B w j = (f (word s.mem B (arr w j))).toNat + 2 ^ 64 * (num s.mem B w j / 2 ^ 64) ∧
      Keep opRegs s t := by
  have fit := h.fit64 hj
  refine ptr_ok h (by decide) (by decide) (show j < 2048 by have := h.fits; omega_arith) ?_
  refine WP.mono (hk _ (by simp [gpr_write]) rfl rfl rfl) fun u ⟨mu, ku⟩ => ?_
  have kt : Keep opRegs s u := ((Keep.write _ _ _).trans ku).mono (by decide)
  have lw := low_write (m := s.mem) (B := B) h.wpos fit (f (word s.mem B (arr w j)))
  rw [← mu] at lw
  exact ⟨h.of_keep kt, lw.1, lw.2, kt⟩

theorem keys_exec_li_one {s : State} {d : Reg} : exec (.li d 1) s = some (s.write d 1#64) := by
  rw [exec_li (by decide)]; rfl

/-- `setOne j`: the low word of `[j]` := 1. -/
theorem setOne_ok {s : State} {B : Addr} {Z w N j : Nat} (h : Ws s B Z w N) (hj : j < N) (hN : N ≤ 2048) :
    WP isa (.block (setOne j)) s fun t => Ws t B Z w N ∧ Frame B w [j] [] s.mem t.mem ∧
      num t.mem B w j = 1 + 2 ^ 64 * (num s.mem B w j / 2 ^ 64) ∧ Keep opRegs s t := by
  have fit := h.arr_fit hj
  have nw := h.nowrap
  have hS : S w = 8 * (w + 2) := rfl
  refine WP.mono (low_ok h hj hN (f := fun _ => 1#64) fun s₀ e0 em ew er => ?_) fun t ⟨a, b, c, d⟩ => ⟨a, b, c, d⟩
  refine WP.keep _ ?_ (by rfl) (by rfl)
  brun [e0, em, keys_exec_li_one, (h.scr.congr ew).st (d := arr w j) (n := 8) (by omega_arith),
    (h.scr.congr ew).al8 (d := arr w j) (by omega_arith) (arr_al _ _)]

/-- `orOne j`: the low bit of `[j]` set. -/
theorem orOne_ok {s : State} {B : Addr} {Z w N j : Nat} (h : Ws s B Z w N) (hj : j < N) (hN : N ≤ 2048) :
    WP isa (.block (orOne j)) s fun t => Ws t B Z w N ∧ Frame B w [j] [] s.mem t.mem ∧
      num t.mem B w j = num s.mem B w j / 2 * 2 + 1 ∧ Keep opRegs s t := by
  have fit := h.arr_fit hj
  have nw := h.nowrap
  have hS : S w = 8 * (w + 2) := rfl
  refine WP.mono (low_ok h hj hN (f := fun x => x ||| 1#64) fun s₀ e0 em ew er => ?_) fun t ⟨a, b, c, d⟩ =>
    ⟨a, b, ?_, d⟩
  · refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [e0, em, (h.scr.congr ew).st (d := arr w j) (n := 8) (by omega_arith),
      (h.scr.congr ew).al8 (d := arr w j) (by omega_arith) (arr_al _ _),
      (h.scr.congr ew).ld (d := arr w j) (n := 8) (by omega_arith)]
  · rw [c, or_one_toNat]
    have e := wordsVal_mod64 s.mem B (d := arr w j) (k := w) h.wpos
    change num s.mem B w j % 2 ^ 64 = _ at e
    rw [← e]
    have := Nat.div_add_mod (num s.mem B w j) (2 ^ 64)
    omega_arith

/-- `clrLow j`: the low bit of `[j]` cleared. -/
theorem clrLow_ok {s : State} {B : Addr} {Z w N j : Nat} (h : Ws s B Z w N) (hj : j < N) (hN : N ≤ 2048) :
    WP isa (.block (clrLow j)) s fun t => Ws t B Z w N ∧ Frame B w [j] [] s.mem t.mem ∧
      num t.mem B w j = num s.mem B w j / 2 * 2 ∧ Keep opRegs s t := by
  have fit := h.arr_fit hj
  have nw := h.nowrap
  have hS : S w = 8 * (w + 2) := rfl
  refine WP.mono (low_ok h hj hN (f := fun x => x &&& BitVec.ofInt 64 (-2)) fun s₀ e0 em ew er => ?_)
    fun t ⟨a, b, c, d⟩ => ⟨a, b, ?_, d⟩
  · refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [e0, em, (h.scr.congr ew).st (d := arr w j) (n := 8) (by omega_arith),
      (h.scr.congr ew).al8 (d := arr w j) (by omega_arith) (arr_al _ _),
      (h.scr.congr ew).ld (d := arr w j) (n := 8) (by omega_arith)]
  · rw [c, clr_toNat]
    have e := wordsVal_mod64 s.mem B (d := arr w j) (k := w) h.wpos
    change num s.mem B w j % 2 ^ 64 = _ at e
    rw [← e]
    have := Nat.div_add_mod (num s.mem B w j) (2 ^ 64)
    omega_arith

/-! ## Zeroing the arrays -/

theorem wordsVal_append (m : Mem) (B : Addr) (d a b : Nat) :
    wordsVal m B d (a + b) = wordsVal m B d a + 2 ^ (64 * a) * wordsVal m B (d + 8 * a) b := by
  induction a generalizing d with
  | zero => simp [wordsVal]
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 by omega_arith, wordsVal, wordsVal, ih (d + 8),
      show d + 8 + 8 * a = d + 8 * (a + 1) by omega_arith, pow64_succ, Nat.mul_add, Nat.mul_assoc]
    omega_arith

/-- The words of a part of a number that is zero. -/
theorem wordsVal_zero_part {m : Mem} {B : Addr} {d K : Nat} (h : wordsVal m B d K = 0) {a c : Nat}
    (hac : a + c ≤ K) : wordsVal m B (d + 8 * a) c = 0 := by
  have e1 := wordsVal_append m B d a (K - a)
  rw [show a + (K - a) = K by omega_arith, h] at e1
  have p := Nat.two_pow_pos (64 * a)
  have z : wordsVal m B (d + 8 * a) (K - a) = 0 := by
    rcases Nat.eq_zero_or_pos (wordsVal m B (d + 8 * a) (K - a)) with e | e
    · exact e
    · have : 0 < 2 ^ (64 * a) * wordsVal m B (d + 8 * a) (K - a) := Nat.mul_pos p e
      omega_arith
  have e2 := wordsVal_append m B (d + 8 * a) c (K - a - c)
  rw [show c + (K - a - c) = K - a by omega_arith, z] at e2
  omega_arith

theorem zc_ofNat (c w : Nat) (hc : c < 2048) (hw : w ≤ 1024) :
    (BitVec.ofNat 64 c * BitVec.ofNat 64 (S w)) >>> 3 = BitVec.ofNat 64 (c * (w + 2)) := by
  rw [← BitVec.ofNat_mul]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  have : c * (w + 2) ≤ 2047 * 1026 := Nat.mul_le_mul (by omega_arith) (by omega_arith)
  rw [show c * S w = 8 * (c * (w + 2)) by simp only [S]; rw [Nat.mul_left_comm],
    Nat.mod_eq_of_lt (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
  omega_arith

/-- Memory changed only on the first `c` arrays. -/
theorem Frame.of_range {B : Addr} {w c : Nat} {m m' : Mem} (h : Outside B hdr (8 * (c * (w + 2))) m m') :
    Frame B w (List.range c) [] m m' := by
  intro x hx
  refine h x ?_
  by_contra hc
  have hS : S w = 8 * (w + 2) := rfl
  have hlo : hdr ≤ ofs B x := by omega_arith
  have hhi : ofs B x < hdr + 8 * (c * (w + 2)) := by omega_arith
  have hj : (ofs B x - hdr) / S w < c := by
    rw [Nat.div_lt_iff_lt_mul (by omega_arith)]; rw [hS, Nat.mul_comm c, Nat.mul_assoc] at *; omega_arith
  have := hx (arr w ((ofs B x - hdr) / S w), S w) (by
    simp only [ranges, List.mem_append, List.mem_map, List.mem_range]; exact .inl ⟨_, hj, rfl⟩)
  have e1 := Nat.div_mul_le_self (ofs B x - hdr) (S w)
  have e2 := Nat.lt_div_mul_add (a := ofs B x - hdr) (b := S w) (by omega_arith)
  simp only [arr] at this
  omega_arith

/-- `zeroArrays c`: the first `c` arrays (all `w + 2` words of each) := 0. -/
theorem zeroArrays_ok {s : State} {B : Addr} {Z w N c : Nat} (h : Ws s B Z w N) (hc : 1 ≤ c) (hcN : c ≤ N)
    (hN : N < 2048) :
    WP isa (zeroArrays c) s fun t => Ws t B Z w N ∧ Frame B w (List.range c) [] s.mem t.mem ∧
      (∀ j < c, wordsVal t.mem B (arr w j) (w + 2) = 0) ∧ Keep opRegs s t := by
  have fit := h.fits
  have nw := h.nowrap
  have hS : S w = 8 * (w + 2) := rfl
  have := h.wle
  have := h.wpos
  have hcN' : arr w c ≤ arr w N := arr_mono hcN
  have hca : arr w c = hdr + 8 * (c * (w + 2)) := by simp only [arr, hS]; rw [Nat.mul_left_comm]
  rw [zeroArrays, WP.seq_iff]
  have hb : WP isa (.block [.li .t3 (c : Int), .mul .t3 .t3 .s10, .shift .srl .d .t3 .t3 3,
      .addi .t0 .s11 (hdr : Int), .li .t5 0]) s fun u =>
      (u.gpr .t0 = off B hdr ∧ u.gpr .t3 = BitVec.ofNat 64 (c * (w + 2)) ∧ u.gpr .t5 = 0 ∧ u.mem = s.mem) ∧
        Keep [.t0, .t3, .t5] s u := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [exec_li_nat (show c < 2048 by omega_arith), exec_addi_nat (show hdr < 2048 by decide),
      fin64_exec_li_zero, h.s10, h.s11, zc_ofNat c w (by omega_arith) (by omega_arith)]
  refine WP.mono hb fun u ⟨⟨u0, u3, u5, um⟩, ku⟩ => ?_
  have k₁ : Keep opRegs s u := ku.mono (by decide)
  have hu := h.of_keep k₁
  have : c * (w + 2) ≥ 1 := Nat.mul_pos (by omega_arith) (by omega_arith)
  have : c * (w + 2) ≤ 2047 * 1026 := Nat.mul_le_mul (by omega_arith) (by omega_arith)
  refine WP.mono (zeroLoop_ok hu.scr u0 u3 u5 (by omega_arith) (by omega_arith) (by decide) (by omega_arith))
    fun t ⟨tz, tout, kt⟩ => ⟨hu.of_keep kt, ?_, fun j hj => ?_, Keep.trans' k₁ (kt.mono (by decide))⟩
  · rw [um] at tout; exact Frame.of_range tout
  · have := wordsVal_zero_part (a := j * (w + 2)) (c := w + 2) tz (by
      rw [show j * (w + 2) + (w + 2) = (j + 1) * (w + 2) by rw [Nat.succ_mul]]
      exact Nat.mul_le_mul_right _ hj)
    rwa [show hdr + 8 * (j * (w + 2)) = arr w j by simp only [arr, hS]; rw [Nat.mul_left_comm]] at this

end VG.Proof.Rsa.RISCV64.Keys
