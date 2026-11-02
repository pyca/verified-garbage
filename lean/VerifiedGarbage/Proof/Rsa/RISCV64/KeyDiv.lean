module

public import VerifiedGarbage.Impl.Rsa.RISCV64.Div
public import VerifiedGarbage.Proof.Rsa.RISCV64.KeyOps
public import VerifiedGarbage.Proof.Rsa.KeyMath
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Rsa.InverseArithmetic
import VerifiedGarbage.Proof.Bignum.RISCV64.MontFinish64
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The division of the RSA key operations on RISC-V

As on PPC64LE (`Proof/Rsa/PPC64LE/DivLoop.lean`), in words of 64 bits.
`step_ok`: a step of `Div.div q r d t` is `Proof/Rsa/KeyMath.lean`'s
`divStep` of the divisor `D = [d]` (its `w + 1` words) and `K = 64 w`, on the
quotient `[q]` and the remainder `[r]` (its `w + 1` words), when `D > 0`; for
`D = 0` it runs all the same. `div_ok`: the `64 w` steps from `(0, N)`, the
quotient `N / D` and the remainder `N mod D`.
-/

@[expose] public section

namespace VG.Proof.Rsa.RISCV64.Keys

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64 VG.Proof.Rsa.RISCV64.Loops
  VG.Impl.Bignum.RISCV64
open VG.Proof.Rsa (divStep divIter divIter_inv divIter_done borrow_iff)
open VG.Impl.Rsa.RISCV64.Keys (ptr ptrs subN selBody mov)
open VG.Impl.Rsa.RISCV64.Div (shlBody shift subtract bit keep setBit step init div)

/-- The `w + 1` words of array `j` (the remainder of the division). -/
abbrev num1 (m : Mem) (B : Addr) (w j : Nat) : Nat := wordsVal m B (arr w j) (w + 1)

/-- The registers the division may change. -/
abbrev divRegs : List Reg := [.t0, .t1, .t2, .t3, .t4, .t5, .t6, .a4, .a5, .s7]

/-- `w` words and one more. -/
theorem num1_eq (m : Mem) (B : Addr) (w j : Nat) :
    num1 m B w j = num m B w j + 2 ^ (64 * w) * (word m B (arr w j + 8 * w)).toNat :=
  wordsVal_succ_top _ _ _ _

/-- The `w + 1` words of an array outside the frame. -/
theorem Frame.num1 {B : Addr} {w : Nat} {js ds : List Nat} {m m' : Mem}
    (h : Frame B w js ds m m') {j : Nat} (hj : ∀ k ∈ js, k ≠ j) (hd : ∀ d ∈ ds, d + 8 ≤ hdr)
    (fit : arr w j + S w ≤ 2 ^ 64) : num1 m' B w j = num1 m B w j := by
  have hS : S w = 8 * (w + 2) := rfl
  exact h.words (fun k hk => by have := arr_disj (w := w) (hj k hk); omega_arith)
    (fun d hd' => by have := hd d hd'; have := hdr_le_arr w j; omega_arith) (by omega_arith)

/-! ## The left shift -/

/-- A word of the left shift: `2 x + c` split into its low word and the carry out. -/
theorem shl64_arith (x c : BitVec 64) (hc : c.toNat ≤ 1) :
    (x <<< 1 ||| c).toNat + 2 ^ 64 * (x >>> 63).toNat = 2 * x.toNat + c.toNat ∧ (x >>> 63).toNat ≤ 1 := by
  have hx := x.isLt
  have h1 : (x <<< 1).toNat = 2 * x.toNat % 2 ^ 64 := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega_arith
  have h2 : (x >>> 63).toNat = x.toNat / 2 ^ 63 := by rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hd : x <<< 1 &&& c = 0 := by
    rcases (show c.toNat = 0 ∨ c.toNat = 1 by omega_arith) with z | z
    · rw [show c = 0#64 from BitVec.eq_of_toNat_eq z, BitVec.and_zero]; rfl
    · rw [show c = 1#64 from BitVec.eq_of_toNat_eq z]
      apply BitVec.eq_of_getElem_eq; intro i hi
      simp only [BitVec.getElem_and, BitVec.getElem_shiftLeft]
      by_cases h : i = 0
      · subst h; simp
      · simp [h]
  rw [← BitVec.add_eq_or_of_and_eq_zero _ _ hd, BitVec.toNat_add, h1, h2]
  have := Nat.div_add_mod x.toNat (2 ^ 63)
  have := Nat.mod_lt x.toNat (show 0 < 2 ^ 63 by decide)
  constructor <;> omega_arith

/-- The left shift of `n` words at `t0` (`countLoop .t3 shlBody`), the carry in
and out in `t4`. -/
theorem shlLoop_ok {s : State} {B : Addr} {Z dO n : Nat} (hs : Scr s B Z)
    (h0 : s.gpr .t0 = off B dO) (h3 : s.gpr .t3 = BitVec.ofNat 64 n) (h4 : (s.gpr .t4).toNat ≤ 1)
    (hn : 1 ≤ n) (hn' : n < 2 ^ 32) (hO8 : dO % 8 = 0) (hO : dO + 8 * n ≤ Z) :
    WP isa (countLoop .t3 shlBody) s fun t =>
      (t.gpr .t4).toNat ≤ 1 ∧
      wordsVal t.mem B dO n + 2 ^ (64 * n) * (t.gpr .t4).toNat = 2 * wordsVal s.mem B dO n + (s.gpr .t4).toNat ∧
      Outside B dO (8 * n) s.mem t.mem ∧ Keep loopRegs s t := by
  have hnw := hs.nowrap
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .t0 = off B (dO + 8 * i) ∧ (t.gpr .t4).toNat ≤ 1 ∧ Outside B dO (8 * i) s.mem t.mem ∧
      wordsVal t.mem B dO i + 2 ^ (64 * i) * (t.gpr .t4).toNat = 2 * wordsVal s.mem B dO i + (s.gpr .t4).toNat ∧
      Keep loopRegs s t
  refine WP.mono (wp_countdown (body := .block (shlBody ++ ([.addi .t3 .t3 (-1)] : List Instr)))
    (cnt := .t3) (N := n) (by omega_arith) (by omega_arith) Inv
    (fun i hi t ⟨j0, j4, jout, jeq, jk⟩ hc => ?_)
    ⟨by rw [h0]; rfl, h4, Outside.refl _ _ _ _, by simp [wordsVal], Keep.refl _ _⟩ h3)
    fun t ⟨_, j4, jout, jeq, jk⟩ => ⟨j4, jeq, jout, jk⟩
  have hs' := hs.congr jk.2.2
  have hst : WP isa (.block (shlBody ++ ([.addi .t3 .t3 (-1)] : List Instr))) t fun t' =>
      (t'.gpr .t0 = off B (dO + 8 * i + 8) ∧ t'.gpr .t3 = t.gpr .t3 - BitVec.ofNat 64 1 ∧
        t'.mem = t.mem.writeW (off B (dO + 8 * i)) (word t.mem B (dO + 8 * i) <<< 1 ||| t.gpr .t4) ∧
        t'.gpr .t4 = word t.mem B (dO + 8 * i) >>> 63) ∧
      Keep loopRegs t t' := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [shlBody, j0, hs'.ld (show dO + 8 * i + 8 ≤ Z by omega_arith),
      hs'.st (show dO + 8 * i + 8 ≤ Z by omega_arith),
      hs'.al8 (show dO + 8 * i + 8 ≤ Z by omega_arith) (by omega_arith)]
  refine WP.mono hst fun t' ⟨⟨l0, l3, lm, l4⟩, lk⟩ => ⟨⟨?_, ?_, ?_, ?_, Keep.trans' jk lk⟩, l3⟩
  · rw [l0, show dO + 8 * i + 8 = dO + 8 * (i + 1) by omega_arith]
  · rw [l4]; exact (shl64_arith _ _ j4).2
  · rw [lm]; exact out_step _ jout (by omega_arith)
  · have wa : word t.mem B (dO + 8 * i) = word s.mem B (dO + 8 * i) := jout.word (by omega_arith) (by omega_arith)
    have k := (shl64_arith (word s.mem B (dO + 8 * i)) (t.gpr .t4) j4).1
    rw [lm, l4, fin64_wordsVal_write_top _ _ _ _ _ (by omega_arith), wa, wordsVal_succ_top s.mem B dO i,
      Nat.mul_succ, Nat.pow_add]
    have e : 2 ^ (64 * i) * (word s.mem B (dO + 8 * i) <<< 1 ||| t.gpr .t4).toNat +
        2 ^ (64 * i) * 2 ^ 64 * (word s.mem B (dO + 8 * i) >>> 63).toNat =
        2 * (2 ^ (64 * i) * (word s.mem B (dO + 8 * i)).toNat) + 2 ^ (64 * i) * (t.gpr .t4).toNat := by
      rw [Nat.mul_assoc, ← Nat.mul_add, k, Nat.mul_add, Nat.mul_left_comm]
    grind

/-- `shift q r`: `[q]' + 2^(64 w) c = 2 [q]` and `[r]' + 2^(64 (w + 1)) c' = 2 [r] + c`, `[r]` of
`w + 1` words. -/
theorem shift_ok {s : State} {B : Addr} {Z w N q r : Nat} (h : Ws s B Z w N)
    (hq : q < N) (hr : r < N) (hN : N ≤ 2048) (hqr : q ≠ r) :
    WP isa (shift q r) s fun t => Ws t B Z w N ∧ Frame B w [q, r] [] s.mem t.mem ∧
      (∃ c ≤ 1, num t.mem B w q + 2 ^ (64 * w) * c = 2 * num s.mem B w q ∧
        ∃ c' ≤ 1, num1 t.mem B w r + 2 ^ (64 * (w + 1)) * c' = 2 * num1 s.mem B w r + c) ∧
      Keep opRegs s t := by
  have fq := h.arr_fit hq
  have fr := h.arr_fit hr
  have nw := h.nowrap
  have hS : S w = 8 * (w + 2) := rfl
  have := h.wpos
  have := h.wle
  have dqr := arr_disj (w := w) hqr
  rw [shift, WP.seq_iff]
  refine ptr_ok h (by decide) (by decide) (show q < 2048 by omega_arith) ?_
  have hb : WP isa (.block [.li .t4 0, mov .t3 .s9]) (s.write .t0 (off B (arr w q))) fun u =>
      (u.gpr .t0 = off B (arr w q) ∧ u.gpr .t3 = BitVec.ofNat 64 w ∧ u.gpr .t4 = 0 ∧ u.mem = s.mem) ∧
        Keep [.t3, .t4] (s.write .t0 (off B (arr w q))) u := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [mov, fin64_exec_li_zero, h.s9, add_ofNat_zero']
  refine WP.mono hb fun u ⟨⟨u0, u3, u4, um⟩, ku⟩ => ?_
  have k₁ : Keep opRegs s u := ((Keep.write _ _ _).trans ku).mono (by decide)
  have hu : Ws u B Z w N := h.of_keep k₁
  rw [WP.seq_iff]
  refine WP.mono (shlLoop_ok hu.scr u0 u3 (by rw [u4]; decide) (by omega_arith) (by omega_arith) (arr_al _ _)
    (by omega_arith)) fun v ⟨c4, veq, vout, kv⟩ => ?_
  have k₂ : Keep opRegs s v := Keep.trans' k₁ kv
  have hv : Ws v B Z w N := h.of_keep k₂
  rw [WP.seq_iff]
  refine ptr_ok hv (by decide) (by decide) (show r < 2048 by omega_arith) ?_
  have hb2 : WP isa (.block [.addi .t3 .s9 1]) (v.write .t0 (off B (arr w r))) fun x =>
      (x.gpr .t0 = off B (arr w r) ∧ x.gpr .t3 = BitVec.ofNat 64 (w + 1) ∧ x.gpr .t4 = v.gpr .t4 ∧
        x.mem = v.mem) ∧ Keep [.t3] (v.write .t0 (off B (arr w r))) x := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [exec_addi_nat (show 1 < 2048 by decide), hv.s9]
    exact (BitVec.ofNat_add _ _).symm
  refine WP.mono hb2 fun x ⟨⟨x0, x3, x4, xm⟩, kx⟩ => ?_
  have k₃ : Keep opRegs s x := Keep.trans' k₂ (((Keep.write _ _ _).trans kx).mono (by decide))
  have hx : Ws x B Z w N := h.of_keep k₃
  refine WP.mono (shlLoop_ok hx.scr x0 x3 (by rw [x4]; exact c4) (by omega_arith) (by omega_arith) (arr_al _ _)
    (by omega_arith)) fun y ⟨c5, yeq, yout, ky⟩ => ?_
  rw [x4, xm] at yeq
  rw [xm] at yout
  rw [um, u4] at veq
  rw [um] at vout
  have rv : wordsVal v.mem B (arr w r) (w + 1) = num1 s.mem B w r := vout.wordsVal (by omega_arith) (by omega_arith)
  have qy : wordsVal y.mem B (arr w q) w = wordsVal v.mem B (arr w q) w :=
    yout.wordsVal (by omega_arith) (by omega_arith)
  rw [rv] at yeq
  refine ⟨hx.of_keep ky, ?_, ⟨(v.gpr .t4).toNat, c4, ?_, (y.gpr .t4).toNat, c5, yeq⟩, Keep.trans' k₃ ky⟩
  · exact (Frame.of_arr (d := 0) (by simpa only [Nat.add_zero] using vout) (by omega_arith) (by simp)).trans
      (Frame.of_arr (d := 0) (by simpa only [Nat.add_zero] using yout) (by omega_arith) (by simp))
  · change wordsVal y.mem B (arr w q) w + _ = 2 * wordsVal s.mem B (arr w q) w
    rw [qy]; simpa using veq

/-! ## The subtraction, the bit, the selection and the quotient bit -/

/-- `subtract r d t`: `[t] + [d] = [r] + 2^(64 (w + 1)) β`, over `w + 1` words. -/
theorem subtract_ok {s : State} {B : Addr} {Z w N r d t : Nat} (h : Ws s B Z w N)
    (hr : r < N) (hd : d < N) (ht : t < N) (hN : N ≤ 2048) (htr : t ≠ r) (htd : t ≠ d) :
    WP isa (subtract r d t) s fun u => Ws u B Z w N ∧ Frame B w [t] [] s.mem u.mem ∧
      num1 u.mem B w t + num1 s.mem B w d = num1 s.mem B w r + 2 ^ (64 * (w + 1)) * (u.gpr .t4).toNat ∧
      (u.gpr .t4).toNat ≤ 1 ∧ Keep opRegs s u :=
  subN_gen_ok (x := 1) h ht hr hd hN (Nat.le_refl _) (ahead_of_ne htr 1 (by decide))
    (ahead_of_ne htd 1 (by decide))

/-- The quotient bit and the mask: from the borrow `β` in `t4`, `a5 = 1 - β` and
`t4` the mask of `β = 0`. -/
theorem bit_ok {s : State} (b4 : (s.gpr .t4).toNat ≤ 1) :
    WP isa (.block bit) s fun u =>
      (u.gpr .a5 = BitVec.ofNat 64 (if (s.gpr .t4).toNat = 0 then 1 else 0) ∧
        u.gpr .t4 = (if decide ((s.gpr .t4).toNat = 0) then BitVec.allOnes 64 else 0) ∧
        u.mem = s.mem) ∧ Keep [.a5, .t4, .t5] s u := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  rcases (show (s.gpr .t4).toNat = 0 ∨ (s.gpr .t4).toNat = 1 by omega_arith) with z | z
  · have e : s.gpr .t4 = 0#64 := BitVec.eq_of_toNat_eq z
    brun [bit, e, fin64_exec_li_zero, z]
    decide
  · have e : s.gpr .t4 = 1#64 := BitVec.eq_of_toNat_eq z
    brun [bit, e, fin64_exec_li_zero, z]
    decide

/-- `keep r t`: `[r] := b ? [t] : [r]` over `w + 1` words, the mask of `b` in `t4`. -/
theorem keep_ok {s : State} {B : Addr} {Z w N r t : Nat} (h : Ws s B Z w N)
    (hr : r < N) (ht : t < N) (hN : N ≤ 2048) (hrt : r ≠ t) {b : Bool}
    (h4 : s.gpr .t4 = if b then BitVec.allOnes 64 else 0) :
    WP isa (keep r t) s fun u => Ws u B Z w N ∧ Frame B w [r] [] s.mem u.mem ∧
      num1 u.mem B w r = (if b then num1 s.mem B w t else num1 s.mem B w r) ∧ Keep opRegs s u := by
  have fr := h.arr_fit hr
  have ft := h.arr_fit ht
  have hS : S w = 8 * (w + 2) := rfl
  have := h.wle
  have := h.wpos
  rw [keep, WP.seq_iff]
  refine ptrs_ok h (by omega_arith) (by omega_arith) (by omega_arith) fun u p0 p1 p2 ku mu => ?_
  have hu := h.of_keep ku
  have hb : WP isa (.block [.addi .t3 .s9 1]) u fun x =>
      (x.gpr .t0 = off B (arr w r) ∧ x.gpr .t1 = off B (arr w r) ∧ x.gpr .t2 = off B (arr w t) ∧
        x.gpr .t3 = BitVec.ofNat 64 (w + 1) ∧ x.gpr .t4 = s.gpr .t4 ∧ x.mem = u.mem) ∧ Keep [.t3] u x := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [exec_addi_nat (show 1 < 2048 by decide), hu.s9, p0, p1, p2, ku.gpr (r := .t4) (by decide)]
    exact (BitVec.ofNat_add _ _).symm
  refine WP.mono hb fun x ⟨⟨x0, x1, x2, x3, x4, xm⟩, kx⟩ => ?_
  have k₁ : Keep opRegs s x := (ku.trans kx).mono (by decide)
  have hx : Ws x B Z w N := h.of_keep k₁
  refine WP.mono (selLoop_ok hx.scr (b := b) x0 x1 x2 x3 (by rw [x4, h4]) (by omega_arith) (by omega_arith)
    (arr_al _ _) (arr_al _ _) (arr_al _ _) (by omega_arith) (by omega_arith) (by omega_arith)
    (ahead_self _ _ _) (ahead_of_ne hrt 1 (by decide))) ?_
  intro y ⟨vv, out, ky, _⟩
  rw [xm, mu] at vv out
  exact ⟨hx.of_keep ky, Frame.of_arr (d := 0) (by simpa only [Nat.add_zero] using out)
    (by omega_arith) (by simp), vv, Keep.trans' k₁ ky⟩

/-- An even word or'ed with a bit is their sum. -/
theorem or_bit64 (x c : BitVec 64) (hx : x.toNat % 2 = 0) (hc : c.toNat ≤ 1) :
    (x ||| c).toNat = x.toNat + c.toNat := by
  rcases (show c.toNat = 0 ∨ c.toNat = 1 by omega_arith) with z | z
  · rw [show c = 0#64 from BitVec.eq_of_toNat_eq z, BitVec.or_zero]; rfl
  · rw [show c = 1#64 from BitVec.eq_of_toNat_eq z, or_one_toNat]
    show _ = x.toNat + 1
    omega_arith

/-- `setBit q`: the bit in `a5` added to the even `[q]`, and `s7` decremented. -/
theorem setBit_ok {s : State} {B : Addr} {Z w N q : Nat} (h : Ws s B Z w N) (hq : q < N)
    (hN : N ≤ 2048) (even : num s.mem B w q % 2 = 0) (b5 : (s.gpr .a5).toNat ≤ 1) :
    WP isa (.block (setBit q)) s fun u => Ws u B Z w N ∧ Frame B w [q] [] s.mem u.mem ∧
      num u.mem B w q = num s.mem B w q + (s.gpr .a5).toNat ∧
      u.gpr .s7 = s.gpr .s7 - BitVec.ofNat 64 1 ∧ Keep [.t0, .t5, .s7] s u := by
  have fit := h.arr_fit hq
  have nw := h.nowrap
  have hS : S w = 8 * (w + 2) := rfl
  have := h.wpos
  have := h.wle
  unfold setBit
  refine ptr_ok h (by decide) (by decide) (show q < 2048 by omega_arith) ?_
  have hb : WP isa (.block [.load .d .t5 .t0 0, .logic .or .t5 .t5 .a5, .store .d .t5 .t0 0,
      .addi .s7 .s7 (-1)]) (s.write .t0 (off B (arr w q))) fun u =>
        (u.mem = s.mem.writeW (off B (arr w q)) (word s.mem B (arr w q) ||| s.gpr .a5) ∧
          u.gpr .s7 = s.gpr .s7 - BitVec.ofNat 64 1) ∧ Keep [.t5, .s7] (s.write .t0 (off B (arr w q))) u := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [add_ofNat_zero', h.scr.ld (d := arr w q) (n := 8) (by omega_arith),
      h.scr.st (d := arr w q) (n := 8) (by omega_arith), h.scr.al8 (d := arr w q) (by omega_arith) (arr_al _ _)]
  refine WP.mono hb fun u ⟨⟨mu, u7⟩, ku⟩ => ?_
  have kt : Keep [.t0, .t5, .s7] s u := ((Keep.write _ _ _).trans ku).mono (by decide)
  obtain ⟨fr, ev⟩ := low_write (m := s.mem) (B := B) (j := q) (by omega_arith) (by omega_arith)
    (word s.mem B (arr w q) ||| s.gpr .a5)
  have e0 : (word s.mem B (arr w q)).toNat % 2 = 0 := by
    rw [← wordsVal_mod2 s.mem B (d := arr w q) (k := w) (by omega_arith)]; exact even
  have e64 : num s.mem B w q % 2 ^ 64 = (word s.mem B (arr w q)).toNat :=
    wordsVal_mod64 s.mem B (d := arr w q) (k := w) (by omega_arith)
  refine ⟨h.of_keep kt, by rw [mu]; exact fr, ?_, u7, kt⟩
  rw [mu, ev, or_bit64 _ _ e0 b5]
  have := Nat.mod_add_div (num s.mem B w q) (2 ^ 64)
  omega_arith

/-! ## A step, and the division -/

/-- The numbers of a step: from the shift's equations and the subtraction's,
the step is `divStep`. -/
theorem step_arith {D R Q Q1 R1 T c c' β P1 P2 H : Nat} (hD : 0 < D) (hR : R < D)
    (hDP : D < P1) (hP1 : P1 = 2 * H) (hP2 : P2 = 2 ^ 64 * P1) (hQ1 : Q1 < P1) (hT : T < P2)
    (hc : c ≤ 1) (hβ : β ≤ 1) (e1 : Q1 + P1 * c = 2 * Q) (e2 : R1 + P2 * c' = 2 * R + c)
    (e3 : T + D = R1 + P2 * β) :
    R1 = 2 * R + Q / H ∧ Q1 = 2 * Q % P1 ∧ (β = 0 ↔ D ≤ R1) ∧ (β = 0 → T = R1 - D) := by
  have hH : 0 < H := by omega_arith
  have hc' : c' = 0 := by
    rcases Nat.eq_zero_or_pos c' with z | z
    · exact z
    · have : P2 ≤ P2 * c' := Nat.le_mul_of_pos_right _ z
      have : P1 ≤ P2 := by rw [hP2]; exact Nat.le_mul_of_pos_left _ (by decide)
      omega_arith
  subst hc'
  have hcQ : c = Q / H := by
    have : 2 * Q / P1 = c := by
      rw [← e1, Nat.add_mul_div_left _ _ (by omega_arith), Nat.div_eq_of_lt hQ1, Nat.zero_add]
    rw [← this, hP1, Nat.mul_div_mul_left _ _ (by decide)]
  have hmod : Q1 = 2 * Q % P1 := by
    rw [← e1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hQ1]
  have hb := borrow_iff e3 hT hβ
  refine ⟨by omega_arith, hmod, hb, fun h0 => ?_⟩
  rw [h0, Nat.mul_zero, Nat.add_zero] at e3
  omega_arith

/-- The registers a step changes. -/
abbrev stepRegs : List Reg := divRegs

/-- A step of the division. -/
theorem step_ok {s : State} {B : Addr} {Z w N q r d t : Nat} (h : Ws s B Z w N)
    (hq : q < N) (hr : r < N) (hd : d < N) (ht : t < N) (hN : N ≤ 2048)
    (hqr : q ≠ r) (hqd : q ≠ d) (hqt : q ≠ t) (hrd : r ≠ d) (hrt : r ≠ t) (hdt : d ≠ t)
    {D N₀ k : Nat} (hk : k < 64 * w) (hN₀ : N₀ < 2 ^ (64 * w)) (hD : num1 s.mem B w d = D)
    (hDw : D < 2 ^ (64 * w))
    (vals : 0 < D → num s.mem B w q = (divIter D (64 * w) k (0, N₀)).2 ∧
      num1 s.mem B w r = (divIter D (64 * w) k (0, N₀)).1) :
    WP isa (step q r d t) s fun u => Ws u B Z w N ∧ Frame B w [q, r, t] [] s.mem u.mem ∧
      u.gpr .s7 = s.gpr .s7 - BitVec.ofNat 64 1 ∧ Keep stepRegs s u ∧
      (0 < D → num u.mem B w q = (divIter D (64 * w) (k + 1) (0, N₀)).2 ∧
        num1 u.mem B w r = (divIter D (64 * w) (k + 1) (0, N₀)).1) := by
  have fq := h.arr_fit hq
  have fr := h.arr_fit hr
  have fd := h.arr_fit hd
  have ft := h.arr_fit ht
  have nw := h.nowrap
  have hS : S w = 8 * (w + 2) := rfl
  have := h.wpos
  rw [step, WP.seq_iff]
  refine WP.mono (shift_ok h hq hr hN hqr) fun s1 ⟨h1, km1, ⟨c, hc, eq1, c', hc', er1⟩, k1⟩ => ?_
  rw [WP.seq_iff]
  refine WP.mono (subtract_ok h1 hr hd ht hN (Ne.symm hrt) (Ne.symm hdt))
    fun s2 ⟨h2, km2, eT, hβ, k2⟩ => ?_
  rw [WP.seq_iff]
  refine WP.mono (bit_ok hβ) fun s3 ⟨⟨a5, t4, m3⟩, k3⟩ => ?_
  have h3 : Ws s3 B Z w N := h2.of_keep k3
  rw [WP.seq_iff]
  refine WP.mono (keep_ok h3 hr ht hN hrt (b := decide ((s2.gpr .t4).toNat = 0)) t4)
    fun s4 ⟨h4, km4, eR, k4⟩ => ?_
  have e5 : s4.gpr .a5 = s3.gpr .a5 := k4.gpr (r := .a5) (by decide)
  -- The quotient after the shift, through the subtraction and the selection.
  have q2 : num s2.mem B w q = num s1.mem B w q :=
    Frame.num km2 (by simp; omega_arith) (by simp) (by omega_arith)
  have q4 : num s4.mem B w q = num s1.mem B w q := by
    rw [Frame.num km4 (by simp; omega_arith) (by simp) (by omega_arith), m3, q2]
  have even : num s4.mem B w q % 2 = 0 := by
    rw [q4]
    have : 2 ∣ 2 ^ (64 * w) * c :=
      Nat.dvd_mul_right_of_dvd (Nat.dvd_of_mod_eq_zero (Nat.pow_mod 2 (64 * w) 2 ▸ by
        rw [Nat.mod_self, Nat.zero_pow (by omega_arith)])) _
    omega_arith
  refine WP.mono (setBit_ok h4 hq hN even (by rw [e5, a5]; split <;> decide))
    fun u ⟨hu, km5, eQ, u7, k5⟩ => ?_
  have kr : Keep stepRegs s u := ((((k1.trans k2).trans k3).trans k4).trans k5).mono (by decide)
  have k12 : Frame B w [q, r, t] [] s.mem s2.mem := Frame.join km1 km2
  have k45 : Frame B w [q, r, t] [] s2.mem u.mem := by
    rw [← m3]; exact Frame.join km4 km5
  refine ⟨hu, k12.trans k45, ?_, kr, fun hD0 => ?_⟩
  · rw [u7, k4.gpr (r := .s7) (by decide), k3.gpr (r := .s7) (by decide), k2.gpr (r := .s7) (by decide),
      k1.gpr (r := .s7) (by decide)]
  · obtain ⟨vq, vr⟩ := vals hD0
    obtain ⟨_, hR, -, -, -⟩ := divIter_inv hD0 hN₀ k (by omega_arith)
    have es : divIter D (64 * w) (k + 1) (0, N₀) = divStep D (64 * w) (divIter D (64 * w) k (0, N₀)) := rfl
    -- The divisor and the shifted remainder, through the writes.
    have d1 : num1 s1.mem B w d = D := by
      rw [Frame.num1 km1 (by simp; omega_arith) (by simp) (by omega_arith), hD]
    have r2 : num1 s2.mem B w r = num1 s1.mem B w r :=
      Frame.num1 km2 (by simp; omega_arith) (by simp) (by omega_arith)
    have t3 : num1 s3.mem B w t = num1 s2.mem B w t := by rw [m3]
    have ur : num1 u.mem B w r = num1 s4.mem B w r :=
      Frame.num1 km5 (by simp; omega_arith) (by simp) (by omega_arith)
    have hP2 : 2 ^ (64 * (w + 1)) = 2 ^ 64 * 2 ^ (64 * w) := by
      rw [show 64 * (w + 1) = 64 + 64 * w by omega_arith, Nat.pow_add]
    have hP1 : 2 ^ (64 * w) = 2 * 2 ^ (64 * w - 1) := by
      obtain ⟨j, hj⟩ : ∃ j, 64 * w = j + 1 := ⟨64 * w - 1, by omega_arith⟩
      rw [hj, Nat.add_sub_cancel, Nat.pow_succ, Nat.mul_comm]
    have hQ1 : num s1.mem B w q < 2 ^ (64 * w) := wordsVal_lt _ _ _ _
    have hT : num1 s2.mem B w t < 2 ^ (64 * (w + 1)) := wordsVal_lt _ _ _ _
    rw [d1] at eT
    have hR' : num1 s.mem B w r < D := by rw [vr]; exact hR
    obtain ⟨eR1, eQ1, hb, hTv⟩ := step_arith hD0 hR' hDw hP1 hP2 hQ1 hT hc hβ eq1 er1 eT
    have ep : divIter D (64 * w) k (0, N₀) = (num1 s.mem B w r, num s.mem B w q) :=
      Prod.ext vr.symm vq.symm
    rw [es, ep]
    simp only [divStep]
    rw [ur, eR, t3, m3, r2, eQ, e5, a5, q4, ← eR1, ← eQ1]
    by_cases hl : num1 s1.mem B w r < D
    · have hβ1 : (s2.gpr .t4).toNat ≠ 0 := fun z => absurd (hb.mp z) (by omega_arith)
      simp only [hl, hβ1, ↓reduceIte, decide_false]
      exact ⟨by simp, rfl⟩
    · have hβ0 : (s2.gpr .t4).toNat = 0 := hb.mpr (by omega_arith)
      simp only [hl, hβ0, ↓reduceIte, decide_true]
      exact ⟨by simp, hTv hβ0⟩

theorem shl6_ofNat (w : Nat) : BitVec.ofNat 64 w <<< 6 = BitVec.ofNat 64 (64 * w) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega_arith

/-- `init r`: the remainder's `w + 1` words := 0, and `64 w` steps to count in `s7`. -/
theorem init_ok {s : State} {B : Addr} {Z w N r : Nat} (h : Ws s B Z w N) (hr : r < N)
    (hN : N ≤ 2048) :
    WP isa (init r) s fun u => Ws u B Z w N ∧ Frame B w [r] [] s.mem u.mem ∧
      num1 u.mem B w r = 0 ∧ u.gpr .s7 = BitVec.ofNat 64 (64 * w) ∧ Keep [.t0, .t3, .t5, .s7] s u := by
  have fr := h.arr_fit hr
  have nw := h.nowrap
  have hS : S w = 8 * (w + 2) := rfl
  have := h.wle
  have := h.wpos
  rw [init, WP.seq_iff]
  refine ptr_ok h (by decide) (by decide) (show r < 2048 by omega_arith) ?_
  have hb : WP isa (.block [.addi .t3 .s9 1, .li .t5 0]) (s.write .t0 (off B (arr w r))) fun u =>
      (u.gpr .t0 = off B (arr w r) ∧ u.gpr .t3 = BitVec.ofNat 64 (w + 1) ∧ u.gpr .t5 = 0 ∧
        u.mem = s.mem) ∧ Keep [.t3, .t5] (s.write .t0 (off B (arr w r))) u := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [exec_addi_nat (show 1 < 2048 by decide), fin64_exec_li_zero, h.s9]
    exact (BitVec.ofNat_add _ _).symm
  refine WP.mono hb fun u ⟨⟨u0, u3, u5, mu⟩, ku⟩ => ?_
  have k₁ : Keep [.t0, .t3, .t5, .s7] s u := ((Keep.write _ _ _).trans ku).mono (by decide)
  have hu : Ws u B Z w N := h.of_keep k₁
  rw [WP.seq_iff]
  refine WP.mono (zeroLoop_ok hu.scr u0 u3 u5 (by omega_arith) (by omega_arith) (arr_al _ _) (by omega_arith))
    fun v ⟨z, out, kv⟩ => ?_
  have k₂ : Keep [.t0, .t3, .t5, .s7] s v := Keep.trans' k₁ (kv.mono (by decide))
  have hv : Ws v B Z w N := h.of_keep k₂
  have hl : WP isa (.block [.shift .sll .d .s7 .s9 6]) v fun x =>
      (x.gpr .s7 = BitVec.ofNat 64 (64 * w) ∧ x.mem = v.mem) ∧ Keep [.s7] v x := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [hv.s9, shl6_ofNat w]
  refine WP.mono hl fun x ⟨⟨x7, xm⟩, kx⟩ =>
    ⟨hv.of_keep kx, ?_, ?_, x7, Keep.trans' k₂ (kx.mono (by decide))⟩
  · rw [xm, ← mu]
    exact Frame.of_arr (d := 0) (by simpa using out) (by omega_arith) (by simp)
  · rw [xm]; exact z

/-- The count after a step. -/
theorem count_sub {N i : Nat} (hi : i < N) :
    BitVec.ofNat 64 (N - i) - BitVec.ofNat 64 1 = BitVec.ofNat 64 (N - (i + 1)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

/-- `Div.div q r d t`: `[q] := [q] / [d]`, `[r] := [q] mod [d]` (its `w + 1` words, so word `w`
of `r` is 0), for a divisor whose word `w` is 0, when it is not 0. -/
theorem div_ok {s : State} {B : Addr} {Z w N q r d t : Nat} (h : Ws s B Z w N)
    (hq : q < N) (hr : r < N) (hd : d < N) (ht : t < N) (hN : N ≤ 2048)
    (hqr : q ≠ r) (hqd : q ≠ d) (hqt : q ≠ t) (hrd : r ≠ d) (hrt : r ≠ t) (hdt : d ≠ t)
    (hdz : word s.mem B (arr w d + 8 * w) = 0) :
    WP isa (div q r d t) s fun u => Ws u B Z w N ∧
      Frame B w [q, r, t] [] s.mem u.mem ∧ Keep divRegs s u ∧ u.gpr .s7 = 0 ∧
      (0 < num s.mem B w d →
        num u.mem B w q = num s.mem B w q / num s.mem B w d ∧
        num1 u.mem B w r = num s.mem B w q % num s.mem B w d ∧
        num u.mem B w r = num s.mem B w q % num s.mem B w d ∧
        word u.mem B (arr w r + 8 * w) = 0) := by
  have fd := h.arr_fit hd
  have fr := h.arr_fit hr
  have nw := h.nowrap
  have hS : S w = 8 * (w + 2) := rfl
  have := h.wpos
  have := h.wle
  -- The divisor's `w + 1` words are its number.
  have hD : num1 s.mem B w d = num s.mem B w d := by
    rw [num1_eq, hdz]; rfl
  have hDw : num s.mem B w d < 2 ^ (64 * w) := wordsVal_lt _ _ _ _
  have hN₀ : num s.mem B w q < 2 ^ (64 * w) := wordsVal_lt _ _ _ _
  have hK : 64 * w < 2 ^ 64 := by omega_arith
  rw [div, WP.seq_iff]
  refine WP.mono (init_ok h hr hN) fun u ⟨hu, km, z, u7, ku⟩ => ?_
  let D := num s.mem B w d
  let N₀ := num s.mem B w q
  let Inv : Nat → State → Prop := fun i x =>
    Ws x B Z w N ∧ Frame B w [q, r, t] [] s.mem x.mem ∧ Keep divRegs s x ∧
      x.gpr .s7 = BitVec.ofNat 64 (64 * w - i) ∧
      (0 < D → num x.mem B w q = (divIter D (64 * w) i (0, N₀)).2 ∧
        num1 x.mem B w r = (divIter D (64 * w) i (0, N₀)).1)
  have i0 : Inv 0 u := ⟨hu, km.mono, ku.mono (by decide), by rw [u7, Nat.sub_zero],
    fun _ => ⟨Frame.num km (by simp; omega_arith) (by simp) (by have := h.fit64 hq; omega_arith), z⟩⟩
  refine WP.mono (wp_countdown (body := step q r d t) (cnt := .s7) (N := 64 * w)
    hK (by omega_arith) Inv (fun i hi x ⟨hx, kx, rx, cx, vx⟩ _ => ?_) i0 u7) fun x ⟨hx, kx, rx, cx, vx⟩ => ?_
  · have dx : num1 x.mem B w d = D := by
      rw [Frame.num1 kx (by simp; omega_arith) (by simp) (by omega_arith), hD]
    refine WP.mono (step_ok hx hq hr hd ht hN hqr hqd hqt hrd hrt hdt hi hN₀ dx hDw vx)
      fun y ⟨hy, ky, y7, ry, vy⟩ => ⟨⟨hy, kx.trans ky, Keep.trans' rx ry,
        by rw [y7, cx, count_sub hi], vy⟩, y7⟩
  · refine ⟨hx, kx, rx, by rw [cx, Nat.sub_self]; rfl, fun hD0 => ?_⟩
    obtain ⟨e1, e2⟩ := vx hD0
    rw [divIter_done hD0 hN₀] at e1 e2
    have hlt : num s.mem B w q % num s.mem B w d < 2 ^ (64 * w) :=
      Nat.lt_trans (Nat.mod_lt _ hD0) hDw
    have e3 := num1_eq x.mem B w r
    change num1 x.mem B w r = num s.mem B w q % num s.mem B w d at e2
    have hw0 : (word x.mem B (arr w r + 8 * w)).toNat = 0 := by
      rcases Nat.eq_zero_or_pos (word x.mem B (arr w r + 8 * w)).toNat with e | e
      · exact e
      · have : 2 ^ (64 * w) ≤ 2 ^ (64 * w) * (word x.mem B (arr w r + 8 * w)).toNat :=
          Nat.le_mul_of_pos_right _ e
        omega_arith
    refine ⟨e1, e2, by rw [hw0, Nat.mul_zero, Nat.add_zero] at e3; omega_arith,
      BitVec.eq_of_toNat_eq (by rw [hw0]; rfl)⟩

end VG.Proof.Rsa.RISCV64.Keys
