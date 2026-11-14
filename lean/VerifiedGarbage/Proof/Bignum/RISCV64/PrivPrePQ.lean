module

public import VerifiedGarbage.Proof.Bignum.RISCV64.CrtMid
public import VerifiedGarbage.Impl.Bignum.RISCV64.PrivPre
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.RISCV64.CrtCheck
import VerifiedGarbage.Proof.Bignum.RISCV64.PreR2
import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
import VerifiedGarbage.Proof.Bignum.RISCV64.PubLoad
import VerifiedGarbage.Proof.Bignum.RISCV64.MontFinish64
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# An RSA private key's precomputed values on RISC-V: `p q = n` at the factors' widths

`checkPQs_ok`: `PrivPre.checkPQs` is a check of `p q = n` as
`Crt.checksWith` needs it (`Crt.PQOk`), when `p` and `q` fit in `w_p` (`a3`)
and `w_q` (`t1`) words, `w_p + w_q ≤ W`:

* `rowWord_ok`, `row_ok`: a row of the schoolbook product, `t += a q`
  over `q`'s `w_q` words, its carry into the word after them (`mac_arith`);
* `rows_ok`: `w_p` rows, `t = p q` over `w_p + w_q` words, from `t = 0`;
* `checkPQs_ok`: array 6 zeroed, `p q` into it, then `Crt.pqEq_ok`.
-/

@[expose] public section

namespace VG.Proof.Bignum.RISCV64.PrivPre

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.RISCV64
  VG.Impl.Bignum.RISCV64.PrivPre
open VG.Proof.Bignum.RISCV64
open VG.Proof.Bignum (slot Arrays)

/-- `a + b` words: the first `a`, and `2^(64 a)` times the `b` after them. -/
theorem wordsVal_app (m : Mem) (B : Addr) (d a : Nat) : ∀ b,
    wordsVal m B d (a + b) = wordsVal m B d a + 2 ^ (64 * a) * wordsVal m B (d + 8 * a) b
  | 0 => by simp [wordsVal]
  | b + 1 => by
    rw [← Nat.add_assoc, wordsVal_succ_top, wordsVal_app m B d a b, wordsVal_succ_top,
      show d + 8 * (a + b) = d + 8 * a + 8 * b by omega_arith, show 64 * (a + b) = 64 * a + 64 * b by omega_arith,
      Nat.pow_add, Nat.mul_add (2 ^ (64 * a)), Nat.mul_assoc, Nat.add_assoc]

/-- `x + y` as its low word and the carry `sltu` computes. -/
theorem add_carry (x y : BitVec 64) :
    (x + y).toNat + 2 ^ 64 * (if x + y < y then (1 : BitVec 64) else 0).toNat = x.toNat + y.toNat := by
  have hx := x.isLt; have hy := y.isLt
  by_cases h : x + y < y
  · rw [ite_eq_left h]; rw [BitVec.lt_def, BitVec.toNat_add] at h
    rw [BitVec.toNat_add, show (1 : BitVec 64).toNat = 1 from rfl]; omega_arith
  · rw [ite_eq_right h]; rw [BitVec.lt_def, BitVec.toNat_add] at h
    rw [BitVec.toNat_add, show (0 : BitVec 64).toNat = 0 from rfl]; omega_arith

/-- The arithmetic of a word of a row: `a q + t + c` as its low word and the
next carry, the high word of `a q` plus the carries of the two additions. -/
theorem mac_arith (a q t c : BitVec 64) :
    (a * q + t + c).toNat + 2 ^ 64 * (BitVec.ofNat 64 (a.toNat * q.toNat / 2 ^ 64) +
      (if a * q + t < t then 1 else 0) + (if a * q + t + c < c then 1 else 0)).toNat =
      a.toNat * q.toNat + t.toNat + c.toNat := by
  have ha := a.isLt; have hq := q.isLt; have ht := t.isLt; have hc := c.isLt
  have hP : a.toNat * q.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := Nat.mul_le_mul (by omega_arith) (by omega_arith)
  have hd := Nat.div_add_mod (a.toNat * q.toNat) (2 ^ 64)
  have e0 : (a * q).toNat = a.toNat * q.toNat % 2 ^ 64 := BitVec.toNat_mul _ _
  have e1 := add_carry (a * q) t
  have e2 := add_carry (a * q + t) c
  have hhi : a.toNat * q.toNat / 2 ^ 64 < 2 ^ 64 := by
    have := Nat.div_le_div_right (c := 2 ^ 64) hP; omega_arith
  generalize (if a * q + t < t then (1 : BitVec 64) else 0) = c1 at e1 ⊢
  generalize (if a * q + t + c < c then (1 : BitVec 64) else 0) = c2 at e2 ⊢
  have hc1 : c1.toNat ≤ 1 := by
    have := (a * q + t).isLt; have := (a * q).isLt; rw [e0] at e1
    rcases Nat.lt_or_ge c1.toNat 2 with h | h
    · omega_arith
    · have := Nat.mul_le_mul_left (2 ^ 64) h; omega_arith
  have hc2 : c2.toNat ≤ 1 := by
    have := (a * q + t + c).isLt; have := (a * q + t).isLt
    rcases Nat.lt_or_ge c2.toNat 2 with h | h
    · omega_arith
    · have := Nat.mul_le_mul_left (2 ^ 64) h; omega_arith
  have hsum : a.toNat * q.toNat / 2 ^ 64 + c1.toNat + c2.toNat < 2 ^ 64 := by
    have hl := (a * q + t + c).isLt
    have hb : a.toNat * q.toNat + t.toNat + c.toNat ≤ 2 ^ 128 - 1 := by omega_arith
    rw [e0] at e1
    rcases Nat.lt_or_ge (a.toNat * q.toNat / 2 ^ 64 + c1.toNat + c2.toNat) (2 ^ 64) with h | h
    · exact h
    · have := Nat.mul_le_mul_left (2 ^ 64) h; omega_arith
  rw [BitVec.toNat_add (BitVec.ofNat 64 _ + c1) c2, BitVec.toNat_add (BitVec.ofNat 64 _) c1, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hhi,
    Nat.mod_eq_of_lt (show a.toNat * q.toNat / 2 ^ 64 + c1.toNat < 2 ^ 64 by omega_arith), Nat.mod_eq_of_lt hsum]
  rw [e0] at e1
  omega_arith

/-- `⌈L / 8⌉`, as `PrivPre.pqLens` computes it. -/
theorem len_words (L : Nat) (hL : L < 2 ^ 32) :
    (BitVec.ofNat 64 L + BitVec.ofNat 64 7) >>> 3 = BitVec.ofNat 64 ((L + 7) / 8) :=
  BitVec.eq_of_toNat_eq (by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_add, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := L) (by omega_arith),
      Nat.mod_eq_of_lt (a := L + 7) (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)])

/-! ## A row -/

/-- What a row keeps after `j` words, from `s`, with the multiplier `a`
(`a6`): the pointers, the carry `c` (`s1`), with
`t_{<j} + 2^(64 j) c = t₀_{<j} + a q_{<j}`, and the words from `j` on. -/
def RowI (s : State) (B : Addr) (dA dQ : Nat) (a : BitVec 64) (j : Nat) (t : State) : Prop :=
  t.gpr .t3 = off B (dA + 8 * j) ∧ t.gpr .t4 = off B (dQ + 8 * j) ∧ t.gpr .a6 = a ∧
    Outside B dA (8 * j) s.mem t.mem ∧
    wordsVal t.mem B dA j + 2 ^ (64 * j) * (t.gpr .s1).toNat = wordsVal s.mem B dA j + a.toNat * wordsVal s.mem B dQ j ∧
    Keep [.s0, .s1, .s2, .s3, .t3, .t4, .t5] s t

theorem rowWord_ok {s : State} {B : Addr} {Z dA dQ wq : Nat} {a : BitVec 64} (hs : Scr s B Z) (hA8 : dA % 8 = 0)
    (hQ8 : dQ % 8 = 0) (hA : dA + 8 * wq ≤ Z) (hQ : dQ + 8 * wq ≤ Z) (dAQ : dQ + 8 * wq ≤ dA ∨ dA + 8 * wq ≤ dQ)
    {j : Nat} (hj : j < wq) {t : State} (hI : RowI s B dA dQ a j t) :
    WP isa (.block (rowWord ++ ([.addi .t5 .t5 (-1)] : List Instr))) t fun t' =>
      RowI s B dA dQ a (j + 1) t' ∧ t'.gpr .t5 = t.gpr .t5 - BitVec.ofNat 64 1 := by
  have hnw := hs.nowrap
  obtain ⟨j3, j4, j6, jout, jv, jk⟩ := hI
  have hs' := hs.congr jk.2.2
  have wT : Mont.word t.mem B (dA + 8 * j) = Mont.word s.mem B (dA + 8 * j) := jout.word (by omega_using []) (by omega_using [hA, hj, hnw])
  have wQ : Mont.word t.mem B (dQ + 8 * j) = Mont.word s.mem B (dQ + 8 * j) := jout.word (by omega_using [dAQ, hj]) (by omega_using [hQ, hj, hnw])
  generalize hq : Mont.word s.mem B (dQ + 8 * j) = q at wQ
  generalize hx : Mont.word s.mem B (dA + 8 * j) = x at wT
  have rQ : t.mem.readW (off B (dQ + 8 * j)) 64 = q := wQ
  have rT : t.mem.readW (off B (dA + 8 * j)) 64 = x := wT
  refine WP.mono (WP.keep [.s0, .s1, .s2, .s3, .t3, .t4, .t5] (Q := fun t' =>
      t'.gpr .t3 = off B (dA + 8 * j + 8) ∧ t'.gpr .t4 = off B (dQ + 8 * j + 8) ∧
      t'.gpr .t5 = t.gpr .t5 - BitVec.ofNat 64 1 ∧
      t'.gpr .s1 = BitVec.ofNat 64 ((t.gpr .a6).toNat * q.toNat / 2 ^ 64) +
        (if t.gpr .a6 * q + x < x then 1 else 0) + (if t.gpr .a6 * q + x + t.gpr .s1 < t.gpr .s1 then 1 else 0) ∧
      t'.mem = t.mem.writeW (off B (dA + 8 * j)) (t.gpr .a6 * q + x + t.gpr .s1)) (by
    unfold rowWord
    brun [j3, j4, rQ, rT, BitVec.add_zero, hs'.ld (show dQ + 8 * j + 8 ≤ Z by omega_using [hQ, hj]),
      hs'.al8 (show dQ + 8 * j + 8 ≤ Z by omega_using [hQ, hj]) (by omega_using [hQ8]), hs'.ld (show dA + 8 * j + 8 ≤ Z by omega_using [hA, hj]),
      hs'.al8 (show dA + 8 * j + 8 ≤ Z by omega_using [hA, hj]) (by omega_using [hA8]), hs'.st (show dA + 8 * j + 8 ≤ Z by omega_using [hA, hj])])
    (by rfl) (by rfl)) fun t' ⟨⟨u3, u4, u5, u1, um⟩, uk⟩ => ⟨⟨?_, ?_, ?_, ?_, ?_, Keep.trans' jk uk⟩, u5⟩
  · rw [u3, show dA + 8 * j + 8 = dA + 8 * (j + 1) by omega_using []]
  · rw [u4, show dQ + 8 * j + 8 = dQ + 8 * (j + 1) by omega_using []]
  · rw [uk.gpr (by decide), j6]
  · rw [um]
    exact (jout.mono (Nat.le_refl _) (by omega_using [])).trans
      ((writeW_outside t.mem B (d := dA + 8 * j) _ (by omega_using [hA, hj, hnw])).mono (by omega_using []) (by omega_using []))
  · have km := mac_arith (t.gpr .a6) q x (t.gpr .s1)
    rw [um, u1, fin64_wordsVal_write_top _ _ _ _ _ (by omega_using [hA, hj, hnw]), wordsVal_succ_top s.mem B dA j,
      wordsVal_succ_top s.mem B dQ j, hq, hx, j6, Nat.mul_succ, Nat.pow_add]
    rw [j6] at km
    generalize (a * q + x + t.gpr .s1).toNat = lo at km ⊢
    generalize (BitVec.ofNat 64 (a.toNat * q.toNat / 2 ^ 64) + (if a * q + x < x then 1 else 0) +
      (if a * q + x + t.gpr .s1 < t.gpr .s1 then 1 else 0)).toNat = c' at km ⊢
    generalize (t.gpr .s1).toNat = c at km jv
    generalize 2 ^ (64 * j) = P at jv ⊢
    generalize wordsVal t.mem B dA j = Wt at jv ⊢
    generalize wordsVal s.mem B dA j = Ws at jv ⊢
    generalize wordsVal s.mem B dQ j = Qs at jv ⊢
    have := congrArg (P * ·) km
    grind

/-- The registers a row writes. -/
def rowRegs : List Reg := [.a0, .a1, .a3, .a6, .s0, .s1, .s2, .s3, .t3, .t4, .t5]

/-- A row, `p_i` at `dP + 8 i` (`a0`), the product's words from `i` at `dA`
(`a1`), `q`'s `w_q` words (`t1`) in array 5, and the product's word
`i + w_q` (which the row overwrites): `t := t + p_i q` over `w_q + 1`
words, and the next row's pointers and count. -/
theorem row_ok {s : State} {B : Addr} {Z w dP dA wq i : Nat} (hs : Scr s B Z)
    (h0 : s.gpr .a0 = off B (dP + 8 * i)) (h1 : s.gpr .a1 = off B dA) (h7 : s.gpr .a7 = off B (slot w 0))
    (h5 : s.gpr .s5 = BitVec.ofNat 64 (8 * (w + 2))) (ht1 : s.gpr .t1 = BitVec.ofNat 64 wq) (hwq : 1 ≤ wq)
    (hwq' : wq < 2 ^ 31) (hP8 : dP % 8 = 0) (hA8 : dA % 8 = 0) (hPZ : dP + 8 * i + 8 ≤ Z)
    (hA : dA + 8 * (wq + 1) ≤ Z) (hQ : slot w 5 + 8 * wq ≤ Z)
    (dAQ : slot w 5 + 8 * wq ≤ dA ∨ dA + 8 * (wq + 1) ≤ slot w 5)
    (dAP : dP + 8 * i + 8 ≤ dA ∨ dA + 8 * (wq + 1) ≤ dP + 8 * i) :
    WP isa (.seq (.block rowHead) (.seq (countLoop .t5 rowWord) (.block rowTail))) s fun t =>
      (wordsVal t.mem B dA (wq + 1) = wordsVal s.mem B dA wq +
          (Mont.word s.mem B (dP + 8 * i)).toNat * wordsVal s.mem B (slot w 5) wq ∧
        Outside B dA (8 * (wq + 1)) s.mem t.mem ∧ t.gpr .a0 = off B (dP + 8 * (i + 1)) ∧
        t.gpr .a1 = off B (dA + 8) ∧ t.gpr .a3 = s.gpr .a3 - BitVec.ofNat 64 1) ∧ Keep rowRegs s t := by
  have hnw := hs.nowrap
  have al := VG.Proof.Bignum.RISCV64.slot_al8 w
  unfold rowHead
  generalize hp : Mont.word s.mem B (dP + 8 * i) = pw
  have rP : s.mem.readW (off B (dP + 8 * i)) 64 = pw := hp
  -- The row's start.
  have head : WP isa (.block (([.load .d .a6 .a0 0, .addi .t3 .a1 0] : List Instr) ++ PublicChecked.base .t4 5)) s
      fun t => (t.gpr .a6 = pw ∧ t.gpr .t3 = off B dA ∧ t.gpr .t4 = off B (slot w 5) ∧ t.mem = s.mem) ∧
        Keep [.a6, .t3, .t4] s t := by
    rw [WP.block_append_iff]
    refine WP.mono (WP.keep [.a6, .t3] (Q := fun t => t.gpr .a6 = pw ∧ t.gpr .t3 = off B dA ∧ t.mem = s.mem)
      (by brun [h0, h1, rP, BitVec.add_zero, hs.ld (show dP + 8 * i + 8 ≤ Z by omega),
        hs.al8 (show dP + 8 * i + 8 ≤ Z by omega) (by omega)]) (by rfl) (by rfl)) fun s₁ ⟨⟨a6, a3, m1⟩, k1⟩ => ?_
    refine WP.mono (Pub.base_ok (rd := .t4) (by decide) ((k1.gpr (by decide)).trans h7)
      ((k1.gpr (by decide)).trans h5) 5) fun s₂ ⟨⟨a4, m2⟩, k2⟩ =>
        ⟨⟨by rw [k2.gpr (by decide), a6], by rw [k2.gpr (by decide), a3], a4, by rw [m2, m1]⟩, (k1.trans k2).mono (by decide)⟩
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono head fun s₂ ⟨⟨a6, a3, a4, m2⟩, k2⟩ => ?_
  refine WP.mono (WP.keep [.t5, .s1] (Q := fun t => t.gpr .t5 = BitVec.ofNat 64 wq ∧ t.gpr .s1 = 0 ∧ t.mem = s₂.mem)
    (by brun [(k2.gpr (by decide)).trans ht1, BitVec.add_zero, exec_li_zero']; rfl) (by rfl) (by rfl))
    fun s₃ ⟨⟨a5, a1', m3⟩, k3⟩ => ?_
  have k23 := k2.trans k3
  have I0 : RowI s₃ B dA (slot w 5) pw 0 s₃ := ⟨by rw [k3.gpr (by decide), a3]; rfl,
    by rw [k3.gpr (by decide), a4]; rfl, by rw [k3.gpr (by decide), a6], Outside.refl _ _ _ _,
    by simp [wordsVal, a1'], Keep.refl _ _⟩
  have hs₃ := hs.congr k23.2.2
  -- The words.
  refine WP.seq (WP.mono (wp_countdown (cnt := .t5) (N := wq) (by omega) (by omega) (RowI s₃ B dA (slot w 5) pw)
    (fun j hj t hI _ => rowWord_ok hs₃ hA8 (al 5) (by omega) hQ (by omega) hj hI) I0 a5)
    fun t ⟨j3, _, _, jout, jv, jk⟩ => ?_)
  have k3t := k23.trans jk
  have hst := hs.congr k3t.2.2
  -- The carry, and the next row.
  refine WP.mono (WP.keep [.a0, .a1, .a3] (Q := fun t' =>
      t'.mem = t.mem.writeW (off B (dA + 8 * wq)) (t.gpr .s1) ∧ t'.gpr .a0 = s.gpr .a0 + BitVec.ofNat 64 8 ∧
        t'.gpr .a1 = s.gpr .a1 + BitVec.ofNat 64 8 ∧ t'.gpr .a3 = s.gpr .a3 - BitVec.ofNat 64 1) (by
    unfold rowTail
    brun [j3, k3t.gpr (r := .a0) (by decide), k3t.gpr (r := .a1) (by decide), k3t.gpr (r := .a3) (by decide),
      hst.st (show dA + 8 * wq + 8 ≤ Z by omega), hst.al8 (show dA + 8 * wq + 8 ≤ Z by omega) (by omega)])
    (by rfl) (by rfl)) fun u ⟨⟨um, u0, u1, u3⟩, uk⟩ => ⟨⟨?_, ?_, ?_, ?_, u3⟩, (k3t.trans uk).mono (by decide)⟩
  · rw [m3, m2] at jv
    rw [um, fin64_wordsVal_write_top _ _ _ _ _ (by omega), jv]
  · rw [m3, m2] at jout
    rw [um]
    exact (jout.mono (Nat.le_refl _) (by omega)).trans
      ((writeW_outside t.mem B (d := dA + 8 * wq) _ (by omega)).mono (by omega) (by omega))
  · rw [u0, h0, off_add, show dP + 8 * i + 8 = dP + 8 * (i + 1) by omega]
  · rw [u1, h1, off_add]

/-! ## The rows -/

/-- What the rows keep after `i` rows, from `s`: the pointers, the product
`p_{<i} q` over the first `i + w_q` words of array 6, and memory elsewhere. -/
def RowsI (s : State) (B : Addr) (w wq : Nat) (i : Nat) (t : State) : Prop :=
  t.gpr .a0 = off B (slot w 4 + 8 * i) ∧ t.gpr .a1 = off B (slot w 6 + 8 * i) ∧
    wordsVal t.mem B (slot w 6) (i + wq) = wordsVal s.mem B (slot w 4) i * wordsVal s.mem B (slot w 5) wq ∧
    Outside B (slot w 6) (8 * (i + wq)) s.mem t.mem ∧ Keep rowRegs s t

/-- `rows`, from array 6's first `w_p + w_q ≤ w` words zero, `p` (array 4)
at `a0` and the product (array 6) at `a1`, `w_p` in `a3` and `w_q` in `t1`:
array 6's first `w_p + w_q` words := `p_{<w_p} q_{<w_q}`, changing only
them. -/
theorem rows_ok {s : State} {B : Addr} {Z w wp wq : Nat} (hs : Scr s B Z)
    (h0 : s.gpr .a0 = off B (slot w 4)) (h1 : s.gpr .a1 = off B (slot w 6)) (h7 : s.gpr .a7 = off B (slot w 0))
    (h5 : s.gpr .s5 = BitVec.ofNat 64 (8 * (w + 2))) (h3 : s.gpr .a3 = BitVec.ofNat 64 wp)
    (ht1 : s.gpr .t1 = BitVec.ofNat 64 wq) (hwp : 1 ≤ wp) (hwq : 1 ≤ wq) (hpq : wp + wq ≤ w) (hw' : w < 2 ^ 31)
    (hZ : slot w 8 ≤ Z) (hz : ∀ k < w, Mont.word s.mem B (slot w 6 + 8 * k) = 0) :
    WP isa rows s fun t =>
      (wordsVal t.mem B (slot w 6) (wp + wq) = wordsVal s.mem B (slot w 4) wp * wordsVal s.mem B (slot w 5) wq ∧
        Outside B (slot w 6) (8 * (wp + wq)) s.mem t.mem) ∧ Keep rowRegs s t := by
  have hnw := hs.nowrap
  have e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  have e4 := e 4; have e5 := e 5; have e6 := e 6; have e7 := e 7; have e8 := e 8
  have hh : hdrBytes = 256 := rfl
  have al := VG.Proof.Bignum.RISCV64.slot_al8 w
  have I0 : RowsI s B w wq 0 s := ⟨by rw [h0]; rfl, by rw [h1]; rfl,
    by rw [Nat.zero_add, wordsVal_zero (fun k hk => hz k (by omega_using [hpq, hk]))]; simp [wordsVal], Outside.refl _ _ _ _,
    Keep.refl _ _⟩
  refine WP.mono (wp_countdown (cnt := .a3) (N := wp) (by omega_using [hpq, hw']) (by omega_using [hwp]) (RowsI s B w wq)
    (fun i hi t ⟨j0, j1, jv, jout, jk⟩ _ => ?_) I0 h3) fun t ⟨_, _, tv, tout, tk⟩ => ⟨⟨tv, tout⟩, tk⟩
  have hst := hs.congr jk.2.2
  refine WP.mono (row_ok (dP := slot w 4) (dA := slot w 6 + 8 * i) (i := i) (wq := wq) hst j0
    (by rw [j1]) ((jk.gpr (by decide)).trans h7) ((jk.gpr (by decide)).trans h5) ((jk.gpr (by decide)).trans ht1)
    hwq (by omega_using [hpq, hw']) (al 4) (by have := al 6; omega_using [this]) (by omega_using [hpq, hZ, e4, e8, hi]) (by omega_using [hpq, hZ, e6, e8, hi]) (by omega_using [hpq, hZ, e5, e8]) (by omega_using [hpq, e5, e6]) (by omega_using [e4, e6]))
    fun t' ⟨⟨rv, rout, r0, r1, r3⟩, rk⟩ => ⟨⟨r0, by rw [r1, show slot w 6 + 8 * i + 8 = slot w 6 + 8 * (i + 1) by omega_using []], ?_, ?_, Keep.trans' jk rk⟩, r3⟩
  · have wP : Mont.word t.mem B (slot w 4 + 8 * i) = Mont.word s.mem B (slot w 4 + 8 * i) :=
      jout.word (by omega_using [hpq, e4, e6, hi]) (by omega_using [hpq, hw', e4, hh, hi])
    have wQ : wordsVal t.mem B (slot w 5) wq = wordsVal s.mem B (slot w 5) wq :=
      Outside.wordsVal jout (by omega_using [hpq, e5, e6]) (by omega_using [hpq, hw', e5, hh])
    have wL : wordsVal t'.mem B (slot w 6) i = wordsVal t.mem B (slot w 6) i :=
      Outside.wordsVal rout (by omega_using []) (by omega_using [hpq, hw', e6, hh, hi])
    have a1 := wordsVal_app t'.mem B (slot w 6) i (wq + 1)
    have a2 := wordsVal_app t.mem B (slot w 6) i wq
    rw [show i + (wq + 1) = i + 1 + wq by omega_using [], wL, rv, wP, wQ] at a1
    rw [a1, wordsVal_succ_top s.mem B (slot w 4) i]
    rw [a2] at jv
    generalize 2 ^ (64 * i) = P at jv ⊢
    generalize wordsVal t.mem B (slot w 6) i = A at jv ⊢
    generalize wordsVal t.mem B (slot w 6 + 8 * i) wq = Bv at jv ⊢
    generalize (Mont.word s.mem B (slot w 4 + 8 * i)).toNat = pi
    generalize wordsVal s.mem B (slot w 5) wq = Q at jv ⊢
    generalize wordsVal s.mem B (slot w 4) i = Pi at jv ⊢
    grind
  · exact (jout.mono (Nat.le_refl _) (by omega_using [])).trans (rout.mono (by omega_using []) (by omega_using []))

/-! ## `p q = n` -/

/-- `checkPQs` is a check of `p q = n` for `Crt.checksWith`, from `s` with
`w_p` in `a3` and `w_q` in `t1`, `p` and `q` (arrays 4 and 5) of `w_p` and
`w_q` words, `w_p + w_q ≤ W`, and the words `W` of arrays 6 and 1 zero. -/
theorem checkPQs_ok {s : State} {S : Addr} {Z w wp wq : Nat} (hs : Scr s S Z) (hZ : slot w 8 ≤ Z)
    (hw' : w < 2 ^ 31) (h3 : s.gpr .a3 = BitVec.ofNat 64 wp) (ht1 : s.gpr .t1 = BitVec.ofNat 64 wq)
    (hwp : 1 ≤ wp) (hwq : 1 ≤ wq) (hpq : wp + wq ≤ w)
    (hp : wordsVal s.mem S (slot w 4) w = wordsVal s.mem S (slot w 4) wp)
    (hq : wordsVal s.mem S (slot w 5) w = wordsVal s.mem S (slot w 5) wq)
    (h6top : Mont.word s.mem S (slot w 6 + 8 * w) = 0) (h1top : Mont.word s.mem S (slot w 1 + 8 * w) = 0) :
    Crt.PQOk checkPQs S Z w s := by
  intro t ht t7 tra t5 t0 tk to
  have hnw := hs.nowrap
  have e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  have e0 := e 0; have e1 := e 1; have e3 := e 3; have e4 := e 4; have e5 := e 5; have e6 := e 6
  have e7 := e 7; have e8 := e 8
  have hh : hdrBytes = 256 := rfl
  have al := VG.Proof.Bignum.RISCV64.slot_al8 w
  have t3' : t.gpr .a3 = BitVec.ofNat 64 wp := (tk.gpr (by decide)).trans h3
  have t1' : t.gpr .t1 = BitVec.ofNat 64 wq := (tk.gpr (by decide)).trans ht1
  have wv : ∀ {j}, j ≠ 3 → j < 8 → ∀ k ≤ w, wordsVal t.mem S (slot w j) k = wordsVal s.mem S (slot w j) k :=
    fun hj hj' k hk => Outside.wordsVal to (by have := VG.Proof.Bignum.slot_sep (w := w) hj; omega_using [hk, this])
      (by have := VG.Proof.Bignum.slot_le (w := w) hj'; omega_using [hZ, hnw, hk, this])
  unfold checkPQs
  -- Array 6 := 0.
  refine WP.seq (WP.mono (Pub.base_ok (rd := .t3) (by decide) t7 t5 6) fun u₁ ⟨⟨b3, m1⟩, k1⟩ => ?_)
  refine WP.seq (WP.mono (zeroWords_ok (hs.congr (tk.trans k1).2.2) b3 ((k1.gpr (by decide)).trans t0)
    (by omega_using [hwp, hpq]) hw' (al 6) (by omega_using [hZ, e6, e8])) fun u₂ ⟨⟨_, z2, o2⟩, k2⟩ => ?_)
  have k12 := k1.trans k2
  -- The pointers.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .a0) (by decide) ((k12.gpr (by decide)).trans t7)
    ((k12.gpr (by decide)).trans t5) 4) fun u₃ ⟨⟨b0, m3⟩, k3⟩ => ?_
  refine WP.mono (Pub.base_ok (rd := .a1) (by decide) ((k3.gpr (by decide)).trans ((k12.gpr (by decide)).trans t7))
    ((k3.gpr (by decide)).trans ((k12.gpr (by decide)).trans t5)) 6) fun u₄ ⟨⟨b1, m4⟩, k4⟩ => ?_
  have k14 := k12.trans (k3.trans k4)
  have m24 : u₄.mem = u₂.mem := by rw [m4, m3]
  -- The rows.
  refine WP.seq (WP.mono (rows_ok (wp := wp) (wq := wq) (hs.congr (tk.trans k14).2.2) (by rw [k4.gpr (by decide), b0])
    b1 ((k14.gpr (by decide)).trans t7) ((k14.gpr (by decide)).trans t5) ((k14.gpr (by decide)).trans t3')
    ((k14.gpr (by decide)).trans t1') hwp hwq hpq hw' hZ (fun k hk => by rw [m24]; exact z2 k hk))
    fun u₅ ⟨⟨r6, o5⟩, k5⟩ => ?_)
  have k15 := k14.trans k5
  have O : Outside S (slot w 6) (8 * w) t.mem u₅.mem := by
    rw [m1] at o2
    exact o2.trans (by rw [m24] at o5; exact o5.mono (Nat.le_refl _) (by omega_using [hpq]))
  -- `p q = n`?
  refine WP.mono (Crt.pqEq_ok (hs.congr (tk.trans k15).2.2) (by omega_using [hwp, hpq]) hw' hZ ((k15.gpr (by decide)).trans t7)
    ((k15.gpr (by decide)).trans tra) ((k15.gpr (by decide)).trans t5) ((k15.gpr (by decide)).trans t0)
    ((Mont.Outside.word O (by omega_using []) (by omega_using [hw', e6, hh])).trans ((Mont.Outside.word to (by omega_using [e3, e6]) (by omega_using [hw', e6, hh])).trans h6top))
    ((Mont.Outside.word O (by omega_using [e1, e6]) (by omega_using [hw', e1, hh])).trans ((Mont.Outside.word to (by omega_using [e1, e3]) (by omega_using [hw', e1, hh])).trans h1top)))
    fun u ⟨⟨u9, uo, u7⟩, uk⟩ => ⟨⟨?_, ?_, u7⟩, (k15.trans uk).mono (by decide)⟩
  · -- The product over `W` words.
    have hz : ∀ k < w - (wp + wq), Mont.word u₅.mem S (slot w 6 + 8 * (wp + wq) + 8 * k) = 0 := fun k hk => by
      rw [Mont.Outside.word o5 (by omega_using []) (by omega_using [hw', e6, hh, hk]), m24, show slot w 6 + 8 * (wp + wq) + 8 * k = slot w 6 + 8 * (wp + wq + k)
        by omega_using []]
      exact z2 _ (by omega_using [hk])
    have hP : wordsVal u₅.mem S (slot w 6) w = wordsVal s.mem S (slot w 4) w * wordsVal s.mem S (slot w 5) w := by
      have a := wordsVal_app u₅.mem S (slot w 6) (wp + wq) (w - (wp + wq))
      rw [show wp + wq + (w - (wp + wq)) = w by omega_using [hpq], wordsVal_zero hz, Nat.mul_zero, Nat.add_zero, r6, m24,
        Outside.wordsVal o2 (by omega_using [hpq, e4, e6]) (by omega_using [hw', hpq, e4, hh]), Outside.wordsVal o2 (by omega_using [hpq, e5, e6]) (by omega_using [hw', hpq, e5, hh]), m1,
        wv (by decide) (by decide) wp (by omega_using [hpq]), wv (by decide) (by decide) wq (by omega_using [hpq])] at a
      rw [a, hp, hq]
    have h1 : wordsVal u₅.mem S (slot w 1) w = wordsVal s.mem S (slot w 1) w := by
      rw [Outside.wordsVal O (by omega_using [e1, e6]) (by omega_using [hw', e1, hh]), wv (by decide) (by decide) w (Nat.le_refl _)]
    rw [u9, hP, h1, k15.gpr (r := .s9) (by decide)]
  · intro x hx
    have hx3 : ofs S x < slot w 3 ∨ slot w 3 + 8 * w ≤ ofs S x := by have := hx 3 (by simp); omega_using [this]
    have hx6 : ofs S x < slot w 6 ∨ slot w 6 + 8 * w ≤ ofs S x := by have := hx 6 (by simp); omega_using [this]
    rw [uo x hx3, O x hx6]

end VG.Proof.Bignum.RISCV64.PrivPre
