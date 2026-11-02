module

public import VerifiedGarbage.Proof.Bignum.RISCV64.CrtSave
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
import VerifiedGarbage.Proof.Bignum.RISCV64.PubLoad
import VerifiedGarbage.Proof.Bignum.RISCV64.MontCore
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The RSA private-key operation on RISC-V: loading `X`

* `onesWords_ok`: `w` words := all ones, so array 0 holds `M = 2^(64 w) - 1`.
* `loadArr_ok`: a number's bytes, most significant first, into array `j`
  (`Precompute.loadN`), its word `w` zero, and `a7` back to array 0.
* `loadX_ok`: `X`'s arrays from the header's pointers and lengths: `M` (0),
  `n` (1), `p` (4), `q` (5), the input (6) and `qInv` (7).
-/

@[expose] public section

namespace VG.Proof.Bignum.RISCV64.Crt

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.RISCV64
  VG.Impl.Bignum.RISCV64.Crt
open VG.Proof.Bignum.RISCV64
open VG.Proof.Bignum (slot Arrays)

/-! ## All ones -/

/-- `w` words all ones are `2^(64 w) - 1`. -/
theorem wordsVal_ones (m : Mem) (B : Addr) (d : Nat) :
    ∀ w, (∀ i < w, Mont.word m B (d + 8 * i) = BitVec.allOnes 64) → wordsVal m B d w = 2 ^ (64 * w) - 1
  | 0, _ => by simp [wordsVal]
  | w + 1, h => by
    rw [Mont.wordsVal_succ_top, wordsVal_ones m B d w fun i hi => h i (by omega_arith), h w (by omega_arith),
      BitVec.toNat_allOnes, Mont.pow64_succ]
    have := Nat.one_le_two_pow (n := 64 * w)
    rw [Nat.mul_sub, Nat.mul_one, Nat.mul_comm]
    omega_arith

/-- `onesWords`, at `d` of `P` (`t3`) with `w` in `t0`: the `w` words := all
ones. -/
theorem onesWords_ok {s : State} {P : Addr} {Z d w : Nat} (hs : Scr s P Z)
    (h3 : s.gpr .t3 = Mont.off P d) (h0 : s.gpr .t0 = BitVec.ofNat 64 w) (hw : 1 ≤ w)
    (hw' : w < 2 ^ 31) (hd8 : d % 8 = 0) (hZ : d + 8 * w ≤ Z) :
    WP isa onesWords s fun s' =>
      (wordsVal s'.mem P d w = 2 ^ (64 * w) - 1 ∧
        (∀ i < w, Mont.word s'.mem P (d + 8 * i) = BitVec.allOnes 64) ∧ Mont.Outside P d (8 * w) s.mem s'.mem) ∧
        Keep [.s0, .t3, .t5] s s' := by
  have hnw := hs.nowrap
  unfold onesWords
  refine WP.seq ?_
  have hpre : WP isa (.block [.addi .t5 .t0 0, .li .s0 (-1)]) s fun s₁ =>
      (s₁.gpr .t5 = BitVec.ofNat 64 w ∧ s₁.gpr .s0 = BitVec.allOnes 64 ∧ s₁.gpr .t3 = Mont.off P d ∧
        s₁.mem = s.mem) ∧ Keep [.s0, .t5] s s₁ := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [exec_li, add_ofNat_zero, h0, h3, BitVec.add_zero]
    rfl
  refine WP.mono hpre fun s₁ ⟨⟨i5, i0, i3, im⟩, k₁⟩ => ?_
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .t3 = Mont.off P (d + 8 * i) ∧ t.gpr .s0 = BitVec.allOnes 64 ∧ Mont.Outside P d (8 * i) s.mem t.mem ∧
      (∀ k < i, Mont.word t.mem P (d + 8 * k) = BitVec.allOnes 64) ∧ Keep [.s0, .t3, .t5] s t
  refine WP.mono (wp_countdown (body := .block ([.store .d .s0 .t3 0, .addi .t3 .t3 8] ++
      ([.addi .t5 .t5 (-1)] : List Instr))) (cnt := .t5) (N := w) (by omega_arith) (by omega_arith) Inv
    (fun i hi t ⟨j3, j0, jout, jz, jk⟩ hc => ?_)
    ⟨by rw [i3]; rfl, i0, by rw [← im]; exact Mont.Outside.refl _ _ _ _, fun _ h => absurd h (by omega_arith),
      k₁.mono (by decide)⟩ i5) fun t ⟨_, _, tout, tz, tk⟩ => ⟨⟨wordsVal_ones _ _ _ w tz, tz, tout⟩, tk⟩
  have hst : WP isa (.block [.store .d .s0 .t3 0, .addi .t3 .t3 8, .addi .t5 .t5 (-1)]) t
      fun t' => t' = ((({ t with mem := t.mem.writeW (Mont.off P (d + 8 * i)) (BitVec.allOnes 64) } : State).write
        .t3 (Mont.off P (d + 8 * i + 8))).write .t5 (t.gpr .t5 - BitVec.ofNat 64 1)) := by
    brun [add_ofNat_zero, j3, j0, (hs.congr jk.2.2).st (show d + 8 * i + 8 ≤ Z by omega_arith),
      (hs.congr jk.2.2).al8 (show d + 8 * i + 8 ≤ Z by omega_arith) (by omega_arith)]
  refine WP.mono hst fun t' e => ?_
  subst e
  have hw := Mont.writeW_outside t.mem P (d := d + 8 * i) (BitVec.allOnes 64) (by omega_arith)
  refine ⟨⟨by gsimp; rw [show d + 8 * i + 8 = d + 8 * (i + 1) by omega_arith], by gsimp; exact j0, ?_, ?_, ?_⟩,
    by gsimp⟩
  · gsimp; exact (jout.mono (Nat.le_refl _) (by omega_arith)).trans (hw.mono (by omega_arith) (by omega_arith))
  · intro k hk
    gsimp
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · rw [hw.word (by omega_arith) (by omega_arith)]; exact jz k hk
    · exact Mont.word_writeW_self _ _ _ _
  · exact Keep.trans' jk ((((Keep.mem _ _).trans (Keep.write _ _ _)).trans (Keep.write _ _ _)).mono (by decide))

/-! ## A number into an array -/

/-- A byte buffer of `len` bytes at `X`: readable, apart from the working
space's `Z` bytes at `S`. -/
structure Buf (s : State) (S X : Addr) (Z len : Nat) : Prop where
  rd : ∀ i < len, InRegions (s.rd ++ s.wr) (Mont.off X i) 1
  sep : ∀ i < len, ∀ x, ofs S x < Z → Mont.off X i ≠ x

theorem Buf.congr {s t : State} {S X : Addr} {Z len : Nat} (h : Buf s S X Z len) (hrd : t.rd = s.rd)
    (hwr : t.wr = s.wr) : Buf t S X Z len := ⟨by rw [hrd, hwr]; exact h.rd, h.sep⟩

/-- `loadArr j`: the `k` bytes at `s7` (`k` in `s8`) into array `j`,
its Mont.word `w` := 0; `a7` back to array 0 (`ra`). -/
theorem loadArr_ok {s : State} {B X : Addr} {Z w k j : Nat} (hs : Scr s B Z) (hj8 : j < 8)
    (h7 : s.gpr .a7 = Mont.off B (slot w 0)) (hra : s.gpr .ra = Mont.off B (slot w 0))
    (h5 : s.gpr .s5 = BitVec.ofNat 64 (8 * (w + 2))) (h0 : s.gpr .t0 = BitVec.ofNat 64 w)
    (hs7 : s.gpr .s7 = Mont.off X 0) (hs8 : s.gpr .s8 = BitVec.ofNat 64 k)
    (hk : 1 ≤ k) (hkw : k ≤ 8 * w) (hw' : w < 2 ^ 31) (hZ : slot w 8 ≤ Z) (hX : Buf s B X Z k) :
    WP isa (loadArr j) s fun t =>
      (wordsVal t.mem B (slot w j) w = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem X k) ∧
        Mont.word t.mem B (slot w j + 8 * w) = 0 ∧ Mont.Outside B (slot w j) (8 * (w + 1)) s.mem t.mem ∧
        t.gpr .a7 = Mont.off B (slot w 0)) ∧
      Keep [.a0, .a7, .s0, .t3, .t4, .t5] s t := by
  have hnw := hs.nowrap
  have e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  have ej := e j; have e8 := e 8
  have hh : hdrBytes = 256 := rfl
  have hj8' : slot w j + 8 * (w + 2) ≤ slot w 8 := VG.Proof.Bignum.slot_le hj8
  have alj : slot w j % 8 = 0 := slot_al w j
  unfold loadArr
  refine WP.seq (WP.mono (Pub.base_ok (rd := .a7) (by decide) h7 h5 j) fun s₁ ⟨⟨a7', m1⟩, k1⟩ => ?_)
  refine WP.seq (WP.mono (loadN_ok (dA := slot w j) (hs.congr k1.2.2) a7'
    ((k1.gpr (by decide)).trans hs7) ((k1.gpr (by decide)).trans hs8) ((k1.gpr (by decide)).trans h0) hk hkw hw'
    (by omega_arith) alj (by omega_arith) (by rw [k1.2.1, k1.2.2]; exact hX.rd) hX.sep)
    fun s₃ ⟨hv, out₃, k3⟩ => ?_)
  rw [m1] at hv out₃
  have k13 := k1.trans k3
  have a7'' : s₃.gpr .a7 = Mont.off B (slot w j) := (k3.gpr (by decide)).trans a7'
  have e16 : Mont.off B (slot w j + 8 * (w + 2)) - BitVec.ofNat 64 16 = Mont.off B (slot w j + 8 * w) := by
    rw [off_sub B (show 16 ≤ slot w j + 8 * (w + 2) by omega_arith),
      show slot w j + 8 * (w + 2) - 16 = slot w j + 8 * w by omega_arith]
  refine WP.mono (WP.keep [.t3, .s0, .a7] (Q := fun t =>
    t.mem = s₃.mem.writeW (Mont.off B (slot w j + 8 * w)) (0 : BitVec 64) ∧ t.gpr .a7 = Mont.off B (slot w 0))
    ?_ (by rfl) (by rfl)) fun t ⟨⟨tm, t7⟩, k4⟩ => ⟨⟨?_, ?_, ?_, t7⟩, (k13.trans k4).mono (by decide)⟩
  · brun [a7'', (k13.gpr (r := .s5) (by decide)).trans h5, (k13.gpr (r := .ra) (by decide)).trans hra, off_add,
      e16, exec_li, add_ofNat_zero, (hs.congr k13.2.2).st (show slot w j + 8 * w + 8 ≤ Z by omega_arith),
      (hs.congr k13.2.2).al8 (show slot w j + 8 * w + 8 ≤ Z by omega_arith) (by omega_arith)]
    rfl
  · rw [tm, Mont.Outside.wordsVal (fun x hx => Mont.writeW_outside s₃.mem B (d := slot w j + 8 * w) 0 (by omega_arith) x hx)
      (by omega_arith) (by omega_arith)]
    exact hv
  · rw [tm]; exact Mont.word_writeW_self _ _ _ _
  · rw [tm]
    exact (Mont.Outside.mono out₃ (Nat.le_refl _) (by omega_arith)).trans
      (Mont.Outside.mono (Mont.writeW_outside s₃.mem B (d := slot w j + 8 * w) 0 (by omega_arith)) (by omega_arith)
        (by omega_arith))

/-! ## `X`'s arrays -/

/-- A buffer's bytes are those of a memory that changed only in the working
space. -/
theorem bytesAt_out {B I : Addr} {Z o n k : Nat} {m m' : Mem} (h : Mont.Outside B o n m m') (hn : o + n ≤ Z)
    (hsep : ∀ i < k, ∀ x, ofs B x < Z → Mont.off I i ≠ x) :
    Spec.Rsa.bytesAt m' I k = Spec.Rsa.bytesAt m I k := by
  rw [VG.Proof.Bignum.bytesAt_eq, VG.Proof.Bignum.bytesAt_eq]
  refine List.map_congr_left fun i hi => h _ ?_
  have hi := List.mem_range.mp hi
  by_contra hc
  exact hsep i hi (I + BitVec.ofNat 64 i) (by simp only [VG.Proof.Bignum.ofs, Mont.ofs] at hc ⊢; omega) rfl

theorem arr_val {m m' : Mem} {B : Addr} {w i j : Nat} (h : Mont.Outside B (slot w i) (8 * (w + 1)) m m')
    (hij : i ≠ j) (hj : j < 8) (hn : B.toNat + slot w 8 ≤ 2 ^ 64) :
    wordsVal m' B (slot w j) w = wordsVal m B (slot w j) w :=
  h.wordsVal (by have := VG.Proof.Bignum.slot_sep (w := w) hij; omega_arith)
    (by have := VG.Proof.Bignum.slot_le (w := w) hj; omega_arith)

theorem arr_word {m m' : Mem} {B : Addr} {w i j q : Nat} (h : Mont.Outside B (slot w i) (8 * (w + 1)) m m')
    (hij : i ≠ j) (hj : j < 8) (hq : q ≤ w) (hn : B.toNat + slot w 8 ≤ 2 ^ 64) :
    Mont.word m' B (slot w j + 8 * q) = Mont.word m B (slot w j + 8 * q) :=
  h.word (by have := VG.Proof.Bignum.slot_sep (w := w) hij; omega_arith)
    (by have := VG.Proof.Bignum.slot_le (w := w) hj; omega_arith)

/-- The address and length of a buffer from the header (words `oA`, `oL`),
then the buffer into `X`'s array `j`. -/
theorem loadOne_ok {s : State} {BX A : Addr} {Z w L j oA oL : Nat} (hs : Scr s BX Z) (hZ : slot w 8 ≤ Z)
    (hj : j < 8) (hw' : w < 2 ^ 31) (h6 : s.gpr .s6 = Mont.off BX 0) (h7 : s.gpr .a7 = Mont.off BX (slot w 0))
    (hra : s.gpr .ra = Mont.off BX (slot w 0)) (h5 : s.gpr .s5 = BitVec.ofNat 64 (8 * (w + 2)))
    (h0 : s.gpr .t0 = BitVec.ofNat 64 w)
    (hoA : oA + 8 ≤ 256 ∧ oA % 8 = 0) (hoL : oL + 8 ≤ 256 ∧ oL % 8 = 0)
    (hA : Mont.word s.mem BX oA = Mont.off A 0) (hLw : Mont.word s.mem BX oL = BitVec.ofNat 64 L) (hL : 1 ≤ L)
    (hLw' : L ≤ 8 * w) (hX : Buf s BX A Z L) :
    WP isa (.seq (.block [.load .d .s7 .s6 oA, .load .d .s8 .s6 oL]) (loadArr j)) s fun t =>
      (wordsVal t.mem BX (slot w j) w = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem A L) ∧
        Mont.word t.mem BX (slot w j + 8 * w) = 0 ∧ Mont.Outside BX (slot w j) (8 * (w + 1)) s.mem t.mem ∧
        t.gpr .a7 = Mont.off BX (slot w 0)) ∧
      Keep [.a0, .a7, .s0, .s7, .s8, .t3, .t4, .t5] s t := by
  have hn := hs.nowrap
  have e8 : slot w 8 = 256 + 8 * (8 * (w + 2)) := rfl
  refine WP.seq (WP.mono (WP.keep [.s7, .s8] (Q := fun t => t.gpr .s7 = Mont.off A 0 ∧
    t.gpr .s8 = BitVec.ofNat 64 L ∧ t.mem = s.mem) (by
      brun [h6, Nat.zero_add, hs.ld (show oA + 8 ≤ Z by omega_arith), hs.al8 (show oA + 8 ≤ Z by omega_arith) hoA.2,
        hs.ld (show oL + 8 ≤ Z by omega_arith), hs.al8 (show oL + 8 ≤ Z by omega_arith) hoL.2,
        show oA < 2048 by omega_arith, show oL < 2048 by omega_arith, hA, hLw]) (by rfl) (by rfl))
    fun s₁ ⟨⟨a7', a8, m1⟩, k1⟩ => ?_)
  refine WP.mono (loadArr_ok (hs.congr k1.2.2) hj ((k1.gpr (by decide)).trans h7)
    ((k1.gpr (by decide)).trans hra) ((k1.gpr (by decide)).trans h5) ((k1.gpr (by decide)).trans h0) a7' a8
    hL hLw' hw' hZ (hX.congr k1.2.1 k1.2.2))
    fun t ⟨⟨v, tp, o, t7⟩, k2⟩ => ⟨⟨by rw [v, m1], tp, by rw [← m1]; exact o, t7⟩, (k1.trans k2).mono (by decide)⟩

/-- The registers `loadX` writes. -/
def loadXRegs : List Reg := [.a0, .a7, .s0, .s7, .s8, .t3, .t4, .t5]

/-- A frame within the arrays is one of all of them. -/
theorem out_arrs {m m' : Mem} {B : Addr} {w o n : Nat} (h : Mont.Outside B o n m m') (ho : 256 ≤ o)
    (hn : o + n ≤ slot w 8) : Mont.Outside B 256 (slot w 8 - 256) m m' :=
  h.mono ho (by omega_arith)

/-- Two programs then a third, regrouped. -/
theorem wp_reassoc2 {a b c : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa (.seq (.seq a b) c) s Q) : WP isa (.seq a (.seq b c)) s Q := by
  obtain ⟨t, s', hx, hq⟩ := h
  cases hx with
  | seq h1 h2 =>
    cases h1 with
    | seq ha hb => exact ⟨_, _, .seq ha (.seq hb h2), hq⟩

/-- `loadX`, in `X` (`w` words, at `BX`, its header holding the buffers'
addresses and lengths): `M = 2^(64 w) - 1` in array 0, then `n`, `p`, `q`,
the input and `qInv` in arrays 1, 4, 5, 6 and 7. -/
theorem loadX_ok {s : State} {BX Na Pa Qa Ia QIa : Addr} {Z w k pL qL : Nat} (hs : Scr s BX Z)
    (hZ : slot w 8 ≤ Z) (hw1 : 1 ≤ w) (hw' : w < 2 ^ 31) (h6 : s.gpr .s6 = Mont.off BX 0)
    (h7 : s.gpr .a7 = Mont.off BX (slot w 0)) (hra : s.gpr .ra = Mont.off BX (slot w 0))
    (h5 : s.gpr .s5 = BitVec.ofNat 64 (8 * (w + 2))) (h0 : s.gpr .t0 = BitVec.ofNat 64 w)
    (hNa : Mont.word s.mem BX oN = Mont.off Na 0) (hK : Mont.word s.mem BX oNLen = BitVec.ofNat 64 k)
    (hPa : Mont.word s.mem BX oP = Mont.off Pa 0) (hPL : Mont.word s.mem BX oPLen = BitVec.ofNat 64 pL)
    (hQa : Mont.word s.mem BX oQ = Mont.off Qa 0) (hQL : Mont.word s.mem BX oQLen = BitVec.ofNat 64 qL)
    (hIa : Mont.word s.mem BX oIn = Mont.off Ia 0) (hQIa : Mont.word s.mem BX oQInv = Mont.off QIa 0)
    (hk : 1 ≤ k) (hkw : k ≤ 8 * w) (hp : 1 ≤ pL) (hpw : pL ≤ 8 * w) (hq : 1 ≤ qL) (hqw : qL ≤ 8 * w)
    (bN : Buf s BX Na Z k) (bP : Buf s BX Pa Z pL) (bQ : Buf s BX Qa Z qL) (bI : Buf s BX Ia Z k)
    (bQI : Buf s BX QIa Z pL) :
    WP isa loadX s fun t =>
      (wordsVal t.mem BX (slot w 0) w = 2 ^ (64 * w) - 1 ∧ Mont.word t.mem BX (slot w 0) = BitVec.allOnes 64 ∧
        wordsVal t.mem BX (slot w 1) w = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Na k) ∧
        wordsVal t.mem BX (slot w 4) w = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Pa pL) ∧
        wordsVal t.mem BX (slot w 5) w = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Qa qL) ∧
        wordsVal t.mem BX (slot w 6) w = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Ia k) ∧
        wordsVal t.mem BX (slot w 7) w = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem QIa pL) ∧
        Mont.word t.mem BX (slot w 1 + 8 * w) = 0 ∧ Mont.word t.mem BX (slot w 4 + 8 * w) = 0 ∧
        Mont.word t.mem BX (slot w 5 + 8 * w) = 0 ∧ Mont.word t.mem BX (slot w 6 + 8 * w) = 0 ∧
        Mont.word t.mem BX (slot w 7 + 8 * w) = 0 ∧ Mont.Outside BX 256 (slot w 8 - 256) s.mem t.mem ∧
        t.gpr .a7 = Mont.off BX (slot w 0)) ∧ Keep loadXRegs s t := by
  have hn := hs.nowrap
  have e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  have e0 := e 0; have e1 := e 1; have e4 := e 4; have e5 := e 5; have e6 := e 6; have e7 := e 7
  have e8 := e 8
  have hh : hdrBytes = 256 := rfl
  have hn8 : BX.toNat + slot w 8 ≤ 2 ^ 64 := by omega_arith
  have hd : ∀ {m m' : Mem}, Mont.Outside BX 256 (slot w 8 - 256) m m' → ∀ d, d + 8 ≤ 256 →
      Mont.word m' BX d = Mont.word m BX d :=
    fun h d hd => h.word (Or.inl hd) (by omega_arith)
  have hbz : ∀ {m m' : Mem} {A : Addr} {L : Nat}, Mont.Outside BX 256 (slot w 8 - 256) m m' →
      Buf s BX A Z L → Spec.Rsa.bytesAt m' A L = Spec.Rsa.bytesAt m A L :=
    fun h b => bytesAt_out h (by omega_arith) b.sep
  have bc : ∀ {t : State} {A : Addr} {L : Nat}, Keep loadXRegs s t → Buf s BX A Z L → Buf t BX A Z L :=
    fun k b => b.congr k.2.1 k.2.2
  unfold loadX
  refine WP.seq (WP.mono (WP.keep [.t3] (Q := fun t => t.gpr .t3 = Mont.off BX (slot w 0) ∧ t.mem = s.mem)
    (by brun [h7, BitVec.add_zero]) (by rfl) (by rfl)) fun s₁ ⟨⟨a3, m1⟩, k1⟩ => ?_)
  refine WP.seq (WP.mono (onesWords_ok (hs.congr k1.2.2) a3 ((k1.gpr (by decide)).trans h0) hw1
    (by omega_arith) (slot_al w 0) (by omega_arith)) fun s₂ ⟨⟨h1s, h1w, o2⟩, k2⟩ => ?_)
  have k12 : Keep loadXRegs s s₂ := (k1.trans k2).mono (by decide)
  rw [m1] at o2
  have O2 := out_arrs (w := w) o2 (by omega_arith) (by omega_arith)
  -- `n` into array 1.
  refine wp_reassoc2 (WP.seq (WP.mono (loadOne_ok (j := 1) (A := Na) (L := k) (hs.congr k12.2.2) hZ (by decide)
    hw' ((k12.gpr (by decide)).trans h6) (((k1.trans k2).gpr (by decide)).trans h7)
    ((k12.gpr (by decide)).trans hra) ((k12.gpr (by decide)).trans h5) ((k12.gpr (by decide)).trans h0)
    (by decide) (by decide) (by rw [hd O2 _ (by decide)]; exact hNa) (by rw [hd O2 _ (by decide)]; exact hK) hk hkw
    (bc k12 bN)) fun s₃ ⟨⟨v1, t1, o3, b7⟩, k3⟩ => ?_))
  have k13 : Keep loadXRegs s s₃ := (k12.trans k3).mono (by decide)
  have O3 := out_arrs (w := w) o3 (by omega_arith)
    (by have := VG.Proof.Bignum.slot_le (w := w) (j := 1) (by decide); omega_arith)
  have O23 := O2.trans O3
  -- `p` into array 4.
  refine wp_reassoc2 (WP.seq (WP.mono (loadOne_ok (j := 4) (A := Pa) (L := pL) (hs.congr k13.2.2) hZ (by decide)
    hw' ((k13.gpr (by decide)).trans h6) b7
    ((k13.gpr (by decide)).trans hra) ((k13.gpr (by decide)).trans h5) ((k13.gpr (by decide)).trans h0)
    (by decide) (by decide) (by rw [hd O23 _ (by decide)]; exact hPa) (by rw [hd O23 _ (by decide)]; exact hPL)
    hp hpw (bc k13 bP)) fun s₄ ⟨⟨v4, t4, o4, c7⟩, k4⟩ => ?_))
  have k14 : Keep loadXRegs s s₄ := (k13.trans k4).mono (by decide)
  have O4 := out_arrs (w := w) o4 (by omega_arith)
    (by have := VG.Proof.Bignum.slot_le (w := w) (j := 4) (by decide); omega_arith)
  have O24 := O23.trans O4
  -- `q` into array 5.
  refine wp_reassoc2 (WP.seq (WP.mono (loadOne_ok (j := 5) (A := Qa) (L := qL) (hs.congr k14.2.2) hZ (by decide)
    hw' ((k14.gpr (by decide)).trans h6) c7
    ((k14.gpr (by decide)).trans hra) ((k14.gpr (by decide)).trans h5) ((k14.gpr (by decide)).trans h0)
    (by decide) (by decide) (by rw [hd O24 _ (by decide)]; exact hQa) (by rw [hd O24 _ (by decide)]; exact hQL)
    hq hqw (bc k14 bQ)) fun s₅ ⟨⟨v5, t5, o5, d7⟩, k5⟩ => ?_))
  have k15 : Keep loadXRegs s s₅ := (k14.trans k5).mono (by decide)
  have O5 := out_arrs (w := w) o5 (by omega_arith)
    (by have := VG.Proof.Bignum.slot_le (w := w) (j := 5) (by decide); omega_arith)
  have O25 := O24.trans O5
  -- The input into array 6.
  refine wp_reassoc2 (WP.seq (WP.mono (loadOne_ok (j := 6) (A := Ia) (L := k) (hs.congr k15.2.2) hZ (by decide)
    hw' ((k15.gpr (by decide)).trans h6) d7
    ((k15.gpr (by decide)).trans hra) ((k15.gpr (by decide)).trans h5) ((k15.gpr (by decide)).trans h0)
    (by decide) (by decide) (by rw [hd O25 _ (by decide)]; exact hIa) (by rw [hd O25 _ (by decide)]; exact hK)
    hk hkw (bc k15 bI)) fun s₆ ⟨⟨v6, t6, o6, e7'⟩, k6⟩ => ?_))
  have k16 : Keep loadXRegs s s₆ := (k15.trans k6).mono (by decide)
  have O6 := out_arrs (w := w) o6 (by omega_arith)
    (by have := VG.Proof.Bignum.slot_le (w := w) (j := 6) (by decide); omega_arith)
  have O26 := O25.trans O6
  -- `qInv` into array 7.
  refine WP.mono (loadOne_ok (j := 7) (A := QIa) (L := pL) (hs.congr k16.2.2) hZ (by decide)
    hw' ((k16.gpr (by decide)).trans h6) e7'
    ((k16.gpr (by decide)).trans hra) ((k16.gpr (by decide)).trans h5) ((k16.gpr (by decide)).trans h0)
    (by decide) (by decide) (by rw [hd O26 _ (by decide)]; exact hQIa) (by rw [hd O26 _ (by decide)]; exact hPL)
    hp hpw (bc k16 bQI)) fun t ⟨⟨v7, t7, o7, t7'⟩, k7⟩ => ?_
  have O7 := out_arrs (w := w) o7 (by omega_arith)
    (by have := VG.Proof.Bignum.slot_le (w := w) (j := 7) (by decide); omega_arith)
  have w0 : ∀ {m m' : Mem} {i : Nat}, Mont.Outside BX (slot w i) (8 * (w + 1)) m m' → i ≠ 0 →
      Mont.word m' BX (slot w 0) = Mont.word m BX (slot w 0) := fun h hi => by
    have := arr_word (q := 0) h hi (by decide) (by omega_arith) hn8
    simpa only [Nat.mul_zero, Nat.add_zero] using this
  have hones0 : Mont.word s₂.mem BX (slot w 0) = BitVec.allOnes 64 := by
    simpa only [Nat.mul_zero, Nat.add_zero] using h1w 0 hw1
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, O26.trans O7, t7'⟩, (k16.trans k7).mono (by decide)⟩
  · rw [arr_val o7 (by decide) (by decide) hn8, arr_val o6 (by decide) (by decide) hn8,
      arr_val o5 (by decide) (by decide) hn8, arr_val o4 (by decide) (by decide) hn8,
      arr_val o3 (by decide) (by decide) hn8, h1s]
  · rw [w0 o7 (by decide), w0 o6 (by decide), w0 o5 (by decide), w0 o4 (by decide), w0 o3 (by decide), hones0]
  · rw [arr_val o7 (by decide) (by decide) hn8, arr_val o6 (by decide) (by decide) hn8,
      arr_val o5 (by decide) (by decide) hn8, arr_val o4 (by decide) (by decide) hn8, v1, hbz O2 bN]
  · rw [arr_val o7 (by decide) (by decide) hn8, arr_val o6 (by decide) (by decide) hn8,
      arr_val o5 (by decide) (by decide) hn8, v4, hbz O23 bP]
  · rw [arr_val o7 (by decide) (by decide) hn8, arr_val o6 (by decide) (by decide) hn8, v5, hbz O24 bQ]
  · rw [arr_val o7 (by decide) (by decide) hn8, v6, hbz O25 bI]
  · rw [v7, hbz O26 bQI]
  · rw [arr_word o7 (by decide) (by decide) (Nat.le_refl _) hn8, arr_word o6 (by decide) (by decide) (Nat.le_refl _) hn8,
      arr_word o5 (by decide) (by decide) (Nat.le_refl _) hn8, arr_word o4 (by decide) (by decide) (Nat.le_refl _) hn8, t1]
  · rw [arr_word o7 (by decide) (by decide) (Nat.le_refl _) hn8, arr_word o6 (by decide) (by decide) (Nat.le_refl _) hn8,
      arr_word o5 (by decide) (by decide) (Nat.le_refl _) hn8, t4]
  · rw [arr_word o7 (by decide) (by decide) (Nat.le_refl _) hn8, arr_word o6 (by decide) (by decide) (Nat.le_refl _) hn8, t5]
  · rw [arr_word o7 (by decide) (by decide) (Nat.le_refl _) hn8, t6]
  · exact t7

end VG.Proof.Bignum.RISCV64.Crt
