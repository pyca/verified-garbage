module

public import VerifiedGarbage.Proof.Rsa.RISCV64.KeyLayout
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Rsa.RISCV64.KeyOps
import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
import VerifiedGarbage.Proof.Bignum.RISCV64.MontFinish64
import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Bignum.ReverseEncoding
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The RSA key operations on RISC-V: bytes in and out, the frame and `w`

* `load_ok`: `load j src len` reads `L` bytes, most significant first, into
  array `j`, which is zero, so that it holds their number;
* `storeBytes_ok`: array `j`'s low `L` bytes out, most significant first,
  masked; `bytes_of_store` says what they are;
* `zeroBytes_ok`: `L` zero bytes out;
* `save_ok`, `restore_ok`: the caller's `s0`–`s11` into the header's words
  0–11 and back, the working space's address in `s11`;
* `setW_ok`: `s9 := w = ⌈len / 8⌉`, `s10 := 8 (w + 2)`.
-/

@[expose] public section

namespace VG.Proof.Rsa.RISCV64.Keys

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum VG.Proof.Bignum.RISCV64
  VG.Impl.Bignum.RISCV64
open VG.Impl.Rsa.RISCV64.Keys (ptr load storeBytes zeroBytes save restore saved setW mov)

/-- The words of a number that is zero. -/
theorem word_of_num_zero {m : Mem} {B : Addr} {w j : Nat} (h : num m B w j = 0) {k : Nat} (hk : k < w) :
    word m B (arr w j + 8 * k) = 0 := by
  have := wordsVal_zero_part (a := k) (c := 1) h (by omega_arith)
  simp only [wordsVal, Nat.mul_zero, Nat.add_zero] at this
  exact BitVec.eq_of_toNat_eq (by simpa using this)

theorem keys_sub1 (P : Addr) {a : Nat} (h : 1 ≤ a) : off P a - BitVec.ofNat 64 1 = off P (a - 1) :=
  off_sub P h

/-- `load j src len`: the `L` bytes at `P` (`src`, outside the working
space), `L` in `len`, most significant first, into array `j`, which is zero. -/
theorem load_ok {s : State} {B P : Addr} {Z w N j L : Nat} {src len : Reg} (h : Ws s B Z w N) (hj : j < N)
    (hN : N ≤ 2048) (hl1 : len ≠ .t1) (hs : s.gpr src = P)
    (hl : s.gpr len = BitVec.ofNat 64 L) (hL : 1 ≤ L)
    (hLw : L ≤ 8 * w) (hP : ∀ i < L, InRegions (s.rd ++ s.wr) (off P i) 1)
    (hsep : ∀ i < L, ∀ x, ofs B x < Z → off P i ≠ x) (hz : num s.mem B w j = 0) :
    WP isa (load j src len) s fun t => Ws t B Z w N ∧ Frame B w [j] [] s.mem t.mem ∧
      num t.mem B w j = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem P L) ∧ Keep [.t0, .t1, .t3, .t5] s t ∧
      Outside B (arr w j) (8 * w) s.mem t.mem := by
  have fit := h.arr_fit hj
  have hnw := h.nowrap
  have hS : S w = 8 * (w + 2) := rfl
  have := h.wle
  rw [load, WP.seq_iff, List.append_assoc, WP.block_append_iff]
  have hb₀ : WP isa (.block [mov .t1 src, mov .t3 len]) s fun u =>
      (u.gpr .t1 = P ∧ u.gpr .t3 = BitVec.ofNat 64 L ∧ u.mem = s.mem) ∧ Keep [.t1, .t3] s u := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [mov, add_ofNat_zero', hs, hl, hl1]
  refine WP.mono hb₀ fun u ⟨⟨u1, u3, um⟩, ku⟩ => ?_
  have hu := h.of_keep ku
  rw [← List.append_nil (ptr .t0 j ++ _), List.append_assoc]
  refine ptr_ok hu (by decide) (by decide) (show j < 2048 by omega_arith) ?_
  rw [List.append_nil]
  have hb : WP isa (.block [.add .t0 .t0 .t3, .addi .t0 .t0 (-1)]) (u.write .t0 (off B (arr w j))) fun v =>
      (v.gpr .t0 = off B (arr w j + L - 1) ∧ v.gpr .t1 = off P 0 ∧ v.gpr .t3 = BitVec.ofNat 64 L ∧
        v.mem = s.mem) ∧ Keep [.t0] (u.write .t0 (off B (arr w j))) v := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [u1, u3, um]
    exact ⟨keys_sub1 _ (by omega_arith), by simp [off]⟩
  refine WP.mono hb fun s₃ ⟨⟨j0, j1, j3, jm⟩, k₃⟩ => ?_
  have k₀ : Keep [.t0, .t1, .t3] s s₃ := (ku.trans ((Keep.write _ _ _).trans k₃)).mono (by decide)
  have hha : hdr ≤ arr w j := hdr_le_arr w j
  have h256 : hdr = 256 := rfl
  have hz' : ∀ p < 8 * w, s.mem (off B (arr w j + p)) = 0 := fun p hp => by
    have := byte_of_zero_word (word_of_num_zero hz (k := p / 8) (by omega_arith)) (j := p % 8) (by omega_arith)
    rwa [off_add, show arr w j + 8 * (p / 8) + p % 8 = arr w j + p by omega_arith] at this
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .t0 = off B (arr w j + L - 1 - i) ∧ t.gpr .t1 = off P i ∧
      Outside B (arr w j) (8 * w) s.mem t.mem ∧
      (∀ c < i, t.mem (off B (arr w j + (L - 1 - c))) = s.mem (off P c)) ∧
      (∀ p, L ≤ p → p < 8 * w → t.mem (off B (arr w j + p)) = 0) ∧
      Keep [.t0, .t1, .t3, .t5] s t
  refine WP.mono (wp_countdown (body := .block ([.load .b .t5 .t1 0, .store .b .t5 .t0 0, .addi .t1 .t1 1,
      .addi .t0 .t0 (-1)] ++ ([.addi .t3 .t3 (-1)] : List Instr))) (cnt := .t3) (N := L) (by omega_arith)
    (by omega_arith) Inv (fun i hi t ⟨t0, t1, tout, tb, tz, tk⟩ _ => ?_)
    ⟨by rw [j0]; rfl, j1, by rw [jm]; exact Outside.refl _ _ _ _, fun _ h => absurd h (by omega_arith),
      fun p _ hp => by rw [jm]; exact hz' p hp, k₀.mono (by decide)⟩ j3)
    fun t ⟨_, _, tout, tb, tz, tk⟩ => ⟨h.of_keep tk, ?_, ?_, tk, tout⟩
  · have hst : WP isa (.block [.load .b .t5 .t1 0, .store .b .t5 .t0 0, .addi .t1 .t1 1, .addi .t0 .t0 (-1),
        .addi .t3 .t3 (-1)]) t fun t' => t' = ((({ (t.write .t5 ((t.mem.read (off P i) 1).setWidth 64)) with
          mem := t.mem.write (off B (arr w j + L - 1 - i)) 1
            (((t.mem.read (off P i) 1).setWidth 64).setWidth 8) } : State).write .t1 (off P (i + 1))).write .t0
              (off B (arr w j + L - 1 - i) - BitVec.ofNat 64 1)).write .t3 (t.gpr .t3 - BitVec.ofNat 64 1) := by
      brun [t0, t1, (by rw [tk.2.1, tk.2.2]; exact hP i (by omega_arith) : InRegions (t.rd ++ t.wr) (off P i) 1),
        (h.scr.congr tk.2.2).st (d := arr w j + L - 1 - i) (n := 1) (by omega_arith)]
    refine WP.mono hst fun t' e => ?_
    subst e
    have ha : arr w j + L - 1 - i = arr w j + (L - 1 - i) := by omega_arith
    have hw1 := write1_outside t.mem B (d := arr w j + L - 1 - i)
      (((t.mem.read (off P i) 1).setWidth 64).setWidth 8) (by omega_arith)
    have hPi : t.mem (off P i) = s.mem (off P i) := by
      refine tout _ (Or.inr ?_)
      have := (off P i - B).isLt
      by_contra hc
      exact hsep i (by omega) (off P i) (by simp only [ofs] at hc ⊢; omega) rfl
    refine ⟨⟨?_, by gsimp, ?_, ?_, ?_, ?_⟩, by gsimp⟩
    · gsimp; rw [keys_sub1 (a := arr w j + L - 1 - i) _ (by omega),
        show arr w j + L - 1 - i - 1 = arr w j + L - 1 - (i + 1) by omega]
    · gsimp; exact tout.trans (hw1.mono (o' := arr w j) (n' := 8 * w) (by omega_arith) (by omega_arith))
    · intro c hc
      gsimp
      rcases Nat.lt_succ_iff_lt_or_eq.mp hc with hc | rfl
      · rw [hw1 _ (by rw [Mont.ofs_off0 B (by omega_arith)]; omega_arith)]; exact tb c hc
      · rw [← ha, write1_self, read_one', hPi]
    · intro p hp hp'
      gsimp
      rw [hw1 _ (by rw [Mont.ofs_off0 B (by omega_arith)]; omega_arith)]; exact tz p hp hp'
    · exact Keep.trans' tk (((((((Keep.write _ _ _).trans (Keep.mem _ _)).trans (Keep.write _ _ _)).trans
        (Keep.write _ _ _)).trans (Keep.write _ _ _))).mono (by decide))
  · exact Frame.of_arr (d := 0) (by simpa using tout) (by omega_arith) (by simp)
  · change wordsVal _ _ _ _ = _
    rw [wordsVal_eq_val32, ← val32_off,
      val32_zero_extension t.mem (off B (arr w j)) (k := L) (by omega_arith) fun p hp hp' => by
        rw [off_add]; exact tz p hp (by omega_arith),
      reversed_read s.mem t.mem P (off B (arr w j)) L fun c hc => by
        rw [off_add, show arr w j + c = arr w j + (L - 1 - (L - 1 - c)) by omega_arith, tb _ (by omega_arith)]]

/-- A byte under a mask of all ones or zero. -/
theorem mask_byte64 (x : BitVec (8 * 1)) (b : Bool) :
    ((x.setWidth 64 &&& (if b then BitVec.allOnes 64 else 0)).setWidth 8) = if b then x else 0 := by
  cases b
  · simp only [Bool.false_eq_true, ite_false]
    rw [show (0 : BitVec 64) = 0#64 from rfl, BitVec.and_zero]; rfl
  · simp only [ite_true, BitVec.and_allOnes]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth]
    have := x.isLt
    omega_arith

/-- `storeBytes j dst len`: array `j`'s low `L` bytes to the `L` bytes at `O`
(`dst`), `L` in `len`, most significant first, masked by `t4` (the mask of `b`). -/
theorem storeBytes_ok {s : State} {B O : Addr} {Z w N j L : Nat} {dst len : Reg} (h : Ws s B Z w N)
    (hj : j < N) (hN : N ≤ 2048) (hd : s.gpr dst = O) (hl : s.gpr len = BitVec.ofNat 64 L)
    (hl1 : len ≠ .t1) (hd1 : dst ≠ .t1) (hl0 : len ≠ .t0) {b : Bool}
    (h4 : s.gpr .t4 = if b then BitVec.allOnes 64 else 0) (hL : 1 ≤ L)
    (hLw : L ≤ 8 * w) (hO : ∀ i < L, InRegions s.wr (off O i) 1)
    (hsep : ∀ i < L, ∀ x, ofs B x < Z → off O i ≠ x) (hOw : O.toNat + L ≤ 2 ^ 64) :
    WP isa (storeBytes j dst len) s fun t => Ws t B Z w N ∧
      (∀ c < L, t.mem (off O c) = if b then s.mem (off B (arr w j + (L - 1 - c))) else 0) ∧
      Outside O 0 L s.mem t.mem ∧ Keep [.t0, .t1, .t3, .t5] s t := by
  have fit := h.arr_fit hj
  have hnw := h.nowrap
  have hS : S w = 8 * (w + 2) := rfl
  have := h.wle
  rw [storeBytes, WP.seq_iff]
  refine ptr_ok h (by decide) (by decide) (show j < 2048 by omega_arith) ?_
  have hha : hdr ≤ arr w j := hdr_le_arr w j
  have h256 : hdr = 256 := rfl
  have hb : WP isa (.block [.add .t1 .t1 len, .addi .t1 .t1 (-1), mov .t0 dst, mov .t3 len])
      (s.write .t1 (off B (arr w j))) fun u =>
      (u.gpr .t1 = off B (arr w j + L - 1) ∧ u.gpr .t0 = off O 0 ∧ u.gpr .t3 = BitVec.ofNat 64 L ∧
        u.gpr .t4 = s.gpr .t4 ∧ u.mem = s.mem) ∧ Keep [.t0, .t1, .t3] (s.write .t1 (off B (arr w j))) u := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [mov, add_ofNat_zero', hd, hl, hl1, hd1, hl0, off_add]
    exact keys_sub1 _ (by omega)
  refine WP.mono hb fun s₃ ⟨⟨j1, j0, j3, j4, jm⟩, k₃⟩ => ?_
  have k₀ : Keep [.t0, .t1, .t3] s s₃ := ((Keep.write _ _ _).trans k₃).mono (by decide)
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .t1 = off B (arr w j + L - 1 - i) ∧ t.gpr .t0 = off O i ∧
      Outside O 0 i s.mem t.mem ∧
      (∀ c < i, t.mem (off O c) = if b then s.mem (off B (arr w j + (L - 1 - c))) else 0) ∧
      Keep [.t0, .t1, .t3, .t5] s t
  refine WP.mono (wp_countdown (body := .block ([.load .b .t5 .t1 0, .logic .and .t5 .t5 .t4, .store .b .t5 .t0 0,
      .addi .t0 .t0 1, .addi .t1 .t1 (-1)] ++ ([.addi .t3 .t3 (-1)] : List Instr))) (cnt := .t3) (N := L)
    (by omega_arith) (by omega_arith) Inv (fun i hi t ⟨t1, t0, tout, tb, tk⟩ _ => ?_)
    ⟨by rw [j1]; rfl, j0, by rw [jm]; exact Outside.refl _ _ _ _, fun _ h => absurd h (by omega_arith),
      k₀.mono (by decide)⟩ j3)
    fun t ⟨_, _, tout, tb, tk⟩ => ⟨h.of_keep tk, tb, tout, tk⟩
  have t4 : t.gpr .t4 = s.gpr .t4 := tk.gpr (by decide)
  have hst : WP isa (.block [.load .b .t5 .t1 0, .logic .and .t5 .t5 .t4, .store .b .t5 .t0 0, .addi .t0 .t0 1,
      .addi .t1 .t1 (-1), .addi .t3 .t3 (-1)]) t fun t' =>
        (t'.gpr .t1 = off B (arr w j + L - 1 - i) - BitVec.ofNat 64 1 ∧ t'.gpr .t0 = off O (i + 1) ∧
          t'.gpr .t3 = t.gpr .t3 - BitVec.ofNat 64 1 ∧
          t'.mem = t.mem.write (off O i) 1 (if b then t.mem.read (off B (arr w j + L - 1 - i)) 1 else 0)) ∧
        Keep [.t0, .t1, .t3, .t5] t t' := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [t1, t0, t4, h4, (h.scr.congr tk.2.2).ld (d := arr w j + L - 1 - i) (n := 1) (by omega_arith),
      (by rw [tk.2.2]; exact hO i hi : InRegions t.wr (off O i) 1), mask_byte64]
  refine WP.mono hst fun t' ⟨⟨l1, l0, l3, lm⟩, lk⟩ => ⟨⟨?_, l0, ?_, ?_, Keep.trans' tk lk⟩, l3⟩
  · rw [l1, keys_sub1 _ (by omega), show arr w j + L - 1 - i - 1 = arr w j + L - 1 - (i + 1) by omega]
  · have hw1 := write1_outside t.mem O (d := i) (if b then t.mem.read (off B (arr w j + L - 1 - i)) 1 else 0)
      (by omega_arith)
    rw [lm]; exact (tout.mono (o' := 0) (n' := i + 1) (by omega_arith) (by omega_arith)).trans
      (hw1.mono (o' := 0) (n' := i + 1) (by omega_arith) (by omega_arith))
  · have hw1 := write1_outside t.mem O (d := i) (if b then t.mem.read (off B (arr w j + L - 1 - i)) 1 else 0)
      (by omega_arith)
    intro c hc
    rw [lm]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hc with hc | rfl
    · rw [hw1 _ (by rw [Mont.ofs_off0 O (by omega_arith)]; omega_arith)]; exact tb c hc
    · rw [write1_self]
      -- The byte read is the array's, which no output byte overlaps.
      have ha : t.mem (off B (arr w j + L - 1 - c)) = s.mem (off B (arr w j + L - 1 - c)) := by
        refine tout _ (Or.inr ?_)
        by_contra hlt
        have hx : off O (ofs O (off B (arr w j + L - 1 - c))) = off B (arr w j + L - 1 - c) := by
          simp only [off, ofs, BitVec.ofNat_toNat, BitVec.setWidth_eq]
          rw [BitVec.add_comm]; exact BitVec.sub_add_cancel _ _
        exact hsep _ (by omega_arith) _ (by rw [Mont.ofs_off0 B (by omega_arith)]; omega_arith) hx
      have r1 : ∀ (m : Mem) (a : Addr), m.read a 1 = m a := fun m a =>
        BitVec.eq_of_toNat_eq (by rw [read_toNat_succ]; simp [Mem.read])
      cases b
      · rfl
      · simp only [ite_true]
        rw [show arr w j + (L - 1 - c) = arr w j + L - 1 - c by omega_arith, ← ha, r1]

/-- `zeroBytes dst len`: the `L` bytes at `O` (`dst`), `L` in `len`, := 0. -/
theorem zeroBytes_ok {s : State} {O : Addr} {L : Nat} {dst len : Reg} (hd : s.gpr dst = O)
    (hl : s.gpr len = BitVec.ofNat 64 L) (hl0 : len ≠ .t0) (hL : 1 ≤ L) (hL' : L < 2 ^ 32)
    (hO : ∀ i < L, InRegions s.wr (off O i) 1) (hOw : O.toNat + L ≤ 2 ^ 64) :
    WP isa (zeroBytes dst len) s fun t => (∀ c < L, t.mem (off O c) = 0) ∧ Outside O 0 L s.mem t.mem ∧
      Keep [.t0, .t3, .t5] s t := by
  rw [zeroBytes, WP.seq_iff]
  have hb : WP isa (.block [mov .t0 dst, mov .t3 len, .li .t5 0]) s fun u =>
      (u.gpr .t5 = 0 ∧ u.gpr .t0 = off O 0 ∧ u.gpr .t3 = BitVec.ofNat 64 L ∧ u.mem = s.mem) ∧
        Keep [.t0, .t3, .t5] s u := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [mov, add_ofNat_zero', fin64_exec_li_zero, hd, hl, hl0]
  refine WP.mono hb fun u ⟨⟨u5, u0, u3, um⟩, ku⟩ => ?_
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .t0 = off O i ∧ t.gpr .t5 = 0 ∧ Outside O 0 i s.mem t.mem ∧ (∀ c < i, t.mem (off O c) = 0) ∧
      Keep [.t0, .t3, .t5] s t
  refine WP.mono (wp_countdown (body := .block ([.store .b .t5 .t0 0, .addi .t0 .t0 1] ++
      ([.addi .t3 .t3 (-1)] : List Instr))) (cnt := .t3) (N := L) (by omega_arith) (by omega_arith) Inv
    (fun i hi t ⟨t0, t5, tout, tz, tk⟩ _ => ?_)
    ⟨u0, u5, by rw [um]; exact Outside.refl _ _ _ _, fun _ h => absurd h (by omega_arith), ku⟩ u3)
    fun t ⟨_, _, tout, tz, tk⟩ => ⟨tz, tout, tk⟩
  have hst : WP isa (.block [.store .b .t5 .t0 0, .addi .t0 .t0 1, .addi .t3 .t3 (-1)]) t fun t' =>
      (t'.gpr .t0 = off O (i + 1) ∧ t'.gpr .t5 = 0 ∧ t'.gpr .t3 = t.gpr .t3 - BitVec.ofNat 64 1 ∧
        t'.mem = t.mem.write (off O i) 1 0) ∧ Keep [.t0, .t3] t t' := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [t0, t5, (by rw [tk.2.2]; exact hO i hi : InRegions t.wr (off O i) 1)]
    rfl
  refine WP.mono hst fun t' ⟨⟨l0, l5, l3, lm⟩, lk⟩ =>
    ⟨⟨l0, l5, ?_, ?_, Keep.trans' tk (lk.mono (by decide))⟩, l3⟩
  · have hw1 := write1_outside t.mem O (d := i) 0 (by omega_arith)
    rw [lm]; exact (tout.mono (o' := 0) (n' := i + 1) (by omega_arith) (by omega_arith)).trans
      (hw1.mono (o' := 0) (n' := i + 1) (by omega_arith) (by omega_arith))
  · have hw1 := write1_outside t.mem O (d := i) 0 (by omega_arith)
    intro c hc
    rw [lm]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hc with hc | rfl
    · rw [hw1 _ (by rw [Mont.ofs_off0 O (by omega_arith)]; omega_arith)]; exact tz c hc
    · rw [write1_self]

/-- The `L` bytes at `O` reversed from array `j`'s low bytes: its number modulo
`256^L`, most significant first. -/
theorem bytes_of_store {m m' : Mem} {B O : Addr} {w j L : Nat} (hL : L ≤ 8 * w)
    (hb : ∀ c < L, m' (off O c) = m (off B (arr w j + (L - 1 - c)))) :
    Spec.Rsa.bytesAt m' O L = Spec.Rsa.i2osp (num m B w j % 256 ^ L) L := by
  have hr := reversed_read m' m O (off B (arr w j)) L fun c hc => by
    rw [off_add]
    have := hb (L - 1 - c) (by omega_arith)
    rw [show L - 1 - (L - 1 - c) = c by omega_arith] at this
    rw [← this]
  have e := read_toNat_add m (8 * w - L) L (off B (arr w j))
  rw [show 8 * w - L + L = 8 * w by omega_arith, show 8 * w = 4 * (2 * w) by omega_arith, read_eq_val32] at e
  have hlt := (m.read (off B (arr w j)) L).isLt
  have hval : num m B w j % 256 ^ L = (m.read (off B (arr w j)) L).toNat := by
    change wordsVal _ _ _ _ % _ = _
    rw [wordsVal_eq_val32, e, show (256 : Nat) ^ L = 2 ^ (8 * L) by rw [Nat.pow_mul],
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  rw [hval, hr]
  have hl : (Spec.Rsa.bytesAt m' O L).length = L := by simp [Spec.Rsa.bytesAt]
  have e2 := i2osp_os2ip (Spec.Rsa.bytesAt m' O L)
  rw [hl] at e2
  exact e2.symm

/-- A number of `L` bytes is below `2^(8 L)`. -/
theorem os2ip_bytes_lt (m : Mem) (p : Addr) (L : Nat) :
    Spec.Rsa.os2ip (Spec.Rsa.bytesAt m p L) < 2 ^ (8 * L) := by
  have h := VG.Proof.Rsa.lt_of_os2ip (Spec.Rsa.bytesAt m p L)
  rwa [show (Spec.Rsa.bytesAt m p L).length = L by simp [Spec.Rsa.bytesAt], show (256 : Nat) = 2 ^ 8 from rfl,
    ← Nat.pow_mul] at h

/-! ## Saving and restoring the caller's registers -/

theorem saved_inj : ∀ i < 12, ∀ j < 12, saved i = saved j → i = j := by decide

theorem saved_ne : ∀ i < 11, saved i ≠ .s11 := by decide

theorem saved_11 : saved 11 = .s11 := rfl

theorem saved_t0 : ∀ i < 12, saved i ≠ .t0 := by decide

/-- The first `n` registers are saved at `B`. -/
structure SI (s₀ : State) (B : Addr) (n : Nat) (s : State) : Prop where
  keep : Keep [.t0] s₀ s
  t0 : s.gpr .t0 = B
  sp : s.sp = s₀.sp
  out : Outside B 0 96 s₀.mem s.mem
  saved : ∀ i < n, word s.mem B (8 * i) = s₀.gpr (saved i)

theorem save_step (s₀ : State) {B : Addr} {Z : Nat} (hs : Scr s₀ B Z) (hZ : 96 ≤ Z) {n : Nat} (hn : n < 12)
    {s : State} (h : SI s₀ B n s) :
    WP isa (.block [.store .d (saved n) .t0 (8 * n)]) s (SI s₀ B (n + 1)) := by
  have hnw := hs.nowrap
  have hs' := hs.congr h.keep.2.2
  have hr : s.gpr (saved n) = s₀.gpr (saved n) := h.keep.gpr (by simpa using saved_t0 n hn)
  have hout : InRegions s.wr (s.gpr .t0 + BitVec.ofNat 64 (8 * n)) 8 := by
    rw [h.t0]; exact hs'.st (d := 8 * n) (n := 8) (by omega_arith)
  have ha : (s.gpr .t0 + BitVec.ofNat 64 (8 * n)).toNat % 8 = 0 := by
    rw [h.t0]; exact hs'.al8 (d := 8 * n) (by omega_arith) (by omega_arith)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    exec_store_d (show 8 * n < 2048 by omega_arith) ha hout, Option.some.injEq, exists_eq_left', h.t0, hr]
  have hw := writeW_outside s.mem B (d := 8 * n) (s₀.gpr (saved n)) (by omega_arith)
  refine ⟨Keep.trans' h.keep ((Keep.mem _ _).mono (by decide)), by rw [gpr_mem]; exact h.t0, h.sp,
    h.out.trans (hw.mono (by omega_arith) (by omega_arith)), fun i hi => ?_⟩
  rw [mem_mem]
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
  · rw [hw.word (by omega_arith) (by omega_arith)]; exact h.saved i hi
  · exact word_writeW_self _ _ _ _

/-- The state after `save`. -/
structure Saved (s₀ : State) (B : Addr) (s : State) : Prop where
  keep : Keep [.t0, .s11] s₀ s
  sp : s.sp = s₀.sp
  t0 : s.gpr .t0 = B
  s11 : s.gpr .s11 = B
  out : Outside B 0 96 s₀.mem s.mem
  saved : ∀ i < 12, word s.mem B (8 * i) = s₀.gpr (saved i)

/-- `save (8 i)`: the working space's address `B`, the stack argument `i`,
into `t0` and `s11`, and the caller's `s0`–`s11` into its first 12 words. -/
theorem save_ok (s₀ : State) {i Z : Nat} (hi : 8 * i < 2048)
    (hin : InRegions (s₀.rd ++ s₀.wr) (stackArgAddr s₀ i) 8) (hal : (stackArgAddr s₀ i).toNat % 8 = 0)
    (hs : Scr s₀ (stackArg s₀ i) Z) (hZ : 96 ≤ Z) :
    WP isa (.block (save (8 * i))) s₀ (Saved s₀ (stackArg s₀ i)) := by
  rw [save, List.append_assoc, WP.block_append_iff]
  have hb : WP isa (.block [.addSp .t0 0, .load .d .t0 .t0 (8 * i)]) s₀ fun s =>
      (s.gpr .t0 = stackArg s₀ i ∧ s.mem = s₀.mem ∧ s.sp = s₀.sp) ∧ Keep [.t0] s₀ s := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    have e : s₀.sp + BitVec.ofNat 64 0 + BitVec.ofNat 64 (8 * i) = stackArgAddr s₀ i := by
      rw [add_ofNat_zero']; rfl
    have ha : ((s₀.write .t0 (s₀.sp + BitVec.ofNat 64 0)).gpr .t0 + BitVec.ofNat 64 (8 * i)).toNat % 8 = 0 := by
      rw [gpr_write_self, e]; exact hal
    have hin' : InRegions ((s₀.write .t0 (s₀.sp + BitVec.ofNat 64 0)).rd ++ (s₀.write .t0 (s₀.sp + BitVec.ofNat 64 0)).wr)
        ((s₀.write .t0 (s₀.sp + BitVec.ofNat 64 0)).gpr .t0 + BitVec.ofNat 64 (8 * i)) 8 := by
      rw [gpr_write_self, e]; exact hin
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec_addSp (show 0 < 2048 by decide),
      exec_load_d hi ha hin', Option.some.injEq, exists_eq_left', gpr_write_self, e, mem_write, sp_write,
      and_true]
    first | rfl | exact ⟨rfl, rfl⟩
  refine WP.mono hb fun s₁ ⟨⟨i0, im, isp⟩, k₁⟩ => ?_
  refine WP.block_append (WP.mono (wp_range_flatMap (M := isa) (SI s₀ (stackArg s₀ i))
    (fun k s hk h => save_step s₀ hs hZ hk h) 12 (Nat.le_refl _) s₁
    ⟨k₁, i0, isp, by rw [im]; exact Outside.refl _ _ _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩)
    fun s h => ?_)
  have hw : s.gpr .t0 = stackArg s₀ i := h.t0
  apply WP.of_runBlock
  simp only [mov, runBlock_cons, runStep_some, runBlock_nil, exec_addi (show imm12 0 by decide),
    BitVec.ofInt_ofNat, add_ofNat_zero', Option.some.injEq, exists_eq_left', hw]
  refine ⟨(h.keep.trans (Keep.write _ _ _)).mono (by decide), h.sp, ?_, ?_, h.out, h.saved⟩
  · rw [gpr_write, ite_eq_right_iff.mpr fun e => absurd e (by decide)]; exact hw
  · rw [gpr_write, ite_eq_left_iff.mpr fun e => absurd rfl e]

/-- The first `n` registers are restored to `v`, from the state `sB` the
restoring starts in. -/
structure RI (sB : State) (B : Addr) (v : Nat → BitVec 64) (n : Nat) (s : State) : Prop where
  s11 : s.gpr .s11 = B
  restored : ∀ i < n, s.gpr (saved i) = v i
  others : ∀ r, (∀ i < 12, r ≠ saved i) → s.gpr r = sB.gpr r
  mem : s.mem = sB.mem
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr
  sp : s.sp = sB.sp

theorem restore_step (sB : State) {B : Addr} {Z : Nat} (hs : Scr sB B Z) (hZ : 96 ≤ Z) {v : Nat → BitVec 64}
    (hsav : ∀ i < 12, word sB.mem B (8 * i) = v i) {n : Nat} (hn : n < 11) {s : State} (h : RI sB B v n s) :
    WP isa (.block [.load .d (saved n) .s11 (8 * n)]) s (RI sB B v (n + 1)) := by
  have hs' := hs.congr h.wr
  have hrd : s.rd = sB.rd := h.rd
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .s11 + BitVec.ofNat 64 (8 * n)) 8 := by
    rw [h.s11]; exact hs'.ld (d := 8 * n) (by omega_arith)
  have ha : (s.gpr .s11 + BitVec.ofNat 64 (8 * n)).toNat % 8 = 0 := by
    rw [h.s11]; exact hs'.al8 (d := 8 * n) (by omega_arith) (by omega_arith)
  have hv : s.mem.readW (B + BitVec.ofNat 64 (8 * n)) 64 = v n := by
    rw [h.mem]; exact hsav n (by omega_arith)
  have hn11 := saved_ne n hn
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    exec_load_d (show 8 * n < 2048 by omega_arith) ha hin, Option.some.injEq, exists_eq_left', h.s11, hv]
  refine ⟨?_, fun i hi => ?_, fun r hr => ?_, h.mem, h.rd, h.wr, h.sp⟩
  · rw [gpr_write, ite_eq_right_iff.mpr fun e => absurd e (Ne.symm hn11)]; exact h.s11
  · rw [gpr_write]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · have e : saved i ≠ saved n := fun e =>
        absurd (saved_inj i (by omega_arith) n (by omega_arith) e) (by omega_arith)
      rw [ite_eq_right_iff.mpr fun e' => absurd e' e]; exact h.restored i hi
    · rw [ite_eq_left_iff.mpr fun e => absurd rfl e]
  · rw [gpr_write, ite_eq_right_iff.mpr fun e => absurd e (hr n (by omega_arith))]
    exact h.others r hr

/-- `restore`, from a state whose first 12 words of the working space `B`
(in `s11`) hold `v`: the saved registers are `v`, everything else is kept. -/
theorem restore_ok (sB : State) {B : Addr} {Z : Nat} (hs : Scr sB B Z) (hZ : 96 ≤ Z) {v : Nat → BitVec 64}
    (hw : sB.gpr .s11 = B) (hsav : ∀ i < 12, word sB.mem B (8 * i) = v i) :
    WP isa (.block restore) sB fun s =>
      (∀ i < 12, s.gpr (saved i) = v i) ∧ (∀ r, (∀ i < 12, r ≠ saved i) → s.gpr r = sB.gpr r) ∧
      s.mem = sB.mem ∧ s.rd = sB.rd ∧ s.wr = sB.wr ∧ s.sp = sB.sp := by
  rw [restore]
  refine WP.block_append (WP.mono (wp_range_flatMap (M := isa) (RI sB B v)
    (fun k s hk h => restore_step sB hs hZ hsav hk h) 11 (Nat.le_refl _) sB
    ⟨hw, fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ => rfl, rfl, rfl, rfl, rfl⟩) fun s h => ?_)
  have hs' := hs.congr h.wr
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .s11 + BitVec.ofNat 64 (8 * 11)) 8 := by
    rw [h.s11]; exact hs'.ld (d := 8 * 11) (by omega_arith)
  have ha : (s.gpr .s11 + BitVec.ofNat 64 (8 * 11)).toNat % 8 = 0 := by
    rw [h.s11]; exact hs'.al8 (d := 8 * 11) (by omega_arith) (by decide)
  have hv : s.mem.readW (B + BitVec.ofNat 64 (8 * 11)) 64 = v 11 := by
    rw [h.mem]; exact hsav 11 (by decide)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    exec_load_d (show 8 * 11 < 2048 by decide) ha hin, Option.some.injEq, exists_eq_left', h.s11, hv]
  refine ⟨fun i hi => ?_, fun r hr => ?_, h.mem, h.rd, h.wr, h.sp⟩
  · rw [gpr_write]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [ite_eq_right_iff.mpr fun e => absurd e (saved_ne i hi)]; exact h.restored i hi
    · rw [saved_11, ite_eq_left_iff.mpr fun e => absurd rfl e]
  · rw [gpr_write, ite_eq_right_iff.mpr fun e => absurd e (saved_11 ▸ hr 11 (by decide))]
    exact h.others r hr

/-! ## `w` and the stride -/

theorem add7_shr3 (k : Nat) (hk : k < 2 ^ 32) :
    (BitVec.ofNat 64 k + BitVec.ofNat 64 7) >>> 3 = BitVec.ofNat 64 ((k + 7) / 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (a := k) (by omega_arith), Nat.mod_eq_of_lt (a := 7) (by decide),
    Nat.mod_eq_of_lt (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]

theorem add2_shl3 (a : Nat) :
    (BitVec.ofNat 64 a + BitVec.ofNat 64 2) <<< 3 = BitVec.ofNat 64 (S a) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.shiftLeft_eq]
  simp only [S]
  omega_arith

/-- `setW len`, `k` in `len`: `s9 := w = ⌈k / 8⌉` and `s10 := 8 (w + 2)`. -/
theorem setW_ok {s : State} {len : Reg} {k : Nat} (hl : s.gpr len = BitVec.ofNat 64 k) (hk : k < 2 ^ 32) :
    WP isa (.block (setW len)) s fun t =>
      (t.gpr .s9 = BitVec.ofNat 64 ((k + 7) / 8) ∧ t.gpr .s10 = BitVec.ofNat 64 (S ((k + 7) / 8)) ∧
        t.mem = s.mem) ∧ Keep [.s9, .s10] s t := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  brun [setW, hl, add7_shr3 k hk, add2_shl3 ((k + 7) / 8)]

end VG.Proof.Rsa.RISCV64.Keys
