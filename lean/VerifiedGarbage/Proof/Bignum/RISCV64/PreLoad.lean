module

public import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public import VerifiedGarbage.Impl.Bignum.RISCV64.Precompute
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Bignum.ReverseEncoding
import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The precomputed values of an RSA modulus on RISC-V: zeroing and loading

`zeroWords_ok`: `w` words := 0. `loadN_ok`: the modulus's bytes, most
significant first, into array 0 as a little-endian number of `w` words.
-/

@[expose] public section

namespace VG.Proof.Bignum.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Impl.Bignum.RISCV64
  VG.Impl.Bignum.RISCV64.Precompute

theorem add_ofNat_zero (x : BitVec 64) : x + BitVec.ofNat 64 0 = x := BitVec.add_zero x

theorem read_one' (m : Mem) (a : Addr) : ((m.read a 1).setWidth 64).setWidth 8 = m a := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth]
  rw [Nat.mod_eq_of_lt (Nat.lt_trans (m.read a 1).isLt (by decide)),
    Nat.mod_eq_of_lt (m.read a 1).isLt]
  show (m.read (a + 1) 0 ++ m a).toNat = (m a).toNat
  rw [BitVec.toNat_append]
  simp [Mem.read]

/-- `zeroWords`, at `d` of `P` (`t3`) with `w` in `t0`: the `w` words := 0,
and the pointer past them. -/
theorem zeroWords_ok {s : State} {P : Addr} {Z d w : Nat} (hs : Scr s P Z)
    (h3 : s.gpr .t3 = off P d) (h0 : s.gpr .t0 = BitVec.ofNat 64 w) (hw : 1 ≤ w)
    (hw' : w < 2 ^ 31) (hd8 : d % 8 = 0) (hZ : d + 8 * w ≤ Z) :
    WP isa zeroWords s fun s' =>
      (s'.gpr .t3 = off P (d + 8 * w) ∧ (∀ i < w, word s'.mem P (d + 8 * i) = 0) ∧
        Outside P d (8 * w) s.mem s'.mem) ∧ Keep [.s0, .t3, .t5] s s' := by
  have hnw := hs.nowrap
  unfold zeroWords
  refine WP.seq ?_
  have hpre : WP isa (.block [.addi .t5 .t0 0, .li .s0 0]) s fun s₁ =>
      (s₁.gpr .t5 = BitVec.ofNat 64 w ∧ s₁.gpr .s0 = 0 ∧ s₁.gpr .t3 = off P d ∧ s₁.mem = s.mem) ∧
        Keep [.s0, .t5] s s₁ := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [exec_li, add_ofNat_zero, h0, h3, BitVec.add_zero]
    rfl
  refine WP.mono hpre fun s₁ ⟨⟨i5, i0, i3, im⟩, k₁⟩ => ?_
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .t3 = off P (d + 8 * i) ∧ t.gpr .s0 = 0 ∧ Outside P d (8 * i) s.mem t.mem ∧
      (∀ k < i, word t.mem P (d + 8 * k) = 0) ∧ Keep [.s0, .t3, .t5] s t
  refine WP.mono (wp_countdown (body := .block ([.store .d .s0 .t3 0, .addi .t3 .t3 8] ++
      ([.addi .t5 .t5 (-1)] : List Instr))) (cnt := .t5) (N := w) (by omega_arith) (by omega_arith) Inv
    (fun i hi t ⟨j3, j0, jout, jz, jk⟩ hc => ?_)
    ⟨by rw [i3]; rfl, i0, by rw [← im]; exact Outside.refl _ _ _ _, fun _ h => absurd h (by omega_arith),
      k₁.mono (by decide)⟩ i5) fun t ⟨t3, _, tout, tz, tk⟩ => ⟨⟨t3, tz, tout⟩, tk⟩
  have hst : WP isa (.block [.store .d .s0 .t3 0, .addi .t3 .t3 8, .addi .t5 .t5 (-1)]) t
      fun t' => t' = ((({ t with mem := t.mem.writeW (off P (d + 8 * i)) (0 : BitVec 64) } : State).write
        .t3 (off P (d + 8 * i + 8))).write .t5 (t.gpr .t5 - BitVec.ofNat 64 1)) := by
    brun [exec_li, add_ofNat_zero, j3, j0, (hs.congr jk.2.2).st (show d + 8 * i + 8 ≤ Z by omega_arith),
      (hs.congr jk.2.2).al8 (show d + 8 * i + 8 ≤ Z by omega_arith) (by omega_arith)]
  refine WP.mono hst fun t' e => ?_
  subst e
  have hw := writeW_outside t.mem P (d := d + 8 * i) 0 (by omega_arith)
  refine ⟨⟨by gsimp; rw [show d + 8 * i + 8 = d + 8 * (i + 1) by omega_arith], by gsimp; exact j0, ?_, ?_, ?_⟩,
    by gsimp⟩
  · gsimp; exact (jout.mono (Nat.le_refl _) (by omega_arith)).trans (hw.mono (by omega_arith) (by omega_arith))
  · intro k hk
    gsimp
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · rw [hw.word (by omega_arith) (by omega_arith)]; exact jz k hk
    · exact word_writeW_self _ _ _ _
  · exact Keep.trans' jk ((((Keep.mem _ _).trans (Keep.write _ _ _)).trans (Keep.write _ _ _)).mono (by decide))

/-- A byte of a zero word. -/
theorem byte_of_zero_word {m : Mem} {P : Addr} {d j : Nat} (h : word m P d = 0) (hj : j < 8) :
    m (off P d + BitVec.ofNat 64 j) = 0 := by
  rw [← Mem.extractLsb'_read m (off P d) (n := 8) hj]
  have : m.read (off P d) 8 = 0 := by
    have e : word m P d = m.read (off P d) 8 := by simp [word, Mem.readW]
    rw [← e, h]
  rw [this]; apply BitVec.eq_of_toNat_eq; simp

theorem val32_off (m : Mem) (P : Addr) (d n : Nat) : val32 m (off P d) 0 n = val32 m P d n := by
  rw [← VG.Proof.Bignum.read_eq_val32, ← VG.Proof.Bignum.read_eq_val32]
  simp [off]

theorem write1_outside (m : Mem) (base : Addr) {d : Nat} (v : BitVec (8 * 1)) (h : d + 1 ≤ 2 ^ 64) :
    Outside base d 1 m (m.write (off base d) 1 v) := by
  intro x hx
  apply Mem.write_apply
  simp only [ofs] at hx
  have : (x - off base d).toNat = (2 ^ 64 - d + (x - base).toNat) % 2 ^ 64 :=
    Offset.toNat_sub_add x base (by omega_arith)
  rw [this]
  have := (x - base).isLt
  rcases hx with hx | hx
  · rw [Nat.mod_eq_of_lt (by omega_arith)]; omega_arith
  · rw [show 2 ^ 64 - d + (x - base).toNat = (x - base).toNat - d + 2 ^ 64 by omega_arith,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega_arith)]
    omega_arith

theorem write1_self (m : Mem) (a : Addr) (v : BitVec (8 * 1)) : m.write a 1 v a = v := by
  simp only [Mem.write, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_lt_one, ite_true, Nat.mul_zero]
  apply BitVec.eq_of_toNat_eq; simp

/-- `loadN`, `n`'s `k` bytes at `N` (`s7`, outside the working space), `k` in
`s8` and `w` in `t0`: array 0 (at `dA`, `a7`) holds `n` as `w` words. -/
theorem loadN_ok {s : State} {B N : Addr} {Z dA k w : Nat} (hs : Scr s B Z)
    (h17 : s.gpr .a7 = off B dA) (h7 : s.gpr .s7 = off N 0) (h8 : s.gpr .s8 = BitVec.ofNat 64 k)
    (h0 : s.gpr .t0 = BitVec.ofNat 64 w) (hk : 1 ≤ k) (hkw : k ≤ 8 * w) (hw' : w < 2 ^ 31)
    (hdA : 1 ≤ dA) (hdA8 : dA % 8 = 0) (hZ : dA + 8 * w ≤ Z)
    (hN : ∀ i < k, InRegions (s.rd ++ s.wr) (off N i) 1)
    (hsep : ∀ i < k, ∀ x, ofs B x < Z → off N i ≠ x) :
    WP isa loadN s fun s' =>
      wordsVal s'.mem B dA w = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem N k) ∧
        Outside B dA (8 * w) s.mem s'.mem ∧ Keep [.a0, .s0, .t3, .t4, .t5] s s' := by
  have hnw := hs.nowrap
  unfold loadN
  refine WP.seq ?_
  have hpre : WP isa (.block [.addi .t3 .a7 0]) s fun s₁ =>
      (s₁.gpr .t3 = off B dA ∧ s₁.mem = s.mem) ∧ Keep [.t3] s s₁ := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [exec_li, add_ofNat_zero, h17, BitVec.add_zero]
  refine WP.mono hpre fun s₁ ⟨⟨i3, im⟩, k₁⟩ => ?_
  refine WP.seq (WP.mono (zeroWords_ok (hs.congr k₁.2.2) i3 ((k₁.gpr (by decide)).trans h0)
    (by omega_arith) hw' hdA8 hZ) fun s₂ ⟨⟨_, hz, out₂⟩, k₂⟩ => ?_)
  rw [im] at out₂
  have k12 := k₁.trans k₂
  refine WP.seq ?_
  have hpre2 : WP isa (.block [.add .t4 .a7 .s8, .addi .t4 .t4 (-1), .addi .a0 .s7 0,
      .addi .t5 .s8 0]) s₂ fun s₃ =>
      (s₃.gpr .t4 = off B (dA + k - 1) ∧ s₃.gpr .a0 = off N 0 ∧ s₃.gpr .t5 = BitVec.ofNat 64 k ∧
        s₃.mem = s₂.mem) ∧ Keep [.t4, .a0, .t5] s₂ s₃ := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [exec_li, add_ofNat_zero, k12.gpr (r := .a7) (by decide), k12.gpr (r := .s8) (by decide), k12.gpr (r := .s7) (by decide),
      h17, h8, h7, BitVec.add_zero]
    exact off_sub _ (by omega_arith)
  refine WP.mono hpre2 fun s₃ ⟨⟨j4, j0, j5, jm⟩, k₃⟩ => ?_
  -- The bytes stored so far.
  let Inv : Nat → State → Prop := fun j t =>
    t.gpr .t4 = off B (dA + k - 1 - j) ∧ t.gpr .a0 = off N j ∧
      Outside B dA (8 * w) s.mem t.mem ∧
      (∀ i < j, t.mem (off B (dA + (k - 1 - i))) = s.mem (off N i)) ∧
      (∀ p, k ≤ p → p < 8 * w → t.mem (off B (dA + p)) = 0) ∧
      Keep [.a0, .s0, .t3, .t4, .t5] s t
  have hz' : ∀ p, p < 8 * w → s₂.mem (off B (dA + p)) = 0 := fun p hp => by
    have := byte_of_zero_word (hz (p / 8) (by omega_arith)) (j := p % 8) (by omega_arith)
    rwa [off_add, show dA + 8 * (p / 8) + p % 8 = dA + p by omega_arith] at this
  refine WP.mono (wp_countdown (body := .block ([.load .b .s0 .a0 0, .store .b .s0 .t4 0, .addi .a0 .a0 1,
      .addi .t4 .t4 (-1)] ++ ([.addi .t5 .t5 (-1)] : List Instr))) (cnt := .t5) (N := k) (by omega_arith)
    (by omega_arith) Inv (fun j hj t ⟨t4, t0', tout, tb, tz, tk⟩ hc => ?_)
    ⟨by rw [j4]; rfl, j0, by rw [jm]; exact out₂, fun _ h => absurd h (by omega_arith),
      fun p _ hp => by rw [jm]; exact hz' p hp, (k12.trans k₃).mono (by decide)⟩ j5)
    fun t ⟨_, _, tout, tb, tz, tk⟩ => ⟨?_, tout, tk⟩
  · have hst : WP isa (.block [.load .b .s0 .a0 0, .store .b .s0 .t4 0, .addi .a0 .a0 1, .addi .t4 .t4 (-1),
        .addi .t5 .t5 (-1)]) t fun t' => t' = ((({ (t.write .s0 ((t.mem.read (off N j) 1).setWidth 64)) with
          mem := t.mem.write (off B (dA + k - 1 - j)) 1 (((t.mem.read (off N j) 1).setWidth 64).setWidth 8) } :
            State).write .a0 (off N (j + 1))).write .t4
              (off B (dA + k - 1 - j) - BitVec.ofNat 64 1)).write .t5 (t.gpr .t5 - BitVec.ofNat 64 1) := by
      brun [exec_li, add_ofNat_zero, t4, t0', (by rw [tk.2.1, tk.2.2]; exact hN j (by omega_arith) : InRegions (t.rd ++ t.wr) (off N j) 1),
        (hs.congr tk.2.2).st (d := dA + k - 1 - j) (n := 1) (by omega_arith)]
    refine WP.mono hst fun t' e => ?_
    subst e
    have ha : dA + k - 1 - j = dA + (k - 1 - j) := by omega_arith
    have hw1 := write1_outside t.mem B (d := dA + k - 1 - j)
      (((t.mem.read (off N j) 1).setWidth 64).setWidth 8) (by omega_arith)
    have hNj : t.mem (off N j) = s.mem (off N j) := by
      refine tout _ (Or.inr ?_)
      have := (off N j - B).isLt
      by_contra hc
      exact hsep j (by omega) (off N j) (by simp only [ofs] at hc ⊢; omega) rfl
    refine ⟨⟨?_, by gsimp, ?_, ?_, ?_, ?_⟩, by gsimp⟩
    · gsimp; rw [off_sub _ (by omega_arith), show dA + k - 1 - j - 1 = dA + k - 1 - (j + 1) by omega_arith]
    · gsimp; exact tout.trans (hw1.mono (by omega_arith) (by omega_arith))
    · intro i hi
      gsimp
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · rw [hw1 _ (by rw [ofs_off0 B (by omega_arith)]; omega_arith)]; exact tb i hi
      · rw [← ha, write1_self, read_one', hNj]
    · intro p hp hp'
      gsimp
      rw [hw1 _ (by rw [ofs_off0 B (by omega_arith)]; omega_arith)]; exact tz p hp hp'
    · exact Keep.trans' tk (((((((Keep.write _ _ _).trans (Keep.mem _ _)).trans (Keep.write _ _ _)).trans
        (Keep.write _ _ _)).trans (Keep.write _ _ _))).mono (by decide))
  · rw [wordsVal_eq_val32, ← val32_off,
      VG.Proof.Bignum.val32_zero_extension t.mem (off B dA) (k := k) (by omega_arith) fun p hp hp' => by
        rw [off_add]; exact tz p hp (by omega_arith),
      VG.Proof.Bignum.reversed_read s.mem t.mem N (off B dA) k fun j hj => by
        rw [off_add, show dA + j = dA + (k - 1 - (k - 1 - j)) by omega_arith, tb _ (by omega_arith)]]

end VG.Proof.Bignum.RISCV64
