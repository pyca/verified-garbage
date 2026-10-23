module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Impl.Bignum.PPC64LE.Precompute
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Bignum.ReverseEncoding
import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# The precomputed values of an RSA modulus on PPC64LE: zeroing and loading

`zeroWords_ok`: `w` words := 0. `loadN_ok`: the modulus's bytes, most
significant first, into array 0 as a little-endian number of `2 w` digits.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.Precompute

theorem read_one' (m : Mem) (a : Addr) : ((m.read a 1).setWidth 64).setWidth 8 = m a := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth]
  rw [Nat.mod_eq_of_lt (Nat.lt_trans (m.read a 1).isLt (by decide)),
    Nat.mod_eq_of_lt (m.read a 1).isLt]
  show (m.read (a + 1) 0 ++ m a).toNat = (m a).toNat
  rw [BitVec.toNat_append]
  simp [Mem.read]

theorem exec_lbz' {s : State} {t n : Reg} {off : Nat} (hn : n ≠ .r0) (ho : off < 2 ^ 15)
    (h : InRegions (s.rd ++ s.wr) (s.gpr n + BitVec.ofNat 64 off) 1) :
    exec (.lbz t n off) s =
      some (s.write t ((s.mem.read (s.gpr n + BitVec.ofNat 64 off) 1).setWidth 64)) :=
  exec_lbz hn ho h

/-- `zeroWords`, at `d` of `P` with `2 w` in `r11`: the `w` words := 0, and the
pointer past them. -/
theorem zeroWords_ok {s : State} {P : Addr} {Z d w : Nat} (hs : Scr s P Z)
    (h14 : s.gpr .r14 = off P d) (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w)) (hw : 1 ≤ w)
    (hw' : w < 2 ^ 31) (hZ : d + 8 * w ≤ Z) :
    WP isa zeroWords s fun s' =>
      (s'.gpr .r14 = off P (d + 8 * w) ∧ (∀ i < w, word s'.mem P (d + 8 * i) = 0) ∧
        Outside P d (8 * w) s.mem s'.mem) ∧ Keep [.r0, .r14, .r17] s s' := by
  have hnw := hs.nowrap
  unfold zeroWords
  refine WP.seq ?_
  have hpre : WP isa (.block [.lsr .d .r17 .r11 1, .li .r0 0]) s fun s₁ =>
      (s₁.gpr .r17 = BitVec.ofNat 64 w ∧ s₁.gpr .r0 = 0 ∧ s₁.gpr .r14 = off P d ∧ s₁.mem = s.mem) ∧
        Keep [.r0, .r17] s s₁ := by
    refine WP.keep _ ?_ (by decide)
    prun [h11, h14]
    refine ⟨?_, rfl⟩
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    omega
  refine WP.mono hpre fun s₁ ⟨⟨i17, i0, i14, im⟩, k₁⟩ => ?_
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .r14 = off P (d + 8 * i) ∧ t.gpr .r0 = 0 ∧ Outside P d (8 * i) s.mem t.mem ∧
      (∀ k < i, word t.mem P (d + 8 * k) = 0) ∧ Keep [.r0, .r14, .r17] s t
  refine WP.mono (wp_countdown (body := .block ([.store .d .r0 .r14 0, .addi .r14 .r14 8] ++
      ([.subi .r17 .r17 1] : List Instr))) (cnt := .r17) (N := w) (by omega) (by omega) Inv
    (fun i hi t ⟨j14, j0, jout, jz, jk⟩ hc => ?_)
    ⟨by rw [i14]; rfl, i0, by rw [← im]; exact Outside.refl _ _ _ _, fun _ h => absurd h (by omega),
      k₁.mono⟩ i17) fun t ⟨t14, _, tout, tz, tk⟩ => ⟨⟨t14, tz, tout⟩, tk⟩
  have hst : WP isa (.block [.store .d .r0 .r14 0, .addi .r14 .r14 8, .subi .r17 .r17 1]) t
      fun t' => t' = ((({ t with mem := t.mem.writeW (off P (d + 8 * i)) (0 : BitVec 64) } : State).write
        .r14 (off P (d + 8 * i + 8))).write .r17 (t.gpr .r17 - BitVec.ofNat 64 1)) := by
    prun [j14, j0, (hs.congr jk.wr).st (show d + 8 * i + 8 ≤ Z by omega)]
  refine WP.mono hst fun t' e => ?_
  subst e
  have hw := writeW_outside t.mem P (d := d + 8 * i) 0 (by omega)
  refine ⟨⟨by gsimp; rw [show d + 8 * i + 8 = d + 8 * (i + 1) by omega], by gsimp; exact j0, ?_, ?_, ?_⟩,
    by gsimp⟩
  · gsimp; exact (jout.mono (Nat.le_refl _) (by omega)).trans (hw.mono (by omega) (by omega))
  · intro k hk
    gsimp
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · rw [hw.word (by omega) (by omega)]; exact jz k hk
    · exact word_writeW_self _ _ _ _
  · exact jk.trans' ((((Keep.mem _ _).trans (Keep.write _ _ _)).trans (Keep.write _ _ _)).mono)

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

theorem off_sub1 (P : Addr) {a : Nat} (h : 1 ≤ a) : off P a - BitVec.ofNat 64 1 = off P (a - 1) :=
  Offset.add_ofNat_sub P h

theorem write1_outside (m : Mem) (base : Addr) {d : Nat} (v : BitVec (8 * 1)) (h : d + 1 ≤ 2 ^ 64) :
    Outside base d 1 m (m.write (off base d) 1 v) := by
  intro x hx
  apply Mem.write_apply
  simp only [ofs] at hx
  have : (x - off base d).toNat = (2 ^ 64 - d + (x - base).toNat) % 2 ^ 64 :=
    Offset.toNat_sub_add x base (by omega)
  rw [this]
  have := (x - base).isLt
  rcases hx with hx | hx
  · rw [Nat.mod_eq_of_lt (by omega)]; omega
  · rw [show 2 ^ 64 - d + (x - base).toNat = (x - base).toNat - d + 2 ^ 64 by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    omega

theorem write1_self (m : Mem) (a : Addr) (v : BitVec (8 * 1)) : m.write a 1 v a = v := by
  simp only [Mem.write, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_lt_one, ite_true, Nat.mul_zero]
  apply BitVec.eq_of_toNat_eq; simp

theorem ofs_off0 (base : Addr) {d : Nat} (h : d < 2 ^ 64) : ofs base (off base d) = d :=
  Mem.sub_ofNat_toNat base h

/-- `loadN`, `n`'s `k` bytes at `N` (outside the working space): array 0 (at
`dA`) holds `n` as `2 w` digits. -/
theorem loadN_ok {s : State} {B N : Addr} {Z dA k w : Nat} (hs : Scr s B Z)
    (h10 : s.gpr .r10 = off B dA) (h12 : s.gpr .r12 = off N 0) (h6 : s.gpr .r6 = BitVec.ofNat 64 k)
    (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w)) (hk : 1 ≤ k) (hkw : k ≤ 8 * w) (hw' : w < 2 ^ 31)
    (hdA : 1 ≤ dA) (hZ : dA + 8 * w ≤ Z)
    (hN : ∀ i < k, InRegions (s.rd ++ s.wr) (off N i) 1)
    (hsep : ∀ i < k, ∀ x, ofs B x < Z → off N i ≠ x) :
    WP isa loadN s fun s' =>
      val32 s'.mem B dA (2 * w) = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem N k) ∧
        Outside B dA (8 * w) s.mem s'.mem ∧ Keep [.r0, .r14, .r15, .r16, .r17] s s' := by
  have hnw := hs.nowrap
  unfold loadN
  refine WP.seq ?_
  have hpre : WP isa (.block [.addi .r14 .r10 0]) s fun s₁ =>
      (s₁.gpr .r14 = off B dA ∧ s₁.mem = s.mem) ∧ Keep [.r14] s s₁ := by
    refine WP.keep _ ?_ (by decide)
    prun [h10]
  refine WP.mono hpre fun s₁ ⟨⟨i14, im⟩, k₁⟩ => ?_
  refine WP.seq (WP.mono (zeroWords_ok (hs.congr k₁.wr) i14 ((k₁.gpr _ (by decide)).trans h11)
    (by omega) hw' hZ) fun s₂ ⟨⟨_, hz, out₂⟩, k₂⟩ => ?_)
  rw [im] at out₂
  have k12 := k₁.trans k₂
  refine WP.seq ?_
  have hpre2 : WP isa (.block [.add .r15 .r10 .r6, .subi .r15 .r15 1, .addi .r16 .r12 0,
      .addi .r17 .r6 0]) s₂ fun s₃ =>
      (s₃.gpr .r15 = off B (dA + k - 1) ∧ s₃.gpr .r16 = off N 0 ∧ s₃.gpr .r17 = BitVec.ofNat 64 k ∧
        s₃.mem = s₂.mem) ∧ Keep [.r15, .r16, .r17] s₂ s₃ := by
    refine WP.keep _ ?_ (by decide)
    prun [k12.gpr .r10 (by decide), k12.gpr .r6 (by decide), k12.gpr .r12 (by decide), h10, h6, h12,
      BitVec.add_zero]
    exact off_sub1 _ (by omega)
  refine WP.mono hpre2 fun s₃ ⟨⟨j15, j16, j17, jm⟩, k₃⟩ => ?_
  have hs₃ := (hs.congr k12.wr).congr k₃.wr
  -- The bytes stored so far.
  let Inv : Nat → State → Prop := fun j t =>
    t.gpr .r15 = off B (dA + k - 1 - j) ∧ t.gpr .r16 = off N j ∧
      Outside B dA (8 * w) s.mem t.mem ∧
      (∀ i < j, t.mem (off B (dA + (k - 1 - i))) = s.mem (off N i)) ∧
      (∀ p, k ≤ p → p < 8 * w → t.mem (off B (dA + p)) = 0) ∧
      Keep [.r0, .r14, .r15, .r16, .r17] s t
  have hz' : ∀ p, p < 8 * w → s₂.mem (off B (dA + p)) = 0 := fun p hp => by
    have := byte_of_zero_word (hz (p / 8) (by omega)) (j := p % 8) (by omega)
    rwa [off_add, show dA + 8 * (p / 8) + p % 8 = dA + p by omega] at this
  refine WP.mono (wp_countdown (body := .block ([.lbz .r0 .r16 0, .stb .r0 .r15 0, .addi .r16 .r16 1,
      .subi .r15 .r15 1] ++ ([.subi .r17 .r17 1] : List Instr))) (cnt := .r17) (N := k) (by omega)
    (by omega) Inv (fun j hj t ⟨t15, t16, tout, tb, tz, tk⟩ hc => ?_)
    ⟨by rw [j15]; rfl, j16, by rw [jm]; exact out₂, fun _ h => absurd h (by omega),
      fun p _ hp => by rw [jm]; exact hz' p hp, (k12.trans k₃).mono⟩ j17)
    fun t ⟨_, _, tout, tb, tz, tk⟩ => ⟨?_, tout, tk⟩
  · have hst : WP isa (.block [.lbz .r0 .r16 0, .stb .r0 .r15 0, .addi .r16 .r16 1, .subi .r15 .r15 1,
        .subi .r17 .r17 1]) t fun t' => t' = ((({ (t.write .r0 ((t.mem.read (off N j) 1).setWidth 64)) with
          mem := t.mem.write (off B (dA + k - 1 - j)) 1 (((t.mem.read (off N j) 1).setWidth 64).setWidth 8) } :
            State).write .r16 (off N (j + 1))).write .r15
              (off B (dA + k - 1 - j) - BitVec.ofNat 64 1)).write .r17 (t.gpr .r17 - BitVec.ofNat 64 1) := by
      prun [t15, t16, exec_lbz' (show Reg.r16 ≠ .r0 by decide) (show 0 < 2 ^ 15 by decide),
        exec_stb (show Reg.r15 ≠ .r0 by decide) (show 0 < 2 ^ 15 by decide),
        (by rw [tk.rd, tk.wr]; exact hN j (by omega) : InRegions (t.rd ++ t.wr) (off N j) 1),
        (hs.congr tk.wr).st (d := dA + k - 1 - j) (n := 1) (by omega)]
    refine WP.mono hst fun t' e => ?_
    subst e
    have ha : dA + k - 1 - j = dA + (k - 1 - j) := by omega
    have hw1 := write1_outside t.mem B (d := dA + k - 1 - j)
      (((t.mem.read (off N j) 1).setWidth 64).setWidth 8) (by omega)
    have hNj : t.mem (off N j) = s.mem (off N j) := by
      refine tout _ (Or.inr ?_)
      have := (off N j - B).isLt
      by_contra hc
      exact hsep j (by omega) (off N j) (by simp only [ofs] at hc ⊢; omega) rfl
    refine ⟨⟨?_, by gsimp, ?_, ?_, ?_, ?_⟩, by gsimp⟩
    · gsimp; rw [off_sub1 _ (by omega), show dA + k - 1 - j - 1 = dA + k - 1 - (j + 1) by omega]
    · gsimp; exact tout.trans (hw1.mono (by omega) (by omega))
    · intro i hi
      gsimp
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · rw [hw1 _ (by rw [ofs_off0 B (by omega)]; omega)]; exact tb i hi
      · rw [← ha, write1_self, read_one', hNj]
    · intro p hp hp'
      gsimp
      rw [hw1 _ (by rw [ofs_off0 B (by omega)]; omega)]; exact tz p hp hp'
    · exact tk.trans' (((((((Keep.write _ _ _).trans (Keep.mem _ _)).trans (Keep.write _ _ _)).trans
        (Keep.write _ _ _)).trans (Keep.write _ _ _))).mono)
  · rw [← val32_off, val32_zero_extension t.mem (off B dA) (k := k) (by omega) fun p hp hp' => by
        rw [off_add]; exact tz p hp (by omega),
      reversed_read s.mem t.mem N (off B dA) k fun j hj => by
        rw [off_add, show dA + j = dA + (k - 1 - (k - 1 - j)) by omega, tb _ (by omega)]]

end VG.Proof.Bignum.PPC64LE
