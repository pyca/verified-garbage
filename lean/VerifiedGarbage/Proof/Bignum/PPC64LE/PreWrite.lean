module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Impl.Bignum.PPC64LE.Precompute
public import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Framework.Offset

/-!
# The precomputed values of an RSA modulus on PPC64LE: the output

`copyWords_ok`: `w` words from the working space to `pre`. `write_ok`: `n`
and `x` into `pre`. `zeroPre_ok`: `pre`'s `2 w` words := 0.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE

open VG VG.PPC64LE VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.Precompute

/-- A word of the working space, unchanged by writes to `pre`, which is apart
from it. -/
theorem Outside.word_sep {B P : Addr} {Z Zp o n : Nat} {m m' : Mem} (h : Outside P o n m m')
    (hsep : ∀ x, ofs B x < Z → Zp ≤ ofs P x) (hn : o + n ≤ Zp) {d : Nat} (hd : d + 8 ≤ Z)
    (hB : B.toNat + Z ≤ 2 ^ 64) : word m' B d = word m B d :=
  Mem.readW_congr fun i hi => h _ (Or.inr (Nat.le_trans hn
    (hsep _ (by rw [ofs_off B (d := d) (i := i) (by omega)]; omega))))

/-- `copyWords`, `w` words from `dS` of the working space (`r15`) to `dD` of
`pre` (`r14`), with `2 w` in `r11`. -/
theorem copyWords_ok {s : State} {B P : Addr} {Z Zp dS dD w : Nat} (hs : Scr s B Z) (hp : Scr s P Zp)
    (h15 : s.gpr .r15 = off B dS) (h14 : s.gpr .r14 = off P dD) (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w))
    (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hS : dS + 8 * w ≤ Z) (hD : dD + 8 * w ≤ Zp)
    (hsep : ∀ x, ofs B x < Z → Zp ≤ ofs P x) :
    WP isa copyWords s fun t =>
      (t.gpr .r14 = off P (dD + 8 * w) ∧ (∀ i < w, word t.mem P (dD + 8 * i) = word s.mem B (dS + 8 * i)) ∧
        Outside P dD (8 * w) s.mem t.mem) ∧ Keep [.r0, .r14, .r15, .r17] s t := by
  have hnw := hs.nowrap
  have hnp := hp.nowrap
  unfold copyWords
  refine WP.seq ?_
  have hpre : WP isa (.block [.lsr .d .r17 .r11 1]) s fun s₁ =>
      (s₁.gpr .r17 = BitVec.ofNat 64 w ∧ s₁.mem = s.mem) ∧ Keep [.r17] s s₁ := by
    refine WP.keep _ ?_ (by decide)
    prun [h11]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    omega
  refine WP.mono hpre fun s₁ ⟨⟨i17, im⟩, k₁⟩ => ?_
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .r14 = off P (dD + 8 * i) ∧ t.gpr .r15 = off B (dS + 8 * i) ∧ Outside P dD (8 * i) s.mem t.mem ∧
      (∀ k < i, word t.mem P (dD + 8 * k) = word s.mem B (dS + 8 * k)) ∧ Keep [.r0, .r14, .r15, .r17] s t
  refine WP.mono (wp_countdown (body := .block ([.load .d .r0 .r15 0, .store .d .r0 .r14 0, .addi .r14 .r14 8,
      .addi .r15 .r15 8] ++ ([.subi .r17 .r17 1] : List Instr))) (cnt := .r17) (N := w) (by omega) (by omega) Inv
    (fun i hi t ⟨j14, j15, jout, jc, jk⟩ hc => ?_)
    ⟨by rw [k₁.gpr .r14 (by decide), h14]; rfl, by rw [k₁.gpr .r15 (by decide), h15]; rfl,
      by rw [← im]; exact Outside.refl _ _ _ _, fun _ h => absurd h (by omega), k₁.mono⟩ i17)
    fun t ⟨t14, _, tout, tc, tk⟩ => ⟨⟨t14, tc, tout⟩, tk⟩
  have hsrc : word t.mem B (dS + 8 * i) = word s.mem B (dS + 8 * i) :=
    Outside.word_sep jout hsep (by omega) (by omega) hnw
  have hst : WP isa (.block [.load .d .r0 .r15 0, .store .d .r0 .r14 0, .addi .r14 .r14 8, .addi .r15 .r15 8,
      .subi .r17 .r17 1]) t
      fun t' => t' = ((({ (t.write .r0 (word t.mem B (dS + 8 * i))) with
        mem := t.mem.writeW (off P (dD + 8 * i)) (word t.mem B (dS + 8 * i)) } :
        State).write .r14 (off P (dD + 8 * i + 8))).write .r15
          (off B (dS + 8 * i + 8))).write .r17 (t.gpr .r17 - BitVec.ofNat 64 1) := by
    prun [j14, j15, (hs.congr jk.wr).ld (show dS + 8 * i + 8 ≤ Z by omega),
      (hp.congr jk.wr).st (show dD + 8 * i + 8 ≤ Zp by omega)]
  refine WP.mono hst fun t' e => ?_
  subst e
  have hw := writeW_outside t.mem P (d := dD + 8 * i) (word t.mem B (dS + 8 * i)) (by omega)
  refine ⟨⟨by gsimp; rw [show dD + 8 * i + 8 = dD + 8 * (i + 1) by omega],
    by gsimp; rw [show dS + 8 * i + 8 = dS + 8 * (i + 1) by omega], ?_, ?_, ?_⟩, by gsimp⟩
  · gsimp; exact (jout.mono (Nat.le_refl _) (by omega)).trans (hw.mono (by omega) (by omega))
  · intro k hk
    gsimp
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · rw [hw.word (by omega) (by omega)]; exact jc k hk
    · rw [word_writeW_self, hsrc]
  · exact jk.trans' (((((Keep.write _ _ _).trans (Keep.mem _ _)).trans (Keep.write _ _ _)).trans
      (Keep.write _ _ _)).trans (Keep.write _ _ _)).mono

/-- `write`, `n` at `dN` (`r10`) and `x` at `dX` (`r5`) of the working space,
into `pre` (`r3`). -/
theorem write_ok {s : State} {B P : Addr} {Z Zp dN dX w : Nat} (hs : Scr s B Z) (hp : Scr s P Zp)
    (h3 : s.gpr .r3 = off P 0) (h10 : s.gpr .r10 = off B dN) (h5 : s.gpr .r5 = off B dX)
    (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w)) (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hN : dN + 8 * w ≤ Z)
    (hX : dX + 8 * w ≤ Z) (hP : 16 * w ≤ Zp) (hsep : ∀ x, ofs B x < Z → Zp ≤ ofs P x) :
    WP isa write s fun t =>
      ((∀ i < w, word t.mem P (8 * i) = word s.mem B (dN + 8 * i)) ∧
        (∀ i < w, word t.mem P (8 * w + 8 * i) = word s.mem B (dX + 8 * i)) ∧
        Outside P 0 (16 * w) s.mem t.mem) ∧ Keep [.r0, .r14, .r15, .r17] s t := by
  have hnw := hs.nowrap
  have hnp := hp.nowrap
  unfold write
  refine WP.seq ?_
  have hpre : WP isa (.block [.addi .r14 .r3 0, .addi .r15 .r10 0]) s fun s₁ =>
      (s₁.gpr .r14 = off P 0 ∧ s₁.gpr .r15 = off B dN ∧ s₁.mem = s.mem) ∧ Keep [.r14, .r15] s s₁ := by
    refine WP.keep _ ?_ (by decide)
    prun [h3, h10, BitVec.add_zero]
  refine WP.mono hpre fun s₁ ⟨⟨i14, i15, im⟩, k₁⟩ => ?_
  refine WP.seq (WP.mono (copyWords_ok (dD := 0) (hs.congr k₁.wr) (hp.congr k₁.wr) i15 i14
    ((k₁.gpr _ (by decide)).trans h11) hw hw' hN (by omega) hsep) fun s₂ ⟨⟨j14, jc, jout⟩, k₂⟩ => ?_)
  have k12 := k₁.trans k₂
  refine WP.seq ?_
  have hmid : WP isa (.block [.addi .r15 .r5 0]) s₂ fun s₃ =>
      (s₃.gpr .r15 = off B dX ∧ s₃.mem = s₂.mem) ∧ Keep [.r15] s₂ s₃ := by
    refine WP.keep _ ?_ (by decide)
    prun [k12.gpr .r5 (by decide), h5, BitVec.add_zero]
  refine WP.mono hmid fun s₃ ⟨⟨l15, lm⟩, k₃⟩ => ?_
  have k13 := k12.trans k₃
  refine WP.mono (copyWords_ok (dD := 0 + 8 * w) (hs.congr k13.wr) (hp.congr k13.wr) l15
    ((k₃.gpr _ (by decide)).trans j14) ((k13.gpr _ (by decide)).trans h11) hw hw' hX (by omega) hsep)
    fun t ⟨⟨_, tc, tout⟩, k₄⟩ => ⟨⟨fun i hi => ?_, fun i hi => ?_, ?_⟩, (k13.trans k₄).mono⟩
  · rw [tout.word (by omega) (by omega), lm]
    have := jc i hi
    rwa [Nat.zero_add, im] at this
  · rw [show 8 * w + 8 * i = 0 + 8 * w + 8 * i by omega, tc i hi, lm,
      Outside.word_sep jout hsep (by omega) (by omega) hnw, im]
  · rw [im] at jout
    rw [lm] at tout
    exact (jout.mono (by omega) (by omega)).trans (tout.mono (by omega) (by omega))

/-- `zeroPre`: `pre`'s (`r3`) `2 w` words := 0. -/
theorem zeroPre_ok {s : State} {P : Addr} {Zp w : Nat} (hp : Scr s P Zp)
    (h3 : s.gpr .r3 = off P 0) (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w)) (hw : 1 ≤ w)
    (hw' : w < 2 ^ 31) (hP : 16 * w ≤ Zp) :
    WP isa zeroPre s fun t =>
      ((∀ i < 2 * w, word t.mem P (8 * i) = 0) ∧ Outside P 0 (16 * w) s.mem t.mem) ∧
        Keep [.r0, .r14, .r17] s t := by
  have hnp := hp.nowrap
  unfold zeroPre
  refine WP.seq ?_
  have hpre : WP isa (.block [.addi .r14 .r3 0]) s fun s₁ =>
      (s₁.gpr .r14 = off P 0 ∧ s₁.mem = s.mem) ∧ Keep [.r14] s s₁ := by
    refine WP.keep _ ?_ (by decide)
    prun [h3, BitVec.add_zero]
  refine WP.mono hpre fun s₁ ⟨⟨i14, im⟩, k₁⟩ => ?_
  refine WP.seq (WP.mono (zeroWords_ok (hp.congr k₁.wr) i14 ((k₁.gpr _ (by decide)).trans h11) hw hw'
    (by omega)) fun s₂ ⟨⟨j14, jz, jout⟩, k₂⟩ => ?_)
  have k12 := k₁.trans k₂
  refine WP.mono (zeroWords_ok (hp.congr k12.wr) j14 ((k12.gpr _ (by decide)).trans h11) hw hw'
    (by omega)) fun t ⟨⟨_, tz, tout⟩, k₃⟩ => ⟨⟨fun i hi => ?_, ?_⟩, (k12.trans k₃).mono⟩
  · rcases Nat.lt_or_ge i w with h | h
    · have := jz i h
      rw [Nat.zero_add] at this
      exact (tout.word (d := 8 * i) (by omega) (by omega)).trans this
    · have := tz (i - w) (by omega)
      rwa [show 0 + 8 * w + 8 * (i - w) = 8 * i by omega] at this
  · rw [im] at jout
    exact (jout.mono (by omega) (by omega)).trans (tout.mono (by omega) (by omega))

end VG.Proof.Bignum.PPC64LE
