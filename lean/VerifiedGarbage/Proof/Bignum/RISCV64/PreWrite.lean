module

public import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public import VerifiedGarbage.Impl.Bignum.RISCV64.Precompute
public import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The precomputed values of an RSA modulus on RISC-V: writing `pre`

`copyWords_ok`: `w` words from the working space to `pre`. `write_ok`: `n`
and `x` into `pre`. `zeroPre_ok`: `pre`'s `2 w` words := 0.
-/

@[expose] public section

namespace VG.Proof.Bignum.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Impl.Bignum.RISCV64
  VG.Impl.Bignum.RISCV64.Precompute

/-- A word of the working space, unchanged by writes to `pre`, which is apart
from it. -/
theorem Outside.word_sep {B P : Addr} {Z Zp o n : Nat} {m m' : Mem} (h : Outside P o n m m')
    (hsep : ∀ x, ofs B x < Z → Zp ≤ ofs P x) (hn : o + n ≤ Zp) {d : Nat} (hd : d + 8 ≤ Z)
    (hB : B.toNat + Z ≤ 2 ^ 64) : word m' B d = word m B d :=
  Mem.readW_congr fun i hi => h _ (Or.inr (Nat.le_trans hn
    (hsep _ (by rw [ofs_off B (d := d) (i := i) (by omega_arith)]; omega_arith))))

/-- `copyWords`, `w` words from `dS` of the working space (`t4`) to `dD` of
`pre` (`t3`), with `w` in `t0`. -/
theorem copyWords_ok {s : State} {B P : Addr} {Z Zp dS dD w : Nat} (hs : Scr s B Z) (hp : Scr s P Zp)
    (h4 : s.gpr .t4 = off B dS) (h3 : s.gpr .t3 = off P dD) (h0 : s.gpr .t0 = BitVec.ofNat 64 w)
    (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hS8 : dS % 8 = 0) (hD8 : dD % 8 = 0) (hS : dS + 8 * w ≤ Z)
    (hD : dD + 8 * w ≤ Zp) (hsep : ∀ x, ofs B x < Z → Zp ≤ ofs P x) :
    WP isa copyWords s fun t =>
      (t.gpr .t3 = off P (dD + 8 * w) ∧ (∀ i < w, word t.mem P (dD + 8 * i) = word s.mem B (dS + 8 * i)) ∧
        Outside P dD (8 * w) s.mem t.mem) ∧ Keep [.s0, .t3, .t4, .t5] s t := by
  have hnw := hs.nowrap
  have hnp := hp.nowrap
  unfold copyWords
  refine WP.seq ?_
  have hpre : WP isa (.block [.addi .t5 .t0 0]) s fun s₁ =>
      (s₁.gpr .t5 = BitVec.ofNat 64 w ∧ s₁.mem = s.mem) ∧ Keep [.t5] s s₁ := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [h0, add_ofNat_zero]
  refine WP.mono hpre fun s₁ ⟨⟨i5, im⟩, k₁⟩ => ?_
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .t3 = off P (dD + 8 * i) ∧ t.gpr .t4 = off B (dS + 8 * i) ∧ Outside P dD (8 * i) s.mem t.mem ∧
      (∀ k < i, word t.mem P (dD + 8 * k) = word s.mem B (dS + 8 * k)) ∧ Keep [.s0, .t3, .t4, .t5] s t
  refine WP.mono (wp_countdown (body := .block ([.load .d .s0 .t4 0, .store .d .s0 .t3 0, .addi .t3 .t3 8,
      .addi .t4 .t4 8] ++ ([.addi .t5 .t5 (-1)] : List Instr))) (cnt := .t5) (N := w) (by omega_arith)
      (by omega_arith) Inv (fun i hi t ⟨j3, j4, jout, jc, jk⟩ hc => ?_)
    ⟨by rw [k₁.gpr (r := .t3) (by decide), h3]; rfl, by rw [k₁.gpr (r := .t4) (by decide), h4]; rfl,
      by rw [← im]; exact Outside.refl _ _ _ _, fun _ h => absurd h (by omega_arith), k₁.mono (by decide)⟩ i5)
    fun t ⟨t3, _, tout, tc, tk⟩ => ⟨⟨t3, tc, tout⟩, tk⟩
  have hsrc : word t.mem B (dS + 8 * i) = word s.mem B (dS + 8 * i) :=
    Outside.word_sep jout hsep (by omega_arith) (by omega_arith) hnw
  have hst : WP isa (.block [.load .d .s0 .t4 0, .store .d .s0 .t3 0, .addi .t3 .t3 8, .addi .t4 .t4 8,
      .addi .t5 .t5 (-1)]) t
      fun t' => t' = ((({ (t.write .s0 (word t.mem B (dS + 8 * i))) with
        mem := t.mem.writeW (off P (dD + 8 * i)) (word t.mem B (dS + 8 * i)) } :
        State).write .t3 (off P (dD + 8 * i + 8))).write .t4
          (off B (dS + 8 * i + 8))).write .t5 (t.gpr .t5 - BitVec.ofNat 64 1) := by
    brun [j3, j4, (hs.congr jk.2.2).ld (show dS + 8 * i + 8 ≤ Z by omega_arith),
      (hp.congr jk.2.2).st (show dD + 8 * i + 8 ≤ Zp by omega_arith),
      (hs.congr jk.2.2).al8 (show dS + 8 * i + 8 ≤ Z by omega_arith) (by omega_arith),
      (hp.congr jk.2.2).al8 (show dD + 8 * i + 8 ≤ Zp by omega_arith) (by omega_arith)]
  refine WP.mono hst fun t' e => ?_
  subst e
  have hw := writeW_outside t.mem P (d := dD + 8 * i) (word t.mem B (dS + 8 * i)) (by omega_arith)
  refine ⟨⟨by gsimp; rw [show dD + 8 * i + 8 = dD + 8 * (i + 1) by omega_arith],
    by gsimp; rw [show dS + 8 * i + 8 = dS + 8 * (i + 1) by omega_arith], ?_, ?_, ?_⟩, by gsimp⟩
  · gsimp; exact (jout.mono (Nat.le_refl _) (by omega_arith)).trans (hw.mono (by omega_arith) (by omega_arith))
  · intro k hk
    gsimp
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · rw [hw.word (by omega_arith) (by omega_arith)]; exact jc k hk
    · rw [word_writeW_self, hsrc]
  · exact Keep.trans' jk ((((((Keep.write _ _ _).trans (Keep.mem _ _)).trans (Keep.write _ _ _)).trans
      (Keep.write _ _ _)).trans (Keep.write _ _ _)).mono (by decide))

/-- `write`, `n` at `dN` (`a7`) and `x` at `dX` (`a2`) of the working space,
into `pre` (`s5`). -/
theorem write_ok {s : State} {B P : Addr} {Z Zp dN dX w : Nat} (hs : Scr s B Z) (hp : Scr s P Zp)
    (h5 : s.gpr .s5 = off P 0) (h17 : s.gpr .a7 = off B dN) (h12 : s.gpr .a2 = off B dX)
    (h0 : s.gpr .t0 = BitVec.ofNat 64 w) (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hN8 : dN % 8 = 0)
    (hX8 : dX % 8 = 0) (hN : dN + 8 * w ≤ Z) (hX : dX + 8 * w ≤ Z) (hP : 16 * w ≤ Zp)
    (hsep : ∀ x, ofs B x < Z → Zp ≤ ofs P x) :
    WP isa write s fun t =>
      ((∀ i < w, word t.mem P (8 * i) = word s.mem B (dN + 8 * i)) ∧
        (∀ i < w, word t.mem P (8 * w + 8 * i) = word s.mem B (dX + 8 * i)) ∧
        Outside P 0 (16 * w) s.mem t.mem) ∧ Keep [.s0, .t3, .t4, .t5] s t := by
  have hnw := hs.nowrap
  have hnp := hp.nowrap
  unfold write
  refine WP.seq ?_
  have hpre : WP isa (.block [.addi .t3 .s5 0, .addi .t4 .a7 0]) s fun s₁ =>
      (s₁.gpr .t3 = off P 0 ∧ s₁.gpr .t4 = off B dN ∧ s₁.mem = s.mem) ∧ Keep [.t3, .t4] s s₁ := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [h5, h17, add_ofNat_zero]
  refine WP.mono hpre fun s₁ ⟨⟨i3, i4, im⟩, k₁⟩ => ?_
  refine WP.seq (WP.mono (copyWords_ok (dD := 0) (hs.congr k₁.2.2) (hp.congr k₁.2.2) i4 i3
    ((k₁.gpr (r := .t0) (by decide)).trans h0) hw hw' hN8 (by decide) hN (by omega_arith) hsep)
    fun s₂ ⟨⟨j3, jc, jout⟩, k₂⟩ => ?_)
  have k12 := k₁.trans k₂
  refine WP.seq ?_
  have hmid : WP isa (.block [.addi .t4 .a2 0]) s₂ fun s₃ =>
      (s₃.gpr .t4 = off B dX ∧ s₃.mem = s₂.mem) ∧ Keep [.t4] s₂ s₃ := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [k12.gpr (r := .a2) (by decide), h12, add_ofNat_zero]
  refine WP.mono hmid fun s₃ ⟨⟨l4, lm⟩, k₃⟩ => ?_
  have k13 := k12.trans k₃
  refine WP.mono (copyWords_ok (dD := 0 + 8 * w) (hs.congr k13.2.2) (hp.congr k13.2.2) l4
    ((k₃.gpr (r := .t3) (by decide)).trans j3) ((k13.gpr (r := .t0) (by decide)).trans h0) hw hw' hX8
    (by omega_arith) hX (by omega_arith) hsep)
    fun t ⟨⟨_, tc, tout⟩, k₄⟩ => ⟨⟨fun i hi => ?_, fun i hi => ?_, ?_⟩, (k13.trans k₄).mono (by decide)⟩
  · rw [tout.word (by omega_arith) (by omega_arith), lm]
    have := jc i hi
    rwa [Nat.zero_add, im] at this
  · rw [show 8 * w + 8 * i = 0 + 8 * w + 8 * i by omega_arith, tc i hi, lm,
      Outside.word_sep jout hsep (by omega_arith) (by omega_arith) hnw, im]
  · rw [im] at jout
    rw [lm] at tout
    exact (jout.mono (by omega_arith) (by omega_arith)).trans (tout.mono (by omega_arith) (by omega_arith))

/-- `zeroPre`: `pre`'s (`s5`) `2 w` words := 0. -/
theorem zeroPre_ok {s : State} {P : Addr} {Zp w : Nat} (hp : Scr s P Zp)
    (h5 : s.gpr .s5 = off P 0) (h0 : s.gpr .t0 = BitVec.ofNat 64 w) (hw : 1 ≤ w)
    (hw' : w < 2 ^ 31) (hP : 16 * w ≤ Zp) :
    WP isa zeroPre s fun t =>
      ((∀ i < 2 * w, word t.mem P (8 * i) = 0) ∧ Outside P 0 (16 * w) s.mem t.mem) ∧
        Keep [.s0, .t3, .t5] s t := by
  have hnp := hp.nowrap
  unfold zeroPre
  refine WP.seq ?_
  have hpre : WP isa (.block [.addi .t3 .s5 0]) s fun s₁ =>
      (s₁.gpr .t3 = off P 0 ∧ s₁.mem = s.mem) ∧ Keep [.t3] s s₁ := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [h5, add_ofNat_zero]
  refine WP.mono hpre fun s₁ ⟨⟨i3, im⟩, k₁⟩ => ?_
  refine WP.seq (WP.mono (zeroWords_ok (hp.congr k₁.2.2) i3 ((k₁.gpr (r := .t0) (by decide)).trans h0) hw hw'
    (by decide) (by omega_arith)) fun s₂ ⟨⟨j3, jz, jout⟩, k₂⟩ => ?_)
  have k12 := k₁.trans k₂
  refine WP.mono (zeroWords_ok (hp.congr k12.2.2) j3 ((k12.gpr (r := .t0) (by decide)).trans h0) hw hw'
    (by omega_arith) (by omega_arith)) fun t ⟨⟨_, tz, tout⟩, k₃⟩ =>
      ⟨⟨fun i hi => ?_, ?_⟩, (k12.trans k₃).mono (by decide)⟩
  · rcases Nat.lt_or_ge i w with h | h
    · have := jz i h
      rw [Nat.zero_add] at this
      exact (tout.word (d := 8 * i) (by omega_arith) (by omega_arith)).trans this
    · have := tz (i - w) (by omega_arith)
      rwa [show 0 + 8 * w + 8 * (i - w) = 8 * i by omega_arith] at this
  · rw [im] at jout
    exact (jout.mono (by omega_arith) (by omega_arith)).trans (tout.mono (by omega_arith) (by omega_arith))

end VG.Proof.Bignum.RISCV64
