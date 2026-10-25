module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Impl.Bignum.PPC64LE.Precompute
public import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Framework.Offset

/-! # A prime search on PPC64LE: `copyWords` within the working space -/

@[expose] public section

namespace VG.Proof.MillerRabin.PPC64LE.Search

open VG VG.PPC64LE VG.Impl.Bignum.PPC64LE.Precompute VG.Proof.Bignum VG.Proof.Bignum.PPC64LE

/-- `copyWords`, `w` words from `dS` (`r15`) to `dD` (`r14`) of the working
space, apart, with `2 w` in `r11`. -/
theorem copyWithin_ok {s : State} {B : Addr} {Z dS dD w : Nat} (hs : Scr s B Z)
    (h15 : s.gpr .r15 = off B dS) (h14 : s.gpr .r14 = off B dD) (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w))
    (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hS : dS + 8 * w ≤ Z) (hD : dD + 8 * w ≤ Z)
    (hsep : dS + 8 * w ≤ dD ∨ dD + 8 * w ≤ dS) :
    WP isa copyWords s fun t =>
      (t.gpr .r14 = off B (dD + 8 * w) ∧ (∀ i < w, word t.mem B (dD + 8 * i) = word s.mem B (dS + 8 * i)) ∧
        Outside B dD (8 * w) s.mem t.mem) ∧ Keep [.r0, .r14, .r15, .r17] s t := by
  have hnw := hs.nowrap
  unfold copyWords
  refine WP.seq ?_
  have hpre : WP isa (.block [.lsr .d .r17 .r11 1]) s fun s₁ =>
      (s₁.gpr .r17 = BitVec.ofNat 64 w ∧ s₁.mem = s.mem) ∧ Keep [.r17] s s₁ := by
    refine WP.keep _ ?_ (by decide)
    prun [h11]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    omega_arith
  refine WP.mono hpre fun s₁ ⟨⟨i17, im⟩, k₁⟩ => ?_
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .r14 = off B (dD + 8 * i) ∧ t.gpr .r15 = off B (dS + 8 * i) ∧ Outside B dD (8 * i) s.mem t.mem ∧
      (∀ k < i, word t.mem B (dD + 8 * k) = word s.mem B (dS + 8 * k)) ∧ Keep [.r0, .r14, .r15, .r17] s t
  refine WP.mono (wp_countdown (body := .block ([.load .d .r0 .r15 0, .store .d .r0 .r14 0, .addi .r14 .r14 8,
      .addi .r15 .r15 8] ++ ([.subi .r17 .r17 1] : List Instr))) (cnt := .r17) (N := w) (by omega_arith) (by omega_arith) Inv
    (fun i hi t ⟨j14, j15, jout, jc, jk⟩ hc => ?_)
    ⟨by rw [k₁.gpr .r14 (by decide), h14]; rfl, by rw [k₁.gpr .r15 (by decide), h15]; rfl,
      by rw [← im]; exact Outside.refl _ _ _ _, fun _ h => absurd h (by omega_arith), k₁.mono⟩ i17)
    fun t ⟨t14, _, tout, tc, tk⟩ => ⟨⟨t14, tc, tout⟩, tk⟩
  have hsrc : word t.mem B (dS + 8 * i) = word s.mem B (dS + 8 * i) :=
    jout.word (by omega_arith) (by omega_arith)
  have hst : WP isa (.block [.load .d .r0 .r15 0, .store .d .r0 .r14 0, .addi .r14 .r14 8, .addi .r15 .r15 8,
      .subi .r17 .r17 1]) t
      fun t' => t' = ((({ (t.write .r0 (word t.mem B (dS + 8 * i))) with
        mem := t.mem.writeW (off B (dD + 8 * i)) (word t.mem B (dS + 8 * i)) } :
        State).write .r14 (off B (dD + 8 * i + 8))).write .r15
          (off B (dS + 8 * i + 8))).write .r17 (t.gpr .r17 - BitVec.ofNat 64 1) := by
    prun [j14, j15, (hs.congr jk.wr).ld (show dS + 8 * i + 8 ≤ Z by omega_arith),
      (hs.congr jk.wr).st (show dD + 8 * i + 8 ≤ Z by omega_arith)]
  refine WP.mono hst fun t' e => ?_
  subst e
  have hw := writeW_outside t.mem B (d := dD + 8 * i) (word t.mem B (dS + 8 * i)) (by omega_arith)
  refine ⟨⟨by gsimp; rw [show dD + 8 * i + 8 = dD + 8 * (i + 1) by omega_arith],
    by gsimp; rw [show dS + 8 * i + 8 = dS + 8 * (i + 1) by omega_arith], ?_, ?_, ?_⟩, by gsimp⟩
  · gsimp; exact (jout.mono (Nat.le_refl _) (by omega_arith)).trans (hw.mono (by omega_arith) (by omega_arith))
  · intro k hk
    gsimp
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · rw [hw.word (by omega_arith) (by omega_arith)]; exact jc k hk
    · rw [word_writeW_self, hsrc]
  · exact jk.trans' (((((Keep.write _ _ _).trans (Keep.mem _ _)).trans (Keep.write _ _ _)).trans
      (Keep.write _ _ _)).trans (Keep.write _ _ _)).mono

end VG.Proof.MillerRabin.PPC64LE.Search
