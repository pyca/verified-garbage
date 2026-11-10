module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Impl.Bignum.PPC64LE.Crt
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMont
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubLoad
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# The RSA private-key operation on PPC64LE: the cached `R² mod p`

`r2Copy_ok`: `vg_rsa_private_crt_precomputed`'s `R² mod p` into array 1 of
a prime's working space, from `w` words of a read-only buffer apart from it,
under the mask `r26` of `b`: the buffer's number if `b`, else 1.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Crt

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.Crt
open VG.Proof.Bignum.PPC64LE

/-- `n` words, the lowest 1 and the others 0, are 1. -/
theorem wv_one_low {m : Mem} {p : Addr} {d : Nat} :
    ∀ {n : Nat}, 1 ≤ n → word m p d = 1#64 → (∀ i < n, 1 ≤ i → word m p (d + 8 * i) = 0#64) → wv m p d n = 1
  | 1, _, h0, _ => by simp [wv, h0]
  | n + 2, _, h0, h => by
    rw [wv, wv_one_low (n := n + 1) (by omega_arith) h0 fun i hi hi1 => h i (by omega_arith) hi1,
      h (n + 1) (by omega_arith) (by omega_arith)]
    simp

/-- The word `r2Copy` writes at index `k`, from the buffer's word `x`, under
the mask `m`. -/
abbrev r2Word (m x : BitVec 64) (k : Nat) : BitVec 64 :=
  (x &&& m) ||| (if k = 0 then (BitVec.ofNat 64 0 - BitVec.ofNat 64 1 ^^^ m) &&& 1#64 else 0#64)

/-- What `r2Copy`'s words are, as a number. -/
theorem r2_words {mt ms : Mem} {B P : Addr} {w : Nat} {b : Bool} {m : BitVec 64} (hw : 1 ≤ w)
    (h26 : m = BitVec.ofNat 64 0 - BitVec.ofNat 64 (if b then 1 else 0))
    (tc : ∀ k < w, word mt B (slot w 1 + 8 * k) = r2Word m (word ms P (8 * k)) k) :
    wv mt B (slot w 1) w = (if b then wv ms P 0 w else 1) := by
  subst h26
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte] at tc ⊢
    have c1 : (BitVec.ofNat 64 0 - BitVec.ofNat 64 1 ^^^ BitVec.ofNat 64 0) &&& 1#64 = 1#64 := by decide
    have t0 := tc 0 (by omega_arith)
    rw [Nat.mul_zero, Nat.add_zero] at t0
    refine wv_one_low (m := mt) (p := B) (d := slot w 1) hw (by
      rw [t0]; simp only [r2Word, BitVec.sub_self, BitVec.and_zero, BitVec.zero_or, ↓reduceIte, c1]) fun i hi hi1 => ?_
    rw [tc i hi]
    simp only [r2Word, BitVec.sub_self, BitVec.and_zero, BitVec.zero_or, show i ≠ 0 by omega_arith, ↓reduceIte]
  · simp only [↓reduceIte] at tc ⊢
    refine wv_congr2 fun i hi => ?_
    rw [Nat.zero_add, tc i hi]
    have h1 : BitVec.ofNat 64 0 - BitVec.ofNat 64 1 = BitVec.allOnes 64 := by decide
    simp only [r2Word, h1, BitVec.and_allOnes, BitVec.xor_self, BitVec.zero_and, ite_self, BitVec.or_zero]

/-- `r2Copy`, in a working space at `B` of `w` words (array 0 in `r10`, an
array's size in `r29`, `2 w` in `r11`), from the `w` words at `P` (`r15`),
readable and apart from it, under the mask of `b` (`r26`): array 1 holds
the buffer's number if `b`, else 1. -/
theorem r2Copy_ok {s : State} {B P : Addr} {Z w : Nat} {b : Bool} (hs : Scr s B Z)
    (hP : P.toNat + 8 * w ≤ 2 ^ 64) (hrd : ∀ i < w, InRegions (s.rd ++ s.wr) (off P (8 * i)) 8)
    (hsep : ∀ x, ofs P x < 8 * w → Z ≤ ofs B x)
    (h15 : s.gpr .r15 = off P 0) (h10 : s.gpr .r10 = off B (slot w 0))
    (h29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2))) (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w))
    (h26 : s.gpr .r26 = BitVec.ofNat 64 0 - BitVec.ofNat 64 (if b then 1 else 0))
    (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hZ : slot w 2 ≤ Z) :
    WP isa r2Copy s fun t =>
      (wv t.mem B (slot w 1) w = (if b then wv s.mem P 0 w else 1) ∧
        Outside B (slot w 1) (8 * w) s.mem t.mem) ∧ Keep [.r0, .r3, .r4, .r14, .r15, .r17] s t := by
  have hnw := hs.nowrap
  have e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  have e1 := e 1; have e2 := e 2
  have hh : hdrBytes = 256 := rfl
  unfold r2Copy
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .r14) (by decide) (by decide) h10 h29 1) fun s₁ ⟨⟨a14, m1⟩, k1⟩ => ?_
  have hpre : WP isa (.block [.li .r3 0, .subi .r3 .r3 1, .logic .xor .r3 .r3 .r26, .li .r4 1,
      .logic .and .r3 .r3 .r4, .lsr .d .r17 .r11 1]) s₁ fun s₂ =>
      (s₂.gpr .r17 = BitVec.ofNat 64 w ∧
        s₂.gpr .r3 = (BitVec.ofNat 64 0 - BitVec.ofNat 64 1 ^^^ s.gpr .r26) &&& 1#64 ∧ s₂.mem = s₁.mem) ∧
        Keep [.r3, .r4, .r17] s₁ s₂ := by
    refine WP.keep _ ?_ (by decide)
    prun [(k1.gpr .r26 (by decide)), (k1.gpr .r11 (by decide)).trans h11]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    omega_arith
  refine WP.mono hpre fun s₂ ⟨⟨i17, i3, im⟩, k₂⟩ => ?_
  have k12 := k1.trans k₂
  have g26 : ∀ {t : State}, Keep [.r0, .r3, .r4, .r14, .r15, .r17] s t → t.gpr .r26 = s.gpr .r26 :=
    fun k => k.gpr _ (by decide)
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .r14 = off B (slot w 1 + 8 * i) ∧ t.gpr .r15 = off P (8 * i) ∧
      t.gpr .r3 = (if i = 0 then (BitVec.ofNat 64 0 - BitVec.ofNat 64 1 ^^^ s.gpr .r26) &&& 1#64 else 0#64) ∧
      Outside B (slot w 1) (8 * i) s.mem t.mem ∧
      (∀ k < i, word t.mem B (slot w 1 + 8 * k) = r2Word (s.gpr .r26) (word s.mem P (8 * k)) k) ∧
      Keep [.r0, .r3, .r4, .r14, .r15, .r17] s t
  refine WP.mono (wp_countdown (body := .block ([.load .d .r0 .r15 0, .logic .and .r0 .r0 .r26,
      .logic .or .r0 .r0 .r3, .store .d .r0 .r14 0, .li .r3 0, .addi .r14 .r14 8, .addi .r15 .r15 8] ++
      ([.subi .r17 .r17 1] : List Instr))) (cnt := .r17) (N := w) (by omega_arith) (by omega_arith) Inv
    (fun i hi t ⟨j14, j15, j3, jout, jc, jk⟩ hc => ?_)
    ⟨by rw [k₂.gpr .r14 (by decide), a14]; rfl, by rw [k12.gpr .r15 (by decide), h15],
      by rw [i3]; rfl, by rw [im, m1]; exact Outside.refl _ _ _ _, fun _ h => absurd h (by omega_arith),
      k12.mono⟩ i17) fun t ⟨_, _, _, tout, tc, tk⟩ => ⟨⟨r2_words hw h26 tc, tout⟩, tk⟩
  have hsrc : word t.mem P (8 * i) = word s.mem P (8 * i) :=
    Pub.Outside.word_apart jout hsep (by omega_arith) (by omega_arith) hP
  have hst : WP isa (.block [.load .d .r0 .r15 0, .logic .and .r0 .r0 .r26, .logic .or .r0 .r0 .r3,
      .store .d .r0 .r14 0, .li .r3 0, .addi .r14 .r14 8, .addi .r15 .r15 8, .subi .r17 .r17 1]) t
      fun t' => t' = (((({ (((t.write .r0 (word t.mem P (8 * i))).write .r0 (word t.mem P (8 * i) &&& t.gpr .r26)).write
          .r0 ((word t.mem P (8 * i) &&& t.gpr .r26) ||| t.gpr .r3)) with
        mem := t.mem.writeW (off B (slot w 1 + 8 * i)) ((word t.mem P (8 * i) &&& t.gpr .r26) ||| t.gpr .r3) } :
        State).write .r3 (BitVec.ofNat 64 0)).write .r14 (off B (slot w 1 + 8 * i + 8))).write .r15
          (off P (8 * i + 8))).write .r17 (t.gpr .r17 - BitVec.ofNat 64 1) := by
    prun [j14, j15, (by rw [jk.rd, jk.wr]; exact hrd i hi : InRegions (t.rd ++ t.wr) (off P (8 * i)) 8),
      (hs.congr jk.wr).st (show slot w 1 + 8 * i + 8 ≤ Z by omega_arith)]
  refine WP.mono hst fun t' ee => ?_
  subst ee
  have hw := writeW_outside t.mem B (d := slot w 1 + 8 * i) ((word t.mem P (8 * i) &&& t.gpr .r26) ||| t.gpr .r3)
    (by omega_arith)
  refine ⟨⟨by gsimp; rw [show slot w 1 + 8 * i + 8 = slot w 1 + 8 * (i + 1) by omega_arith],
    by gsimp; rw [show 8 * i + 8 = 8 * (i + 1) by omega_arith], by gsimp, ?_, ?_, ?_⟩, by gsimp⟩
  · gsimp; exact (jout.mono (Nat.le_refl _) (by omega_arith)).trans (hw.mono (by omega_arith) (by omega_arith))
  · intro k hk
    gsimp
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · rw [hw.word (by omega_arith) (by omega_arith)]; exact jc k hk
    · rw [word_writeW_self, hsrc, j3, g26 jk]
  · exact jk.trans' ((((((((Keep.write _ _ _).trans (Keep.write _ _ _)).trans (Keep.write _ _ _)).trans
      (Keep.mem _ _)).trans (Keep.write _ _ _)).trans (Keep.write _ _ _)).trans (Keep.write _ _ _)).trans
      (Keep.write _ _ _)).mono

end VG.Proof.Bignum.PPC64LE.Crt
