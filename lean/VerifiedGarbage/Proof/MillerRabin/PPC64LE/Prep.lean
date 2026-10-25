module

public import VerifiedGarbage.Impl.MillerRabin.PPC64LE.Prep
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Last
import VerifiedGarbage.Proof.RsaKeyGen.Halve
import VerifiedGarbage.Proof.RsaKeyGen.MrMont
import VerifiedGarbage.Proof.RsaKeyGen.MillerRabin
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCore
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Exp

/-!
# Miller–Rabin's exponent on PPC64LE

As `Proof/RsaKeyGen/AArch64/MrShift.lean`: `lowWord_ok`, the lowest nonzero
word of `c − 1`; `halfPass_ok`, `[r16] := r9 ? [r15] / 2 : [r15]`, in place
or not; `expSetup_ok`, `E = (c − 1) / 2^σ` in array 27 and the lowest set bit
of `c − 1`'s lowest nonzero word after it.
-/

@[expose] public section

namespace VG.Proof.MillerRabin.PPC64LE

open VG VG.PPC64LE VG.Proof.Bignum.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.MillerRabin.PPC64LE
open VG.Proof.Bignum (slot slot_sep wv wv_lt wv_congr word_of_wv)
open VG.Proof.RsaKeyGen (mrE mrA mrSig sigOf)
open VG.Proof.Mont (off Outside word writeW_outside word_writeW_self)

/-- The mask of a word being zero. -/
theorem z64_mask (x : BitVec 64) :
    BitVec.ofNat 64 0 - ((x >>> 1 ||| x &&& BitVec.ofNat 64 1) - BitVec.ofNat 64 1) >>> 63 =
      mask (decide (x = 0)) := by
  have ht : (x >>> 1 ||| x &&& BitVec.ofNat 64 1).toNat < 2 ^ 63 := by
    rw [BitVec.toNat_or]
    apply Nat.or_lt_two_pow
    · rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; have := x.isLt; omega_arith
    · rw [BitVec.toNat_and]; exact Nat.lt_of_le_of_lt (Nat.and_le_right) (by decide)
  have hz : (x >>> 1 ||| x &&& BitVec.ofNat 64 1).toNat = 0 ↔ x = 0 := by
    constructor
    · intro h
      have h1 : (x >>> 1).toNat = 0 ∧ (x &&& BitVec.ofNat 64 1).toNat = 0 := by
        rw [BitVec.toNat_or] at h; exact Nat.or_eq_zero_iff.mp h
      have a : (x >>> 1).toNat = x.toNat / 2 := by
        rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
      have b : (x &&& BitVec.ofNat 64 1).toNat = x.toNat % 2 := by
        rw [BitVec.toNat_and, show (BitVec.ofNat 64 1).toNat = 1 from rfl, Nat.and_one_is_mod]
      apply BitVec.eq_of_toNat_eq
      rw [show (0 : BitVec 64).toNat = 0 from rfl]
      omega_arith
    · rintro rfl; rfl
  by_cases e : x = 0
  · subst e; decide
  · have hne : (x >>> 1 ||| x &&& BitVec.ofNat 64 1).toNat ≠ 0 := fun h => e (hz.mp h)
    have hs : ((x >>> 1 ||| x &&& BitVec.ofNat 64 1) - BitVec.ofNat 64 1) >>> 63 = BitVec.ofNat 64 0 := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
      omega_arith
    rw [hs, show decide (x = 0) = false from decide_eq_false e]
    rfl

/-- `zeroMask`: `r5 :=` the mask of `r3 = 0`. -/
theorem zeroMask_ok (s : State) :
    WP isa (.block zeroMask) s fun t => (t.gpr .r5 = mask (decide (s.gpr .r3 = 0)) ∧ t.mem = s.mem) ∧
      Keep [.r0, .r5] s t := by
  refine WP.keep _ ?_ (by decide)
  unfold zeroMask
  prun [z64_mask]

/-- Word `j` of `c − 1`, as the scan reads it: `c`'s, bit 0 of the first
flipped. -/
def cw (m : Mem) (B : Addr) (w j : Nat) : BitVec 64 :=
  VG.Proof.Bignum.word m B (slot w 0 + 8 * j) ^^^ BitVec.ofNat 64 (if j = 0 then 1 else 0)

theorem xor_one_odd {x : BitVec 64} (h : x.toNat % 2 = 1) : (x ^^^ BitVec.ofNat 64 1).toNat = x.toNat / 2 * 2 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [BitVec.toNat_xor, Nat.testBit_xor, show (BitVec.ofNat 64 1 : BitVec 64).toNat = 1 from rfl]
  rcases i with _ | i
  · rw [Nat.testBit_zero, Nat.testBit_zero, Nat.testBit_zero, h, Nat.mul_mod_left]; rfl
  · rw [Nat.testBit_lt_two_pow (show 1 < 2 ^ (i + 1) from Nat.one_lt_two_pow (by omega_arith)), Bool.xor_false,
      show x.toNat / 2 * 2 = x.toNat / 2 ^ 1 * 2 ^ 1 from rfl, Nat.testBit_mul_two_pow, Nat.testBit_div_two_pow]
    simp

theorem cw_toNat {m : Mem} {B : Addr} {w c : Nat} (hn : wv m B (slot w 0) w = c) (hodd : c % 2 = 1) {j : Nat}
    (hj : j < w) : (cw m B w j).toNat = (c - 1) / 2 ^ (64 * j) % 2 ^ 64 := by
  unfold cw
  split
  · rename_i hj0; subst hj0
    rw [Nat.mul_zero, Nat.add_zero]
    have h0 := word_of_wv m B (slot w 0) w (q := 0) hj
    rw [Nat.mul_zero, Nat.add_zero, hn, Nat.pow_zero, Nat.div_one] at h0
    rw [xor_one_odd (by rw [h0]; omega_arith), h0, Nat.pow_zero, Nat.div_one]
    omega_arith
  · rw [BitVec.xor_zero, word_of_wv m B (slot w 0) w hj, hn,
      VG.Proof.RsaKeyGen.odd_sub_one_div hodd (by omega_arith)]

theorem lw_val (v x : BitVec 64) : v ||| x &&& mask (decide (v = 0)) = if v = 0 then x else v := by
  by_cases h : v = 0
  · subst h
    rw [show decide ((0 : BitVec 64) = 0) = true from rfl, ite_eq_left rfl]
    show 0#64 ||| x &&& BitVec.allOnes 64 = x
    rw [BitVec.and_allOnes, BitVec.zero_or]
  · rw [decide_eq_false h, ite_eq_right h]
    show v ||| x &&& 0#64 = v
    rw [BitVec.and_zero, BitVec.or_zero]

/-- The registers `lowWord` writes. -/
def lowRegs : List Reg := [.r0, .r3, .r4, .r5, .r6, .r7, .r14, .r17]

/-- After `i` words of the scan. -/
structure LInv (s₀ : State) (B : Addr) (w i0 : Nat) (x : BitVec 64) (i : Nat) (t : State) : Prop where
  keep : Keep lowRegs s₀ t
  mem : t.mem = s₀.mem
  r14 : t.gpr .r14 = off B (slot w 0 + 8 * i)
  r4 : t.gpr .r4 = BitVec.ofNat 64 (if i = 0 then 1 else 0)
  r6 : t.gpr .r6 = if i ≤ i0 then 0 else x

/-- `lowWord`: the lowest nonzero word of `c − 1` into `r6`. -/
theorem lowWord_ok {s : State} {B : Addr} {Z w c : Nat} (h : Env s B Z w) (hn : wv s.mem B (slot w 0) w = c)
    (hodd : c % 2 = 1) (hc1 : 1 < c) :
    WP isa lowWord s fun t =>
      ((t.gpr .r6).toNat = (c - 1) / 2 ^ (64 * (mrA c / 64)) % 2 ^ 64 ∧ t.mem = s.mem) ∧ Keep lowRegs s t := by
  have hnw := h.hs.nowrap
  have hw := h.hw
  have hw' := h.hw'
  have s0 := Env.arr h (show 0 < 28 by decide)
  obtain ⟨hN, hm2⟩ := VG.Proof.RsaKeyGen.splitTwos_spec (c - 1) (by omega_arith)
  change c - 1 = (Spec.Rsa.splitTwos (c - 1)).2 * 2 ^ mrA c at hN
  obtain ⟨hz, -, -⟩ := VG.Proof.RsaKeyGen.lowWord_bits hN hm2
  have hcw : c < 2 ^ (64 * w) := by rw [← hn]; exact wv_lt _ _ _ _
  have ha : mrA c < 64 * w := by
    rcases Nat.lt_or_ge (mrA c) (64 * w) with h | h
    · exact h
    exfalso
    have h1 : 2 ^ (64 * w) ≤ 2 ^ mrA c := Nat.pow_le_pow_right (by decide) h
    have h2 : 2 ^ mrA c ≤ (Spec.Rsa.splitTwos (c - 1)).2 * 2 ^ mrA c := Nat.le_mul_of_pos_left _ (by omega_arith)
    omega_arith
  generalize hi0 : mrA c / 64 = i0 at hz ⊢
  have hi0w : i0 < w := by omega_arith
  have hx : (cw s.mem B w i0).toNat = (c - 1) / 2 ^ (64 * i0) % 2 ^ 64 := cw_toNat hn hodd hi0w
  have hne : cw s.mem B w i0 ≠ 0 := fun e => by
    obtain ⟨-, hx1, -⟩ := VG.Proof.RsaKeyGen.lowWord_bits hN hm2
    rw [hi0, ← hx, e] at hx1; simp at hx1
  unfold lowWord
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (h.base (rd := .r14) (by decide) (by decide) 0) fun s₁ ⟨⟨a14, m1⟩, k1⟩ => ?_
  have hpre : WP isa (.block [.lsr .d .r17 .r11 1, .li .r6 0, .li .r4 1]) s₁ fun t =>
      (t.gpr .r17 = BitVec.ofNat 64 w ∧ t.gpr .r6 = 0 ∧ t.gpr .r4 = BitVec.ofNat 64 1 ∧ t.mem = s₁.mem) ∧
        Keep [.r17, .r6, .r4] s₁ t := by
    refine WP.keep _ ?_ (by decide)
    prun [(k1.gpr .r11 (by decide)).trans h.h11, shr1_ofNat w hw']
    rfl
  refine WP.mono hpre fun s₂ ⟨⟨a17, a6, a4, m2⟩, k2⟩ => ?_
  refine WP.mono (wp_countdown (N := w) (by omega_arith) (by omega_arith) (LInv s B w i0 (cw s.mem B w i0))
    (fun i hi t hI _ => ?_) ⟨(k1.trans k2).mono (by decide), by rw [m2, m1],
      by rw [k2.gpr .r14 (by decide), a14]; rfl, by rw [a4]; rfl, by rw [a6]; simp⟩ a17)
    fun t hI => ⟨⟨?_, hI.mem⟩, hI.keep⟩
  · have hs := h.hs.congr hI.keep.wr
    have hwd : VG.Proof.Bignum.word t.mem B (slot w 0 + 8 * i) ^^^ BitVec.ofNat 64 (if i = 0 then 1 else 0) =
        cw s.mem B w i := by rw [hI.mem]; rfl
    have hr : t.gpr .r6 ||| cw s.mem B w i &&& mask (decide (t.gpr .r6 = 0)) =
        if i + 1 ≤ i0 then 0 else cw s.mem B w i0 := by
      rw [lw_val, hI.r6]
      rcases Nat.lt_trichotomy i i0 with hlt | rfl | hgt
      · have hz0 : cw s.mem B w i = 0 :=
          BitVec.eq_of_toNat_eq (by rw [cw_toNat hn hodd (by omega_arith), hz i hlt]; rfl)
        rw [ite_eq_left (show i ≤ i0 by omega_arith), ite_eq_left rfl, hz0, ite_eq_left (show i + 1 ≤ i0 by omega_arith)]
      · rw [ite_eq_left (Nat.le_refl _), ite_eq_left rfl, ite_eq_right (show ¬ i + 1 ≤ i by omega_arith)]
      · rw [ite_eq_right (show ¬ i ≤ i0 by omega_arith), ite_eq_right hne, ite_eq_right (show ¬ i + 1 ≤ i0 by omega_arith)]
    refine WP.mono (WP.keep lowRegs (Q := fun t' => t'.gpr .r14 = off B (slot w 0 + 8 * (i + 1)) ∧
        t'.gpr .r4 = BitVec.ofNat 64 0 ∧ t'.gpr .r6 = (if i + 1 ≤ i0 then 0 else cw s.mem B w i0) ∧
        t'.gpr .r17 = t.gpr .r17 - BitVec.ofNat 64 1 ∧ t'.mem = t.mem) ?_ (by decide))
      fun t' ⟨⟨b14, b4, b6, b17, bm⟩, k'⟩ => ⟨⟨(hI.keep.trans k').mono (by decide), bm.trans hI.mem, b14,
        by rw [b4]; simp, b6⟩, b17⟩
    unfold zeroMask
    prun [hI.r14, hI.r4, hs.ld (show slot w 0 + 8 * i + 8 ≤ Z by omega_arith), hwd, z64_mask, hr, BitVec.add_zero,
      show slot w 0 + 8 * i + 8 = slot w 0 + 8 * (i + 1) by omega_arith]
  · rw [hI.r6, ite_eq_right (show ¬ w ≤ i0 by omega_arith), hx]

/-! ## Halving -/

/-- A word of the halved number, or the word itself. -/
def hsel (mb : Bool) (a b : BitVec 64) : BitVec 64 := if mb then (a >>> 1) ||| (b <<< 63) else a

theorem hsel_eq (mb : Bool) (a b : BitVec 64) :
    ((a >>> 1 ||| b <<< 63) ^^^ a) &&& mask mb ^^^ a = hsel mb a b := by
  cases mb
  · show _ &&& 0#64 ^^^ a = a
    rw [BitVec.and_zero, BitVec.zero_xor]
  · show _ &&& BitVec.allOnes 64 ^^^ a = _
    rw [BitVec.and_allOnes, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]; rfl

theorem top_sel (a : BitVec 64) (mb : Bool) :
    (a >>> 1 ^^^ a) &&& mask mb ^^^ a = if mb then a >>> 1 else a := by
  cases mb
  · show _ &&& 0#64 ^^^ a = a
    rw [BitVec.and_zero, BitVec.zero_xor]
  · show _ &&& BitVec.allOnes 64 ^^^ a = _
    rw [BitVec.and_allOnes, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]; rfl

/-- The registers `halfPass` writes. -/
def halfRegs : List Reg := [.r3, .r4, .r5, .r6, .r15, .r16, .r17]

/-- After `i` words of a halving pass's loop from `s₀`. -/
structure HInv (s₀ : State) (B : Addr) (Z w eS eD : Nat) (mb : Bool) (i : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep halfRegs s₀ t
  r15 : t.gpr .r15 = off B (eS + 8 * (i + 1))
  r16 : t.gpr .r16 = off B (eD + 8 * i)
  r5 : t.gpr .r5 = word s₀.mem B (eS + 8 * i)
  done : ∀ k, k < i → word t.mem B (eD + 8 * k) =
    hsel mb (word s₀.mem B (eS + 8 * k)) (word s₀.mem B (eS + 8 * (k + 1)))
  src : ∀ k, i + 1 ≤ k → k < w → word t.mem B (eS + 8 * k) = word s₀.mem B (eS + 8 * k)
  out : Outside B eD (8 * i) s₀.mem t.mem

/-- A word of a halving pass. -/
theorem halfStep_ok {s₀ : State} {B : Addr} {Z w eS eD : Nat} {mb : Bool} (h9 : s₀.gpr .r9 = mask mb)
    (hS : eS + 8 * w ≤ Z) (hD : eD + 8 * w ≤ Z) (hsep : eD = eS ∨ eD + 8 * w ≤ eS ∨ eS + 8 * w ≤ eD)
    {i : Nat} (hi : i + 1 < w) {t : State} (hI : HInv s₀ B Z w eS eD mb i t) :
    WP isa (.block (([.load .d .r3 .r15 0, .lsl .r4 .r3 63, .lsr .d .r6 .r5 1, .logic .or .r6 .r6 .r4,
        .logic .xor .r6 .r6 .r5, .logic .and .r6 .r6 .r9, .logic .xor .r6 .r6 .r5, .store .d .r6 .r16 0,
        .addi .r15 .r15 8, .addi .r16 .r16 8, .addi .r5 .r3 0] : List Instr) ++ ([.subi .r17 .r17 1] : List Instr))) t
      fun t' => HInv s₀ B Z w eS eD mb (i + 1) t' ∧ t'.gpr .r17 = t.gpr .r17 - BitVec.ofNat 64 1 := by
  have hn := hI.scr.nowrap
  have t9 : t.gpr .r9 = mask mb := (hI.keep.gpr .r9 (by decide)).trans h9
  have hSj : word t.mem B (eS + 8 * (i + 1)) = word s₀.mem B (eS + 8 * (i + 1)) :=
    hI.src (i + 1) (Nat.le_refl _) hi
  have hst : WP isa (.block ([.load .d .r3 .r15 0, .lsl .r4 .r3 63, .lsr .d .r6 .r5 1, .logic .or .r6 .r6 .r4,
        .logic .xor .r6 .r6 .r5, .logic .and .r6 .r6 .r9, .logic .xor .r6 .r6 .r5, .store .d .r6 .r16 0,
        .addi .r15 .r15 8, .addi .r16 .r16 8, .addi .r5 .r3 0] ++ ([.subi .r17 .r17 1] : List Instr))) t
      fun t' => (t'.mem = t.mem.writeW (off B (eD + 8 * i))
        (hsel mb (word s₀.mem B (eS + 8 * i)) (word s₀.mem B (eS + 8 * (i + 1)))) ∧
        t'.gpr .r5 = word s₀.mem B (eS + 8 * (i + 1)) ∧ t'.gpr .r15 = off B (eS + 8 * (i + 1 + 1)) ∧
        t'.gpr .r16 = off B (eD + 8 * (i + 1)) ∧ t'.gpr .r17 = t.gpr .r17 - BitVec.ofNat 64 1) ∧
        Keep halfRegs t t' := by
    refine WP.keep _ ?_ (by decide)
    prun [hI.r15, hI.r16, hI.r5, t9, hI.scr.ld (show eS + 8 * (i + 1) + 8 ≤ Z by omega_arith),
      hI.scr.st (show eD + 8 * i + 8 ≤ Z by omega_arith), hSj, hsel_eq, BitVec.add_zero]
    rw [show eS + 8 * (i + 1) + 8 = eS + 8 * (i + 1 + 1) by omega_arith, show eD + 8 * i + 8 = eD + 8 * (i + 1) by omega_arith]
    exact ⟨rfl, rfl⟩
  refine WP.mono hst fun t' ⟨⟨hm, h5, h15, h16, h17⟩, k'⟩ => ⟨?_, h17⟩
  have hw8 : Outside B (eD + 8 * i) 8 t.mem t'.mem := by
    rw [hm]; exact writeW_outside _ _ _ (by omega_arith)
  refine ⟨hI.scr.congr k'.wr, (hI.keep.trans k').mono (by decide), h15, h16, h5, fun k hk => ?_,
    fun k hk hkw => ?_, ?_⟩
  · rw [hm]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · rw [Outside.word (writeW_outside t.mem B _ (by omega_arith)) (by omega_arith) (by omega_arith)]; exact hI.done k hk
    · rw [word_writeW_self]
  · rw [hm, Outside.word (writeW_outside t.mem B _ (by omega_arith)) (by omega_arith) (by omega_arith)]
    exact hI.src k (by omega_arith) hkw
  · exact Outside.trans (Outside.mono hI.out (Nat.le_refl _) (by omega_arith)) (Outside.mono hw8 (by omega_arith) (by omega_arith))

/-- A halving pass: `[eD] := mb ? [eS] / 2 : [eS]` over `w` words, in place
or not. -/
theorem halfPass_ok {s : State} {B : Addr} {Z w eS eD : Nat} {mb : Bool} (hs : Scr s B Z)
    (h15 : s.gpr .r15 = off B eS) (h16 : s.gpr .r16 = off B eD) (h9 : s.gpr .r9 = mask mb)
    (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w)) (hw : 2 ≤ w) (hw' : w ≤ 128) (hS : eS + 8 * w ≤ Z)
    (hD : eD + 8 * w ≤ Z) (hsep : eD = eS ∨ eD + 8 * w ≤ eS ∨ eS + 8 * w ≤ eD) :
    WP isa halfPass s fun t => wv t.mem B eD w = (if mb then wv s.mem B eS w / 2 else wv s.mem B eS w) ∧
      Outside B eD (8 * w) s.mem t.mem ∧ Keep halfRegs s t := by
  have hn := hs.nowrap
  unfold halfPass
  have hpre : WP isa (.block [.load .d .r5 .r15 0, .addi .r15 .r15 8, .lsr .d .r17 .r11 1, .subi .r17 .r17 1]) s
      fun t => (t.gpr .r5 = word s.mem B eS ∧ t.gpr .r15 = off B (eS + 8 * (0 + 1)) ∧
        t.gpr .r17 = BitVec.ofNat 64 (w - 1) ∧ t.mem = s.mem) ∧ Keep [.r5, .r15, .r17] s t := by
    refine WP.keep _ ?_ (by decide)
    prun [h15, h11, hs.ld (show eS + 8 ≤ Z by omega_arith), shr1_ofNat w hw', BitVec.add_zero]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega_arith
  refine WP.seq (WP.mono hpre fun s₀ ⟨⟨h5₀, h15₀, h17₀, hm₀⟩, k₀⟩ => ?_)
  have hs₀ := hs.congr k₀.wr
  have h9₀ : s₀.gpr .r9 = mask mb := (k₀.gpr .r9 (by decide)).trans h9
  have h16₀ : s₀.gpr .r16 = off B eD := (k₀.gpr .r16 (by decide)).trans h16
  refine WP.seq (WP.mono (wp_countdown (N := w - 1) (by omega_arith) (by omega_arith) (HInv s₀ B Z w eS eD mb)
    (fun i hi t hI _ => halfStep_ok h9₀ hS hD hsep (by omega_arith) hI)
    ⟨hs₀, Keep.refl _ _, h15₀, by rw [h16₀]; rfl, by rw [h5₀, hm₀, Nat.mul_zero, Nat.add_zero],
      fun k hk => absurd hk (by omega_arith), fun k _ _ => rfl, Outside.refl _ _ _ _⟩ h17₀) fun s₁ hI => ?_)
  have t9 : s₁.gpr .r9 = mask mb := (hI.keep.gpr .r9 (by decide)).trans h9₀
  have htopb : WP isa (.block [.lsr .d .r6 .r5 1, .logic .xor .r6 .r6 .r5, .logic .and .r6 .r6 .r9,
      .logic .xor .r6 .r6 .r5, .store .d .r6 .r16 0]) s₁ fun t =>
      t.mem = s₁.mem.writeW (off B (eD + 8 * (w - 1)))
        (if mb then word s₀.mem B (eS + 8 * (w - 1)) >>> 1 else word s₀.mem B (eS + 8 * (w - 1))) ∧
        Keep halfRegs s₁ t := by
    refine WP.keep _ ?_ (by decide)
    prun [hI.r16, hI.scr.st (show eD + 8 * (w - 1) + 8 ≤ Z by omega_arith), t9, hI.r5, top_sel, BitVec.add_zero]
  refine WP.mono htopb fun t ⟨hm, k⟩ => ?_
  have hw8 : Outside B (eD + 8 * (w - 1)) 8 s₁.mem t.mem := by rw [hm]; exact writeW_outside _ _ _ (by omega_arith)
  have hdone : ∀ i, i + 1 < w → word t.mem B (eD + 8 * i) =
      hsel mb (word s.mem B (eS + 8 * i)) (word s.mem B (eS + 8 * (i + 1))) := fun i hi => by
    rw [Outside.word hw8 (by omega_arith) (by omega_arith), hI.done i (by omega_arith), hm₀]
  have htop : word t.mem B (eD + 8 * (w - 1)) = if mb then word s.mem B (eS + 8 * (w - 1)) >>> 1
      else word s.mem B (eS + 8 * (w - 1)) := by rw [hm, word_writeW_self, hm₀]
  refine ⟨?_, ?_, ((k₀.trans hI.keep).trans k).mono (by decide)⟩
  · cases mb
    · rw [ite_eq_right (by decide)] at htop ⊢
      refine VG.Proof.Bignum.wv_congr2 fun i hi => ?_
      rcases Nat.lt_or_ge (i + 1) w with h | h
      · exact hdone i h
      · rw [show i = w - 1 by omega_arith]; exact htop
    · rw [ite_eq_left rfl] at htop ⊢
      exact VG.Proof.RsaKeyGen.wv_half (by omega_arith) (fun i hi => hdone i hi) htop
  · rw [← hm₀]
    exact Outside.trans (Outside.mono hI.out (Nat.le_refl _) (by omega_arith)) (Outside.mono hw8 (by omega_arith) (by omega_arith))

/-! ## The exponent -/

theorem shl2_ofNat (w : Nat) : BitVec.ofNat 64 (2 * w) <<< 2 = BitVec.ofNat 64 (8 * w) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega_arith

/-- `markerAddr`: the word after array 27's `w` into `r14`. -/
theorem markerAddr_ok {s : State} {B : Addr} {Z w : Nat} (h : Env s B Z w) :
    WP isa (.block markerAddr) s fun t => (t.gpr .r14 = off B (slot w aE + 8 * w) ∧ t.mem = s.mem) ∧
      Keep [.r7, .r14] s t := by
  unfold markerAddr
  rw [WP.block_append_iff]
  refine WP.mono (h.base (rd := .r14) (by decide) (by decide) aE) fun s₁ ⟨⟨a14, m1⟩, k1⟩ => ?_
  have hb : WP isa (.block [.lsl .r7 .r11 2, .add .r14 .r14 .r7]) s₁ fun t =>
      (t.gpr .r14 = off B (slot w aE + 8 * w) ∧ t.mem = s₁.mem) ∧ Keep [.r7, .r14] s₁ t := by
    refine WP.keep _ ?_ (by decide)
    prun [(k1.gpr .r11 (by decide)).trans h.h11, shl2_ofNat w, a14]
  exact WP.mono hb fun t ⟨⟨a, m⟩, k⟩ => ⟨⟨a, m.trans m1⟩, (k1.trans k).mono (by decide)⟩

theorem neg_and_low {x : BitVec 64} {k : Nat} (hk : k < 64) (h1 : x.toNat.testBit k = true)
    (h0 : ∀ j < k, x.toNat.testBit j = false) : x &&& (BitVec.ofNat 64 0 - x) = BitVec.twoPow 64 k := by
  rw [show (BitVec.ofNat 64 0 : BitVec 64) = 0#64 from rfl, BitVec.zero_sub]
  exact VG.Proof.RsaKeyGen.and_neg_eq_twoPow hk h1 h0

/-- `lowBit`: `l = x & −x` (`x` in `r6`) after array 27's `w` words. -/
theorem lowBit_ok {s : State} {B : Addr} {Z w : Nat} (h : Env s B Z w) {x : BitVec 64} {k : Nat} (hk : k < 64)
    (h6 : s.gpr .r6 = x) (h1 : x.toNat.testBit k = true) (h0 : ∀ j < k, x.toNat.testBit j = false) :
    WP isa (.block lowBit) s fun t =>
      t.mem = s.mem.writeW (off B (slot w aE + 8 * w)) (BitVec.twoPow 64 k) ∧ Keep [.r6, .r7, .r14] s t := by
  have hE := h.arr (show aE < 28 by decide)
  unfold lowBit
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  have hb : WP isa (.block [.li .r7 0, .sub .r7 .r7 .r6, .logic .and .r6 .r6 .r7]) s fun t =>
      (t.gpr .r6 = BitVec.twoPow 64 k ∧ t.mem = s.mem) ∧ Keep [.r6, .r7] s t := by
    refine WP.keep _ ?_ (by decide)
    prun [h6, neg_and_low hk h1 h0]
  refine WP.mono hb fun s₁ ⟨⟨a6, m1⟩, k1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (markerAddr_ok (h.keep k1 (by decide))) fun s₂ ⟨⟨a14, m2⟩, k2⟩ => ?_
  have hs₂ := h.hs.congr (k1.trans k2).wr
  have hst : WP isa (.block [.store .d .r6 .r14 0]) s₂ fun t =>
      t.mem = s₂.mem.writeW (off B (slot w aE + 8 * w)) (BitVec.twoPow 64 k) ∧ Keep [] s₂ t := by
    refine WP.keep _ ?_ (by decide)
    prun [a14, hs₂.st (show slot w aE + 8 * w + 8 ≤ Z by omega_arith), (k2.gpr .r6 (by decide)).trans a6]
  exact WP.mono hst fun t ⟨m, k⟩ => ⟨by rw [m, m2, m1], ((k1.trans k2).trans k).mono (by decide)⟩

theorem not_mask (b : Bool) : (BitVec.ofNat 64 0 - BitVec.ofNat 64 1) ^^^ mask b = mask (!b) := by
  cases b <;> decide

/-- The mask of `σ > j` into `r9`, from the word after array 27 at `r14`. -/
def condMid (j : Nat) : List Instr :=
  [.load .d .r3 .r14 0] ++ repeat16 (sigK j) ++ [.logic .and .r3 .r3 .r4] ++ zeroMask ++
    ([.li .r9 0, .subi .r9 .r9 1, .logic .xor .r9 .r9 .r5] : List Instr)

theorem condMid_ok {s : State} {B : Addr} {Z w c : Nat} (hs : Scr s B Z) (hZ : slot w aE + 8 * w + 8 ≤ Z)
    (h14 : s.gpr .r14 = off B (slot w aE + 8 * w))
    (hL : s.mem.readW (off B (slot w aE + 8 * w)) 64 = BitVec.twoPow 64 (mrA c % 64)) {j : Nat}
    (hj : j = 1 ∨ j = 2 ∨ j = 3) :
    WP isa (.block (condMid j)) s fun t => (t.gpr .r9 = mask (decide (j < mrSig c)) ∧ t.mem = s.mem) ∧
      Keep [.r0, .r3, .r4, .r5, .r9] s t := by
  refine WP.keep _ ?_ (by rfl)
  unfold condMid zeroMask repeat16
  prun [h14, hs.ld hZ, hL, exec_lis, exec_ori, exec_oris, repeat16_val j hj, z64_mask, not_mask, BitVec.add_zero]
  rw [← sig_word hj, decide_not]

theorem halfCond_eq (j : Nat) : halfCond j =
    .seq (.block (markerAddr ++ (condMid j ++ (PublicChecked.base .r15 aE ++ PublicChecked.base .r16 aE)))) halfPass := by
  simp only [halfCond, condMid, List.append_assoc]

/-- The registers `expSetup` writes. -/
def prepRegs : List Reg := [.r0, .r3, .r4, .r5, .r6, .r7, .r9, .r14, .r15, .r16, .r17]

/-- A conditional halving of array 27, in place, under the mask of `σ > j`. -/
theorem halfCond_ok {s : State} {B : Addr} {Z w c : Nat} (h : Env s B Z w)
    (hL : s.mem.readW (off B (slot w aE + 8 * w)) 64 = BitVec.twoPow 64 (mrA c % 64)) {j : Nat}
    (hj : j = 1 ∨ j = 2 ∨ j = 3) :
    WP isa (halfCond j) s fun t =>
      wv t.mem B (slot w aE) w = (if j < mrSig c then wv s.mem B (slot w aE) w / 2 else wv s.mem B (slot w aE) w) ∧
      Outside B (slot w aE) (8 * w) s.mem t.mem ∧ Keep prepRegs s t := by
  have hE := h.arr (show aE < 28 by decide)
  have hw := h.hw
  have hw' := h.hw'
  rw [halfCond_eq]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (markerAddr_ok h) fun s₁ ⟨⟨a14, m1⟩, k1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (condMid_ok (c := c) (h.hs.congr k1.wr) (by omega_arith) a14 (by rw [m1]; exact hL) hj)
    fun s₂ ⟨⟨a9, m2⟩, k2⟩ => ?_
  have e2 := (h.keep k1 (by decide)).keep k2 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (e2.base (rd := .r15) (by decide) (by decide) aE) fun s₃ ⟨⟨a15, m3⟩, k3⟩ => ?_
  refine WP.mono ((e2.keep k3 (by decide)).base (rd := .r16) (by decide) (by decide) aE)
    fun s₄ ⟨⟨a16, m4⟩, k4⟩ => ?_
  have k14 := ((k1.trans k2).trans k3).trans k4
  refine WP.mono (halfPass_ok (h.hs.congr k14.wr) ((k4.gpr .r15 (by decide)).trans a15) a16
    (((k3.trans k4).gpr .r9 (by decide)).trans a9) ((k14.gpr .r11 (by decide)).trans h.h11) (by omega_arith) hw'
    (by omega_arith) (by omega_arith) (Or.inl rfl)) fun t ⟨hv, ho, k⟩ => ?_
  have hm : s₄.mem = s.mem := by rw [m4, m3, m2, m1]
  rw [hm] at hv ho
  refine ⟨?_, ho, (k14.trans k).mono (by decide)⟩
  rw [hv]
  simp only [decide_eq_true_eq]

/-- `halfCond_ok` within `Env`, keeping the word after array 27. -/
theorem halfCond_step {s : State} {B : Addr} {Z w c e : Nat} (h : Env s B Z w)
    (hL : s.mem.readW (off B (slot w aE + 8 * w)) 64 = BitVec.twoPow 64 (mrA c % 64))
    (he : wv s.mem B (slot w aE) w = e) {j : Nat} (hj : j = 1 ∨ j = 2 ∨ j = 3) :
    WP isa (halfCond j) s fun t => (Env t B Z w ∧
      t.mem.readW (off B (slot w aE + 8 * w)) 64 = BitVec.twoPow 64 (mrA c % 64) ∧
      wv t.mem B (slot w aE) w = (if j < mrSig c then e / 2 else e) ∧
      Outside B (slot w aE) (8 * (w + 2)) s.mem t.mem) ∧ Keep prepRegs s t := by
  have hE := h.arr (show aE < 28 by decide)
  have hn := h.hs.nowrap
  refine WP.mono (halfCond_ok h hL hj) fun t ⟨hv, ho, k⟩ => ⟨⟨h.keep k (by decide), ?_, by rw [hv, he], ?_⟩, k⟩
  · rw [← hL]; exact Outside.word ho (Or.inr (by omega_arith)) (by omega_arith)
  · exact Outside.mono ho (Nat.le_refl _) (by omega_arith)

/-- `expSetup`: `E = (c − 1) / 2^σ` in array 27, and after its `w` words the
lowest set bit of `c − 1`'s lowest nonzero word. -/
theorem expSetup_ok {s : State} {B : Addr} {Z w c : Nat} (h : Env s B Z w) (hn : wv s.mem B (slot w 0) w = c)
    (hodd : c % 2 = 1) (hc1 : 1 < c) :
    WP isa expSetup s fun t => (arr t.mem B w aE = mrE c ∧
      t.mem.readW (off B (slot w aE + 8 * w)) 64 = BitVec.twoPow 64 (mrA c % 64) ∧
      Outside B (slot w aE) (8 * (w + 2)) s.mem t.mem) ∧ Keep prepRegs s t := by
  have hE := h.arr (show aE < 28 by decide)
  have h0E : slot w 0 + 8 * (w + 2) ≤ slot w aE := slot_lt (by decide)
  have hnw := h.hs.nowrap
  have hw := h.hw
  have hw' := h.hw'
  obtain ⟨hN, hm2⟩ := VG.Proof.RsaKeyGen.splitTwos_spec (c - 1) (by omega_arith)
  change c - 1 = (Spec.Rsa.splitTwos (c - 1)).2 * 2 ^ mrA c at hN
  obtain ⟨-, hx1, hx0⟩ := VG.Proof.RsaKeyGen.lowWord_bits hN hm2
  unfold expSetup
  refine WP.seq (WP.mono (lowWord_ok h hn hodd hc1) fun s₁ ⟨⟨h6, m1⟩, k1⟩ => ?_)
  have e1 := h.keep k1 (by decide)
  refine WP.seq ?_
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (lowBit_ok e1 (k := mrA c % 64) (Nat.mod_lt _ (by decide)) rfl (by rw [h6]; exact hx1)
    (fun j hj => by rw [h6]; exact hx0 j hj)) fun s₂ ⟨m2, k2⟩ => ?_
  have e2 := e1.keep k2 (by decide)
  rw [WP.block_append_iff]
  have h9 : WP isa (.block [.li .r9 0, .subi .r9 .r9 1]) s₂ fun t =>
      (t.gpr .r9 = mask true ∧ t.mem = s₂.mem) ∧ Keep [.r9] s₂ t := by
    refine WP.keep _ ?_ (by decide)
    prun
    rfl
  refine WP.mono h9 fun s₃ ⟨⟨a9, m3⟩, k3⟩ => ?_
  have e3 := e2.keep k3 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (e3.base (rd := .r15) (by decide) (by decide) 0) fun s₄ ⟨⟨a15, m4⟩, k4⟩ => ?_
  have e4 := e3.keep k4 (by decide)
  refine WP.mono (e4.base (rd := .r16) (by decide) (by decide) aE) fun s₅ ⟨⟨a16, m5⟩, k5⟩ => ?_
  have e5 := e4.keep k5 (by decide)
  have k15 := (((k1.trans k2).trans k3).trans k4).trans k5
  have hm5 : s₅.mem = s.mem.writeW (off B (slot w aE + 8 * w)) (BitVec.twoPow 64 (mrA c % 64)) := by
    rw [m5, m4, m3, m2, m1]
  have hwr : Outside B (slot w aE + 8 * w) 8 s.mem s₅.mem := by rw [hm5]; exact writeW_outside _ _ _ (by omega_arith)
  have hL5 : s₅.mem.readW (off B (slot w aE + 8 * w)) 64 = BitVec.twoPow 64 (mrA c % 64) := by
    rw [hm5]; exact word_writeW_self _ _ _ _
  have hc5 : wv s₅.mem B (slot w 0) w = c := by
    rw [VG.Proof.Bignum.Outside.wv hwr (Or.inl (by omega_arith)) (by omega_arith)]; exact hn
  refine WP.seq (WP.mono (halfPass_ok e5.hs (mb := true) ((k5.gpr .r15 (by decide)).trans a15) a16
    (((k4.trans k5).gpr .r9 (by decide)).trans a9) e5.h11 (by omega_arith) hw' (by omega_arith) (by omega_arith)
    (Or.inr (Or.inr (by omega_arith)))) fun s₆ ⟨hv6, ho6, k6⟩ => ?_)
  rw [hc5, ite_eq_left rfl] at hv6
  have e6 := e5.keep k6 (by decide)
  have hL6 : s₆.mem.readW (off B (slot w aE + 8 * w)) 64 = BitVec.twoPow 64 (mrA c % 64) := by
    rw [← hL5]; exact Outside.word ho6 (Or.inr (by omega_arith)) (by omega_arith)
  refine WP.seq (WP.mono (halfCond_step e6 hL6 hv6 (j := 1) (by decide)) fun s₇ ⟨⟨e7, hL7, hv7, ho7⟩, k7⟩ => ?_)
  refine WP.seq (WP.mono (halfCond_step e7 hL7 hv7 (j := 2) (by decide)) fun s₈ ⟨⟨e8, hL8, hv8, ho8⟩, k8⟩ => ?_)
  refine WP.mono (halfCond_step e8 hL8 hv8 (j := 3) (by decide)) fun t ⟨⟨_, hLt, hvt, hot⟩, kt⟩ => ?_
  refine ⟨⟨?_, hLt, ?_⟩, ((((k15.trans k6).trans k7).trans k8).trans kt).mono (by decide)⟩
  · rw [arr, Pre.val32_eq_wv, hvt, ← VG.Proof.RsaKeyGen.mrE_halves hodd]
  · refine Outside.trans (Outside.mono hwr (by omega_arith) (by omega_arith)) (Outside.trans ?_ (Outside.trans ho7
      (Outside.trans ho8 hot)))
    exact Outside.mono ho6 (Nat.le_refl _) (by omega_arith)

end VG.Proof.MillerRabin.PPC64LE
