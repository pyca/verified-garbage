module

public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrSq
import VerifiedGarbage.Proof.RsaKeyGen.Halve
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrBit
import VerifiedGarbage.Proof.RsaKeyGen.MrMont
import VerifiedGarbage.Proof.Rsa.AArch64.KeyLoops
import VerifiedGarbage.Proof.Rsa.Ranges
import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks
import VerifiedGarbage.Proof.Bignum.AArch64.CrtArith
import VerifiedGarbage.Proof.Bignum.AArch64.Row
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.AArch64.Bytes
import VerifiedGarbage.Proof.Framework.AArch64.Call

/-!
# A candidate on AArch64: Miller–Rabin's exponent

`halfPass_ok`: `[x17] := x15 ? [x16] / 2 : [x16]`, in place or not;
`lowWord_ok`: the lowest nonzero word of `c − 1`; `expSetup_ok`: its lowest
set bit after the words of `aE`, then `E = (c − 1) / 2^σ` in `aE` (`ECtx`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Rsa (slot_lt)
open VG.Impl.Bignum.Public (aN aAcc aTmp aXm aY sCnt)

/-- A word of the halved number, or the word itself. -/
def hsel (mb : Bool) (a b : BitVec 64) : BitVec 64 := if mb then (a >>> 1) ||| (b <<< 63) else a

theorem hsel_eq (mb : Bool) (a b : BitVec 64) :
    ((a >>> 1 ||| b <<< 63) ^^^ a) &&& mask mb ^^^ a = hsel mb a b := by
  cases mb
  · simp [hsel, mask_false]
  · simp only [hsel, mask_true, BitVec.and_allOnes, ↓reduceIte, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

theorem top_sel (a : BitVec 64) (mb : Bool) :
    (a >>> 1 ^^^ a) &&& mask mb ^^^ a = if mb then a >>> 1 else a := by
  cases mb
  · simp [mask_false]
  · simp only [mask_true, BitVec.and_allOnes, ↓reduceIte, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

/-- After `i` words of a halving pass's loop from `s₀`. -/
structure HInv (s₀ : State) (B : Addr) (Z w eS eD : Nat) (mb : Bool) (i : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.x3, .x4, .x5, .x6, .x14, .x16, .x17] s₀ t
  x16 : t.gpr .x16 = off B (eS + 8 * (i + 1))
  x17 : t.gpr .x17 = off B (eD + 8 * i)
  x5 : t.gpr .x5 = word s₀.mem B (eS + 8 * i)
  done : ∀ k, k < i → word t.mem B (eD + 8 * k) =
    hsel mb (word s₀.mem B (eS + 8 * k)) (word s₀.mem B (eS + 8 * (k + 1)))
  src : ∀ k, i + 1 ≤ k → k < w → word t.mem B (eS + 8 * k) = word s₀.mem B (eS + 8 * k)
  out : Outside B eD (8 * i) s₀.mem t.mem

/-- A word of a halving pass. -/
theorem halfStep_ok {s₀ : State} {B : Addr} {Z w eS eD : Nat} {mb : Bool} (h15 : s₀.gpr .x15 = mask mb)
    (hS : eS + 8 * w ≤ Z) (hD : eD + 8 * w ≤ Z) (hsep : eD = eS ∨ eD + 8 * w ≤ eS ∨ eS + 8 * w ≤ eD)
    {i : Nat} (hi : i + 1 < w) {t : State} (hI : HInv s₀ B Z w eS eD mb i t) :
    WP isa (.block ([ld .x3 .x16, .lsl .x .x4 .x3 63, .lsr .x .x6 .x5 1, .logic .orr .x .x6 .x6 .x4,
        .logic .eor .x .x6 .x6 .x5, .logic .and .x .x6 .x6 .x15, .logic .eor .x .x6 .x6 .x5, st .x6 .x17, next .x16,
        next .x17, mov .x5 .x3] ++ ([.subImm .x .x14 .x14 1] : List Instr))) t
      fun t' => HInv s₀ B Z w eS eD mb (i + 1) t' ∧ t'.gpr .x14 = t.gpr .x14 - BitVec.ofNat 64 1 := by
  have hn := hI.scr.nowrap
  have t15 : t.gpr .x15 = mask mb := (hI.keep.gpr .x15 (by decide)).trans h15
  have hSj : word t.mem B (eS + 8 * (i + 1)) = word s₀.mem B (eS + 8 * (i + 1)) :=
    hI.src (i + 1) (Nat.le_refl _) hi
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x3, .x4, .x5, .x6, .x16, .x17] (Q := fun t₁ => t₁.mem = t.mem.writeW (off B (eD + 8 * i))
      (hsel mb (word s₀.mem B (eS + 8 * i)) (word s₀.mem B (eS + 8 * (i + 1)))) ∧
      t₁.gpr .x5 = word s₀.mem B (eS + 8 * (i + 1)) ∧ t₁.gpr .x16 = off B (eS + 8 * (i + 1 + 1)) ∧
      t₁.gpr .x17 = off B (eD + 8 * (i + 1))) ?_ (by decide) (by decide) (by decide +kernel)) fun t₁ ⟨⟨hm, h5, h16, h17⟩, k₁⟩ => ?_
  · brun [hI.x16, hI.x17, hI.x5, t15, hI.scr.ld (show eS + 8 * (i + 1) + 8 ≤ Z by omega_arith),
      hI.scr.st (show eD + 8 * i + 8 ≤ Z by omega_arith), hSj, hsel_eq, off_add]
    refine ⟨?_, ?_⟩ <;> congr 1 <;> omega_arith
  refine WP.mono (dec_ok t₁ .x14) fun t' ⟨⟨h14', hm', _⟩, k'⟩ => ⟨?_, by rw [h14', k₁.gpr .x14 (by decide)]⟩
  have hw8 : Outside B (eD + 8 * i) 8 t.mem t'.mem := by
    rw [hm', hm]; exact writeW_outside _ _ _ (by omega_arith)
  refine ⟨hI.scr.congr (k'.wr.trans k₁.wr), (hI.keep.trans (k₁.trans k')).mono (by decide),
    (k'.gpr .x16 (by decide)).trans h16, (k'.gpr .x17 (by decide)).trans h17, (k'.gpr .x5 (by decide)).trans h5,
    fun k hk => ?_, fun k hk hkw => ?_, ?_⟩
  · rw [hm', hm]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · rw [(writeW_outside t.mem B _ (by omega_arith)).word (by omega_arith) (by omega_arith)]; exact hI.done k hk
    · rw [word_writeW_self]
  · rw [hm', hm, (writeW_outside t.mem B _ (by omega_arith)).word (by omega_arith) (by omega_arith)]
    exact hI.src k (by omega_arith) hkw
  · exact (hI.out.mono (Nat.le_refl _) (by omega_arith)).trans (hw8.mono (by omega_arith) (by omega_arith))

theorem halfPass_eq : halfPass = [.block [ld .x5 .x16, next .x16, .subImm .x .x14 .x12 1],
    countLoop .x14 [ld .x3 .x16, .lsl .x .x4 .x3 63, .lsr .x .x6 .x5 1, .logic .orr .x .x6 .x6 .x4,
      .logic .eor .x .x6 .x6 .x5, .logic .and .x .x6 .x6 .x15, .logic .eor .x .x6 .x6 .x5, st .x6 .x17, next .x16,
      next .x17, mov .x5 .x3],
    .block [.lsr .x .x6 .x5 1, .logic .eor .x .x6 .x6 .x5, .logic .and .x .x6 .x6 .x15, .logic .eor .x .x6 .x6 .x5,
      st .x6 .x17]] := rfl

/-- A halving pass: `[eD] := mb ? [eS] / 2 : [eS]` over `w` words, in place
or not. -/
theorem halfPass_ok {s : State} {B : Addr} {Z w eS eD : Nat} {mb : Bool} (hs : Scr s B Z)
    (h16 : s.gpr .x16 = off B eS) (h17 : s.gpr .x17 = off B eD) (h15 : s.gpr .x15 = mask mb)
    (h12 : s.gpr .x12 = BitVec.ofNat 64 w) (hw : 2 ≤ w) (hw' : w < 2 ^ 31) (hS : eS + 8 * w ≤ Z)
    (hD : eD + 8 * w ≤ Z) (hsep : eD = eS ∨ eD + 8 * w ≤ eS ∨ eS + 8 * w ≤ eD) :
    WP isa (seqs halfPass) s fun t => wv t.mem B eD w = (if mb then wv s.mem B eS w / 2 else wv s.mem B eS w) ∧
      Outside B eD (8 * w) s.mem t.mem ∧ Keep [.x3, .x4, .x5, .x6, .x14, .x16, .x17] s t := by
  have hn := hs.nowrap
  rw [halfPass_eq]
  simp only [seqs]
  refine WP.seq (WP.mono (WP.keep [.x5, .x16, .x14] (Q := fun t => t.gpr .x5 = word s.mem B eS ∧
      t.gpr .x16 = off B (eS + 8) ∧ t.gpr .x14 = BitVec.ofNat 64 (w - 1) ∧ t.mem = s.mem) (by
    brun [h16, h12, hs.ld (show eS + 8 ≤ Z by omega_arith), off_add, ofNat64_pred (show 1 ≤ w by omega_arith) (by omega_arith)])
    (by decide) (by decide) (by decide +kernel)) fun s₀ ⟨⟨h5₀, h16₀, h14₀, hm₀⟩, k₀⟩ => ?_)
  have hs₀ := hs.congr k₀.wr
  have h15₀ : s₀.gpr .x15 = mask mb := (k₀.gpr .x15 (by decide)).trans h15
  have h17₀ : s₀.gpr .x17 = off B eD := (k₀.gpr .x17 (by decide)).trans h17
  have h12₀ : s₀.gpr .x12 = BitVec.ofNat 64 w := (k₀.gpr .x12 (by decide)).trans h12
  refine WP.seq (WP.mono (wp_countdown (N := w - 1) (by omega_arith) (by omega_arith) (HInv s₀ B Z w eS eD mb)
    (fun i hi t hI _ => halfStep_ok h15₀ hS hD hsep (by omega_arith) hI)
    ⟨hs₀, Keep.refl _ _, by rw [h16₀], by rw [h17₀]; rfl, by rw [h5₀, hm₀, Nat.mul_zero, Nat.add_zero],
      fun k hk => absurd hk (by omega_arith), fun k _ _ => rfl, Outside.refl _ _ _ _⟩ h14₀) fun s₁ hI => ?_)
  have t15 : s₁.gpr .x15 = mask mb := (hI.keep.gpr .x15 (by decide)).trans h15₀
  refine WP.mono (WP.keep [.x6] (Q := fun t => t.mem = s₁.mem.writeW (off B (eD + 8 * (w - 1)))
      (if mb then word s₀.mem B (eS + 8 * (w - 1)) >>> 1 else word s₀.mem B (eS + 8 * (w - 1)))) (by
    brun [hI.x17, hI.scr.st (show eD + 8 * (w - 1) + 8 ≤ Z by omega_arith), t15, hI.x5, top_sel])
    (by decide) (by decide) (by decide +kernel)) fun t ⟨hm, k⟩ => ?_
  have hw8 : Outside B (eD + 8 * (w - 1)) 8 s₁.mem t.mem := by rw [hm]; exact writeW_outside _ _ _ (by omega_arith)
  have hdone : ∀ i, i + 1 < w → word t.mem B (eD + 8 * i) =
      hsel mb (word s.mem B (eS + 8 * i)) (word s.mem B (eS + 8 * (i + 1))) := fun i hi => by
    rw [hw8.word (by omega_arith) (by omega_arith), hI.done i (by omega_arith), hm₀]
  have htop : word t.mem B (eD + 8 * (w - 1)) = if mb then word s.mem B (eS + 8 * (w - 1)) >>> 1
      else word s.mem B (eS + 8 * (w - 1)) := by rw [hm, word_writeW_self, hm₀]
  refine ⟨?_, ?_, ((k₀.trans hI.keep).trans k).mono (by decide)⟩
  · cases mb
    · simp only [Bool.false_eq_true, ↓reduceIte] at htop ⊢
      refine wv_congr2 fun i hi => ?_
      rcases Nat.lt_or_ge (i + 1) w with h | h
      · rw [hdone i h]; rfl
      · rw [show i = w - 1 by omega_arith, htop]
    · simp only [↓reduceIte] at htop ⊢
      exact wv_half (by omega_arith) (fun i hi => by rw [hdone i hi]; rfl) htop
  · rw [← hm₀]
    exact (hI.out.mono (Nat.le_refl _) (by omega_arith)).trans (hw8.mono (by omega_arith) (by omega_arith))

/-! ## The lowest nonzero word of `c − 1` -/

theorem xor_one_odd16 {x : BitVec 64} (h : x.toNat % 2 = 1) :
    (x ^^^ BitVec.setWidth 64 (1#16)).toNat = x.toNat / 2 * 2 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [BitVec.toNat_xor, Nat.testBit_xor, show (BitVec.setWidth 64 (1#16) : BitVec 64).toNat = 1 from rfl]
  rcases i with _ | i
  · rw [Nat.testBit_zero, Nat.testBit_zero, Nat.testBit_zero, h, Nat.mul_mod_left]; rfl
  · rw [Nat.testBit_lt_two_pow (show 1 < 2 ^ (i + 1) from Nat.one_lt_two_pow (by omega_arith)), Bool.xor_false,
      show x.toNat / 2 * 2 = x.toNat / 2 ^ 1 * 2 ^ 1 from rfl, Nat.testBit_mul_two_pow, Nat.testBit_div_two_pow]
    simp

/-- Word `j` of `c − 1`, as the scan reads it: `c`'s, bit 0 of the first
flipped. -/
def nwv (m : Mem) (B : Addr) (w j : Nat) : BitVec 64 :=
  if j = 0 then word m B (slot w aN) ^^^ BitVec.setWidth 64 (1#16) else word m B (slot w aN + 8 * j)

theorem nwv_toNat {m : Mem} {B : Addr} {w c : Nat} (hn : wv m B (slot w aN) w = c) (hodd : c % 2 = 1) {j : Nat}
    (hj : j < w) : (nwv m B w j).toNat = (c - 1) / 2 ^ (64 * j) % 2 ^ 64 := by
  unfold nwv
  split
  · rename_i hj0; subst hj0
    have h0 := word_of_wv m B (slot w aN) w (q := 0) hj
    rw [Nat.mul_zero, Nat.add_zero, hn, Nat.pow_zero, Nat.div_one] at h0
    rw [xor_one_odd16 (by rw [h0]; omega_arith), h0, Nat.mul_zero, Nat.pow_zero, Nat.div_one]
    omega_arith
  · rw [word_of_wv m B (slot w aN) w hj, hn, odd_sub_one_div hodd (by omega_arith)]

theorem lw_val (v : BitVec 64) (x : BitVec 64) :
    x ||| v &&& mask (decide (x = 0)) = if x = 0 then v else x := by
  by_cases h : x = 0
  · rw [decide_eq_true h, mask_true, BitVec.and_allOnes, h, ite_eq_left rfl]; exact BitVec.zero_or
  · rw [decide_eq_false h, mask_false]; simp; intro h'; exact absurd h' h

/-- After `i` words of the scan's loop from `s₀`: 0 below the word `i0`,
then it. -/
structure LInv (s₀ : State) (B : Addr) (w i0 : Nat) (x : BitVec 64) (i : Nat) (t : State) : Prop where
  keep : Keep [.x3, .x5, .x6, .x14, .x16] s₀ t
  mem : t.mem = s₀.mem
  x16 : t.gpr .x16 = off B (slot w aN + 8 * (i + 1))
  x5 : t.gpr .x5 = if i + 1 ≤ i0 then 0 else x

/-- The lowest nonzero word of `c − 1` into `x5`; `x7 = 0`, `x8` all ones. -/
theorem lowWord_ok {s : State} {B : Addr} {Z w c : Nat} (h : Ws s B Z w) (hn : wv s.mem B (slot w aN) w = c)
    (hodd : c % 2 = 1) (hc1 : 1 < c) :
    WP isa (seqs lowWord) s fun t =>
      (t.gpr .x5).toNat = (c - 1) / 2 ^ (64 * (mrA c / 64)) % 2 ^ 64 ∧ t.mem = s.mem ∧
      t.gpr .x7 = BitVec.setWidth 64 0#16 ∧ t.gpr .x8 = BitVec.setWidth 64 0#16 - 1#64 ∧
      t.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2)) ∧ t.gpr .x12 = BitVec.ofNat 64 w ∧
      Keep [.x3, .x4, .x5, .x6, .x7, .x8, .x11, .x12, .x14, .x16] s t := by
  have hnw := h.scr.nowrap
  have hw2 := h.w1
  have hw' := h.w2
  have sN := h.sl (show aN < 16 by decide)
  obtain ⟨hN, hm2⟩ := splitTwos_spec (c - 1) (by omega_arith)
  change c - 1 = (Spec.Rsa.splitTwos (c - 1)).2 * 2 ^ mrA c at hN
  obtain ⟨hz, hx1, hx0⟩ := lowWord_bits hN hm2
  have hcw : c < 2 ^ (64 * w) := by rw [← hn]; exact wv_lt _ _ _ _
  have ha : mrA c < 64 * w := by
    rcases Nat.lt_or_ge (mrA c) (64 * w) with h | h
    · exact h
    exfalso
    have h1 : 2 ^ (64 * w) ≤ 2 ^ mrA c := Nat.pow_le_pow_right (by decide) h
    have h2 : 2 ^ mrA c ≤ (Spec.Rsa.splitTwos (c - 1)).2 * 2 ^ mrA c := Nat.le_mul_of_pos_left _ (by omega_arith)
    omega_arith
  generalize hi0 : mrA c / 64 = i0 at hz hx1 hx0 ⊢
  have hi0w : i0 < w := by omega_arith
  have hx : (nwv s.mem B w i0).toNat = (c - 1) / 2 ^ (64 * i0) % 2 ^ 64 := nwv_toNat hn hodd hi0w
  unfold lowWord
  simp only [seqs]
  rw [List.append_assoc]
  refine WP.seq (WP.block_append_iff.mpr (WP.mono h.ws_ok fun s₁ ⟨⟨h12, h11, m₁, _⟩, k₁⟩ => ?_))
  rw [WP.block_append_iff]
  refine WP.mono (base_ok aN .x16 ((k₁.gpr .x0 (by decide)).trans h.x0) h11) fun s₂ ⟨⟨h16, m₂, _⟩, k₂⟩ => ?_
  have k12 := k₁.trans k₂
  refine WP.mono (WP.keep [.x4, .x5, .x7, .x8, .x14, .x16] (Q := fun t => t.gpr .x5 = nwv s.mem B w 0 ∧
      t.gpr .x4 = BitVec.setWidth 64 1#16 ∧ t.gpr .x7 = BitVec.setWidth 64 0#16 ∧
      t.gpr .x8 = BitVec.setWidth 64 0#16 - 1#64 ∧ t.gpr .x16 = off B (slot w aN + 8 * (0 + 1)) ∧
      t.gpr .x14 = BitVec.ofNat 64 (w - 1) ∧ t.mem = s.mem) (by
    brun [h16, (k₂.gpr .x12 (by decide)).trans h12, (h.scr.congr k12.wr).ld (show slot w aN + 8 ≤ Z by omega_arith),
      m₂, m₁, nwv, off_add, ofNat64_pred (show 1 ≤ w by omega_arith) (by omega_arith)])
    (by decide) (by decide) (by decide +kernel)) fun s₃ ⟨⟨h5, h4, h7, h8, h16₃, h14, m₃⟩, k₃⟩ => ?_
  have h0 : nwv s.mem B w 0 = if 0 + 1 ≤ i0 then 0 else nwv s.mem B w i0 := by
    by_cases h : 1 ≤ i0
    · rw [ite_eq_left h]; apply BitVec.eq_of_toNat_eq
      rw [nwv_toNat hn hodd (by omega_arith), Nat.mul_zero, Nat.pow_zero, Nat.div_one]
      have := hz 0 (by omega_arith); rw [Nat.mul_zero, Nat.pow_zero, Nat.div_one] at this; rw [this]; rfl
    · rw [ite_eq_right h, show i0 = 0 by omega_arith]
  have k13 := k12.trans k₃
  refine WP.mono (wp_countdown (N := w - 1) (by omega_arith) (by omega_arith) (LInv s₃ B w i0 (nwv s.mem B w i0))
    (fun i hi t hI _ => ?_) ⟨Keep.refl _ _, rfl, h16₃, by rw [h5, h0]⟩ h14) fun t hI => ⟨?_, by rw [hI.mem, m₃],
      (hI.keep.gpr .x7 (by decide)).trans h7, (hI.keep.gpr .x8 (by decide)).trans h8,
      (hI.keep.gpr .x11 (by decide)).trans ((k₂.trans k₃ |>.gpr .x11 (by decide)).trans h11),
      (hI.keep.gpr .x12 (by decide)).trans ((k₂.trans k₃ |>.gpr .x12 (by decide)).trans h12),
      (k13.trans hI.keep).mono (by decide)⟩
  · have t4 : t.gpr .x4 = BitVec.setWidth 64 1#16 := (hI.keep.gpr .x4 (by decide)).trans h4
    have t7 : t.gpr .x7 = BitVec.setWidth 64 0#16 := (hI.keep.gpr .x7 (by decide)).trans h7
    have t8 : t.gpr .x8 = BitVec.setWidth 64 0#16 - 1#64 := (hI.keep.gpr .x8 (by decide)).trans h8
    have hwj : word t.mem B (slot w aN + 8 * (i + 1)) = nwv s.mem B w (i + 1) := by
      rw [hI.mem, m₃]; unfold nwv; rw [ite_eq_right (show ¬ i + 1 = 0 by omega_arith)]
    have hr : t.gpr .x5 ||| nwv s.mem B w (i + 1) &&& mask (decide (t.gpr .x5 = 0)) =
        if i + 1 + 1 ≤ i0 then 0 else nwv s.mem B w i0 := by
      rw [lw_val, hI.x5]
      rcases Nat.lt_trichotomy (i + 1) i0 with h | h | h
      · have hz0 : nwv s.mem B w (i + 1) = 0 :=
          BitVec.eq_of_toNat_eq (by rw [nwv_toNat hn hodd (by omega_arith), hz (i + 1) h]; rfl)
        simp [show i + 1 ≤ i0 by omega_arith, show i + 1 + 1 ≤ i0 by omega_arith, hz0]
      · subst h; simp
      · have hne : nwv s.mem B w i0 ≠ 0 := fun h0 => by
          have := hx1
          rw [← hx, h0] at this; simp at this
        simp [show ¬ i + 1 ≤ i0 by omega_arith, show ¬ i + 1 + 1 ≤ i0 by omega_arith]; intro h; exact absurd h hne
    have hs₃ := (h.scr.congr k13.wr).congr hI.keep.wr
    rw [WP.block_append_iff]
    refine WP.mono (WP.keep [.x3, .x5, .x6, .x16] (Q := fun t₁ => t₁.gpr .x5 = (if i + 1 + 1 ≤ i0 then 0 else
        nwv s.mem B w i0) ∧ t₁.gpr .x16 = off B (slot w aN + 8 * (i + 1 + 1)) ∧ t₁.mem = t.mem) (by
      brun [hI.x16, t4, t7, t8, hs₃.ld (show slot w aN + 8 * (i + 1) + 8 ≤ Z by omega_arith), hwj, subs_one_c,
        csel_mask', Bool.not_not, hr, off_add]
      rw [show slot w aN + 8 * (i + 1) + 8 = slot w aN + 8 * (i + 1 + 1) by omega_arith]) (by decide) (by decide) (by decide +kernel)) fun t₁ ⟨⟨h5₁, h16₁, m₁'⟩, k'⟩ => ?_
    refine WP.mono (dec_ok t₁ .x14) fun t' ⟨⟨h14', hm', _⟩, k''⟩ => ⟨⟨((hI.keep.trans k').trans k'').mono (by decide),
      by rw [hm', m₁', hI.mem], (k''.gpr .x16 (by decide)).trans h16₁, (k''.gpr .x5 (by decide)).trans h5₁⟩,
      by rw [h14', k'.gpr .x14 (by decide)]⟩
  · rw [hI.x5, ite_eq_right (show ¬ w - 1 + 1 ≤ i0 by omega_arith), hx]

/-! ## The exponent -/

/-- The block after `lowWord`: `l` after the words of `aE`. -/
def lowBit : List Instr :=
  base aE .x10 ++ ([.sub .x .x6 .x7 .x5, .logic .and .x .x6 .x6 .x5, .lsl .x .x9 .x12 3, .add .x .x9 .x10 .x9,
    st .x6 .x9, mov .x15 .x8, mov .x17 .x10] : List Instr) ++ base aN .x16

theorem expSetup_eq : expSetup = lowWord ++ (([.block lowBit] : List (Prog isa)) ++
    (halfPass ++ (halfCond 1 ++ (halfCond 2 ++ halfCond 3)))) := by
  simp only [expSetup, lowBit, List.append_assoc]

theorem low_bit {x : BitVec 64} {k : Nat} (hk : k < 64) (h1 : x.toNat.testBit k = true)
    (h0 : ∀ j < k, x.toNat.testBit j = false) :
    (BitVec.setWidth 64 (0#16) - x) &&& x = BitVec.twoPow 64 k := by
  rw [show BitVec.setWidth 64 (0#16) = 0#64 by decide, BitVec.zero_sub, BitVec.and_comm]
  exact and_neg_eq_twoPow hk h1 h0

theorem ones_mask : BitVec.setWidth 64 (0#16) - 1#64 = mask true := rfl

/-- `l` after the words of `aE`, and the registers of the first halving:
`x16 = aN`, `x17 = x10 = aE`, `x9` at `l`, `x15` all ones. -/
theorem lowBit_ok {s : State} {B : Addr} {Z w : Nat} (hs : Scr s B Z) (h0 : s.gpr .x0 = B)
    (hEZ : slot w aE + 8 * (w + 2) ≤ Z) (hw' : w < 2 ^ 24) {x : BitVec 64} {c : Nat} (h5 : s.gpr .x5 = x)
    (hx : x.toNat.testBit (mrA c % 64) = true) (hx0 : ∀ j < mrA c % 64, x.toNat.testBit j = false)
    (h7 : s.gpr .x7 = BitVec.setWidth 64 0#16) (h8 : s.gpr .x8 = BitVec.setWidth 64 0#16 - 1#64)
    (h11 : s.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2))) (h12 : s.gpr .x12 = BitVec.ofNat 64 w) :
    WP isa (.block lowBit) s fun t =>
      (t.mem = s.mem.writeW (off B (slot w aE + 8 * w)) (BitVec.twoPow 64 (mrA c % 64)) ∧
      t.gpr .x16 = off B (slot w aN) ∧ t.gpr .x17 = off B (slot w aE) ∧ t.gpr .x10 = off B (slot w aE) ∧
      t.gpr .x9 = off B (slot w aE + 8 * w) ∧ t.gpr .x15 = mask true) ∧
      Keep [.x6, .x9, .x10, .x15, .x16, .x17] s t := by
  have hn := hs.nowrap
  unfold lowBit
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (base_ok aE .x10 h0 h11) fun s₁ ⟨⟨h10, m₁, _⟩, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x6, .x9, .x15, .x17] (Q := fun t => t.mem = s.mem.writeW (off B (slot w aE + 8 * w))
      (BitVec.twoPow 64 (mrA c % 64)) ∧ t.gpr .x9 = off B (slot w aE + 8 * w) ∧ t.gpr .x15 = mask true ∧
      t.gpr .x17 = off B (slot w aE)) (by
    brun [h10, (k₁.gpr .x5 (by decide)).trans h5, (k₁.gpr .x7 (by decide)).trans h7,
      (k₁.gpr .x8 (by decide)).trans h8, (k₁.gpr .x12 (by decide)).trans h12,
      ofNat_shl3 (show w < 2 ^ 60 by omega_arith), off_add, low_bit (Nat.mod_lt _ (by decide)) hx hx0,
      (hs.congr k₁.wr).st (show slot w aE + 8 * w + 8 ≤ Z by omega_arith), m₁, ones_mask])
    (by decide) (by decide) (by decide +kernel)) fun s₂ ⟨⟨hm₂, h9, h15, h17⟩, k₂⟩ => ?_
  refine WP.mono (base_ok aN .x16 ((k₁.trans k₂ |>.gpr .x0 (by decide)).trans h0)
    ((k₁.trans k₂ |>.gpr .x11 (by decide)).trans h11)) fun t ⟨⟨h16, m₃, _⟩, k₃⟩ => ?_
  exact ⟨⟨by rw [m₃, hm₂], h16, (k₃.gpr .x17 (by decide)).trans h17,
    (k₂.trans k₃ |>.gpr .x10 (by decide)).trans h10, (k₃.gpr .x9 (by decide)).trans h9,
    (k₃.gpr .x15 (by decide)).trans h15⟩, ((k₁.trans k₂).trans k₃).mono (by decide)⟩

/-- The mask of `σ > j` into `x15`, from `l` at `x9`; `x16 = x17 = x10`. -/
theorem sigMask_ok {s : State} {B : Addr} {Z w c : Nat} (hs : Scr s B Z) (hEZ : slot w aE + 8 * (w + 2) ≤ Z)
    (hL : word s.mem B (slot w aE + 8 * w) = BitVec.twoPow 64 (mrA c % 64))
    (h9 : s.gpr .x9 = off B (slot w aE + 8 * w)) (h7 : s.gpr .x7 = BitVec.setWidth 64 0#16)
    (h8 : s.gpr .x8 = BitVec.setWidth 64 0#16 - 1#64) {j : Nat} (hj : 1 ≤ j ∧ j ≤ 3) :
    WP isa (.block (ldK j ++ [ld .x3 .x9, .logic .and .x .x3 .x3 .x4, movi .x4 1, .subs .x .x3 .x3 .x4,
        .csel .x .x15 .x8 .x7, mov .x16 .x10, mov .x17 .x10])) s fun t =>
      (t.gpr .x15 = mask (decide (j < mrSig c)) ∧ t.gpr .x16 = s.gpr .x10 ∧ t.gpr .x17 = s.gpr .x10 ∧
        t.mem = s.mem) ∧ Keep [.x3, .x4, .x15, .x16, .x17] s t := by
  have hn := hs.nowrap
  have hσ : (!decide (BitVec.twoPow 64 (mrA c % 64) &&& BitVec.ofNat 64 (sigK j) = 0)) = decide (j < mrSig c) := by
    have e := sigK_and j hj (k := mrA c % 64) (Nat.mod_lt _ (by decide))
    rw [sigOf_mod] at e
    unfold mrSig; simp only [e, decide_not, Bool.not_not]
  rw [WP.block_append_iff]
  refine WP.mono (ldK_ok s j) fun s₁ ⟨⟨h4, m₁⟩, k₁⟩ => ?_
  refine WP.mono (WP.keep [.x3, .x4, .x15, .x16, .x17] (Q := fun t => t.gpr .x15 = mask (decide (j < mrSig c)) ∧
      t.gpr .x16 = s.gpr .x10 ∧ t.gpr .x17 = s.gpr .x10 ∧ t.mem = s₁.mem) (by
    brun [(k₁.gpr .x9 (by decide)).trans h9, (k₁.gpr .x7 (by decide)).trans h7, (k₁.gpr .x8 (by decide)).trans h8,
      (k₁.gpr .x10 (by decide)), h4, (hs.congr k₁.wr).ld (show slot w aE + 8 * w + 8 ≤ Z by omega_arith), m₁, hL,
      subs_one_c, hσ, csel_mask_pos]) (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨h15, h16, h17, m⟩, k⟩ =>
    ⟨⟨h15, h16, h17, by rw [m, m₁]⟩, (k₁.trans k).mono (by decide)⟩

/-- A conditional halving of `aE`, in place; `x7` to `x10` and `x12` kept. -/
theorem halfCond_ok {s : State} {B : Addr} {Z w c : Nat} (hs : Scr s B Z) (hEZ : slot w aE + 8 * (w + 2) ≤ Z)
    (hw : 2 ≤ w) (hw' : w < 2 ^ 24) (hL : word s.mem B (slot w aE + 8 * w) = BitVec.twoPow 64 (mrA c % 64))
    (h9 : s.gpr .x9 = off B (slot w aE + 8 * w)) (h10 : s.gpr .x10 = off B (slot w aE))
    (h7 : s.gpr .x7 = BitVec.setWidth 64 0#16) (h8 : s.gpr .x8 = BitVec.setWidth 64 0#16 - 1#64)
    (h12 : s.gpr .x12 = BitVec.ofNat 64 w) {j : Nat} (hj : 1 ≤ j ∧ j ≤ 3) :
    WP isa (seqs (halfCond j)) s fun t =>
      wv t.mem B (slot w aE) w = (if j < mrSig c then wv s.mem B (slot w aE) w / 2 else wv s.mem B (slot w aE) w) ∧
      Outside B (slot w aE) (8 * w) s.mem t.mem ∧ Keep [.x3, .x4, .x5, .x6, .x14, .x15, .x16, .x17] s t := by
  rw [show seqs (halfCond j) = .seq (.block (ldK j ++ [ld .x3 .x9, .logic .and .x .x3 .x3 .x4, movi .x4 1,
      .subs .x .x3 .x3 .x4, .csel .x .x15 .x8 .x7, mov .x16 .x10, mov .x17 .x10])) (seqs halfPass) from rfl]
  refine WP.seq (WP.mono (sigMask_ok hs hEZ hL h9 h7 h8 hj) fun s₁ ⟨⟨h15, h16, h17, hm₁⟩, k₁⟩ => ?_)
  refine WP.mono (halfPass_ok (hs.congr k₁.wr) (h16.trans h10) (h17.trans h10) h15 ((k₁.gpr .x12 (by decide)).trans h12)
    hw (by omega_arith) (by omega_arith) (by omega_arith) (Or.inl rfl))
    fun t ⟨hv, ho, k⟩ => ⟨?_, by rw [← hm₁]; exact ho, (k₁.trans k).mono (by decide)⟩
  rw [hv, hm₁]
  simp only [decide_eq_true_eq]

/-- `expSetup`: `E` in `aE`, and the bit after it (`ECtx`). -/
theorem expSetup_ok {s : State} {B : Addr} {Z w c : Nat} (h : Ws s B Z w) (hEZ : slot w aE + 8 * (w + 2) ≤ Z)
    (hn : wv s.mem B (slot w aN) w = c) (hodd : c % 2 = 1) (hc1 : 1 < c) :
    WP isa (seqs expSetup) s fun t => ECtx t.mem B w c ∧ Frm B [(slot w aE, 8 * (w + 1))] s.mem t.mem ∧
      Ws t B Z w ∧ Keep mmRegs s t := by
  have hnw := h.scr.nowrap
  have hw2 := h.w1
  have hw' := h.w2
  have sN := h.sl (show aN < 16 by decide)
  have hNE : slot w aN + 8 * (w + 2) ≤ slot w aE := slot_lt (show aN < aE by decide)
  obtain ⟨hN, hm2⟩ := splitTwos_spec (c - 1) (by omega_arith)
  change c - 1 = (Spec.Rsa.splitTwos (c - 1)).2 * 2 ^ mrA c at hN
  obtain ⟨-, hx1, hx0⟩ := lowWord_bits hN hm2
  rw [expSetup_eq]
  refine wp_seqs_append (by simp [lowWord]) (by simp) (WP.mono (lowWord_ok h hn hodd hc1)
    fun s₁ ⟨h5, hm₁, h7, h8, h11, h12, k₁⟩ => ?_)
  refine wp_seqs_append (by simp) (by simp [halfPass]) (WP.mono (lowBit_ok (c := c) (h.scr.congr k₁.wr)
    ((k₁.gpr .x0 (by decide)).trans h.x0) hEZ hw' rfl (by rw [h5]; exact hx1) (fun j hj => by rw [h5]; exact hx0 j hj)
    h7 h8 h11 h12) fun s₂ ⟨⟨hm₂, h16, h17, h10, h9, h15⟩, k₂⟩ => ?_)
  rw [hm₁] at hm₂
  have hf₂ : Frm B [(slot w aE, 8 * (w + 1))] s.mem s₂.mem := by
    rw [hm₂]; exact Frm.of_outside ((writeW_outside _ B _ (by omega_arith)).mono (o' := slot w aE) (n' := 8 * (w + 1))
      (by omega_arith) (by omega_arith)) (by simp)
  have hL₂ : word s₂.mem B (slot w aE + 8 * w) = BitVec.twoPow 64 (mrA c % 64) := by rw [hm₂, word_writeW_self]
  have hN₂ : wv s₂.mem B (slot w aN) w = c := by
    rw [hf₂.wv_eq (fun r hr => by simp at hr; subst hr; left; simp only; omega_arith) (by omega_arith)]; exact hn
  have k12 := k₁.trans k₂
  have h12₂ : s₂.gpr .x12 = BitVec.ofNat 64 w := (k₂.gpr .x12 (by decide)).trans h12
  -- `E := c / 2`.
  refine wp_seqs_append (by simp [halfPass]) (by simp [halfCond]) (WP.mono (halfPass_ok (h.scr.congr k12.wr) h16 h17
    h15 h12₂ hw2 (by omega_arith) (by omega_arith) (by omega_arith) (Or.inr (Or.inr (by omega_arith)))) fun s₃ ⟨hv₃, ho₃, k₃⟩ => ?_)
  rw [hN₂] at hv₃
  simp only [↓reduceIte] at hv₃
  have hf₃ : Frm B [(slot w aE, 8 * (w + 1))] s₂.mem s₃.mem :=
    Frm.of_outside (ho₃.mono (o' := slot w aE) (n' := 8 * (w + 1)) (by omega_arith) (by omega_arith)) (by simp)
  have hL₃ : word s₃.mem B (slot w aE + 8 * w) = BitVec.twoPow 64 (mrA c % 64) := by
    rw [ho₃.word (Or.inr (by omega_arith)) (by omega_arith)]; exact hL₂
  have k13 := k12.trans k₃
  have r₃ : ∀ r, r = Reg.x7 ∨ r = Reg.x8 ∨ r = Reg.x9 ∨ r = Reg.x10 ∨ r = Reg.x12 → s₃.gpr r = s₂.gpr r := by
    rintro r (rfl | rfl | rfl | rfl | rfl) <;> exact k₃.gpr _ (by decide)
  have h7₂ : s₂.gpr .x7 = BitVec.setWidth 64 0#16 := (k₂.gpr .x7 (by decide)).trans h7
  have h8₂ : s₂.gpr .x8 = BitVec.setWidth 64 0#16 - 1#64 := (k₂.gpr .x8 (by decide)).trans h8
  -- The three conditional halvings.
  refine wp_seqs_append (by simp [halfCond]) (by simp [halfCond]) (WP.mono (halfCond_ok (h.scr.congr k13.wr) hEZ hw2 hw'
    hL₃ ((r₃ _ (by simp)).trans h9) ((r₃ _ (by simp)).trans h10) ((r₃ _ (by simp)).trans h7₂)
    ((r₃ _ (by simp)).trans h8₂) ((r₃ _ (by simp)).trans h12₂) (j := 1) (by decide)) fun s₄ ⟨hv₄, ho₄, k₄⟩ => ?_)
  have hf₄ : Frm B [(slot w aE, 8 * (w + 1))] s₃.mem s₄.mem :=
    Frm.of_outside (ho₄.mono (o' := slot w aE) (n' := 8 * (w + 1)) (by omega_arith) (by omega_arith)) (by simp)
  have hL₄ : word s₄.mem B (slot w aE + 8 * w) = BitVec.twoPow 64 (mrA c % 64) := by
    rw [ho₄.word (Or.inr (by omega_arith)) (by omega_arith)]; exact hL₃
  have k14 := k13.trans k₄
  have r₄ : ∀ r, r = Reg.x7 ∨ r = Reg.x8 ∨ r = Reg.x9 ∨ r = Reg.x10 ∨ r = Reg.x12 → s₄.gpr r = s₂.gpr r := by
    rintro r (rfl | rfl | rfl | rfl | rfl) <;> exact (k₃.trans k₄).gpr _ (by decide)
  refine wp_seqs_append (by simp [halfCond]) (by simp [halfCond]) (WP.mono (halfCond_ok (h.scr.congr k14.wr) hEZ hw2 hw'
    hL₄ ((r₄ _ (by simp)).trans h9) ((r₄ _ (by simp)).trans h10) ((r₄ _ (by simp)).trans h7₂)
    ((r₄ _ (by simp)).trans h8₂) ((r₄ _ (by simp)).trans h12₂) (j := 2) (by decide)) fun s₅ ⟨hv₅, ho₅, k₅⟩ => ?_)
  have hf₅ : Frm B [(slot w aE, 8 * (w + 1))] s₄.mem s₅.mem :=
    Frm.of_outside (ho₅.mono (o' := slot w aE) (n' := 8 * (w + 1)) (by omega_arith) (by omega_arith)) (by simp)
  have hL₅ : word s₅.mem B (slot w aE + 8 * w) = BitVec.twoPow 64 (mrA c % 64) := by
    rw [ho₅.word (Or.inr (by omega_arith)) (by omega_arith)]; exact hL₄
  have k15 := k14.trans k₅
  have r₅ : ∀ r, r = Reg.x7 ∨ r = Reg.x8 ∨ r = Reg.x9 ∨ r = Reg.x10 ∨ r = Reg.x12 → s₅.gpr r = s₂.gpr r := by
    rintro r (rfl | rfl | rfl | rfl | rfl) <;> exact ((k₃.trans k₄).trans k₅).gpr _ (by decide)
  refine WP.mono (halfCond_ok (h.scr.congr k15.wr) hEZ hw2 hw'
    hL₅ ((r₅ _ (by simp)).trans h9) ((r₅ _ (by simp)).trans h10) ((r₅ _ (by simp)).trans h7₂)
    ((r₅ _ (by simp)).trans h8₂) ((r₅ _ (by simp)).trans h12₂) (j := 3) (by decide)) fun t ⟨hv, ho, k⟩ => ?_
  have hft : Frm B [(slot w aE, 8 * (w + 1))] s₅.mem t.mem :=
    Frm.of_outside (ho.mono (o' := slot w aE) (n' := 8 * (w + 1)) (by omega_arith) (by omega_arith)) (by simp)
  have hf : Frm B [(slot w aE, 8 * (w + 1))] s.mem t.mem :=
    (((hf₂.trans hf₃).trans hf₄).trans hf₅).trans hft
  refine ⟨⟨?_, by rw [ho.word (Or.inr (by omega_arith)) (by omega_arith)]; exact hL₅⟩, hf,
    h.congr' hf (by w_mut) (k15.trans k) (by decide), (k15.trans k).mono (by decide)⟩
  rw [hv, hv₅, hv₄, hv₃, ← mrE_halves hodd]

end VG.Proof.RsaKeyGen.AArch64
