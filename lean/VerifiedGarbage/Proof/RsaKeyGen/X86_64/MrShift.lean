module

public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrSq
import VerifiedGarbage.Proof.RsaKeyGen.Halve
import VerifiedGarbage.Proof.RsaKeyGen.MrMont
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrSel
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.TrialLoop
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.GCongr
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.ModE
import VerifiedGarbage.Proof.RsaKeyGen.Gcd

/-!
# A candidate on x86-64: Miller–Rabin's exponent

`halfPass_ok`: `[rbx] := r15 ? [rsi] / 2 : [rsi]`, in place or not;
`lowWord_ok`: the lowest nonzero word of `c − 1`; `expSetup_ok`: its lowest
set bit after the words of `aE`, then `E = (c − 1) / 2^σ` in `aE` (`ECtx`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 VG.Proof.RsaKeyGen

/-- A word of the halved number, or the word itself. -/
def hsel (mb : Bool) (a b : BitVec 64) : BitVec 64 := if mb then (a >>> 1) ||| (b <<< 63) else a

/-- After the words below `j − 1` of a halving pass from `s₀`. -/
structure HInv (s₀ : State) (B : Addr) (Z w eS eD : Nat) (mb : Bool) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.rax, .rbp, .rcx, .rdx, .r14] s₀ t
  r14 : t.gpr .r14 = BitVec.ofNat 64 j
  rbp : t.gpr .rbp = word s₀.mem B (eS + 8 * (j - 1))
  done : ∀ i, i + 1 < j → word t.mem B (eD + 8 * i) =
    hsel mb (word s₀.mem B (eS + 8 * i)) (word s₀.mem B (eS + 8 * (i + 1)))
  src : ∀ i, j ≤ i → i < w → word t.mem B (eS + 8 * i) = word s₀.mem B (eS + 8 * i)
  out : Outside B eD (8 * (j - 1)) s₀.mem t.mem

theorem hsel_eq (mb : Bool) (a b : BitVec 64) :
    (((a >>> 1) ||| (b <<< 63)) ^^^ a) &&& mask mb ^^^ a = hsel mb a b := by
  rw [sel_word]; rfl

/-- A word of a halving pass. -/
theorem halfStep_ok {s₀ : State} {B : Addr} {Z w eS eD : Nat} {mb : Bool}
    (hsi : s₀.gpr .rsi = off B eS) (hbx : s₀.gpr .rbx = off B eD) (h15 : s₀.gpr .r15 = mask mb)
    (h12 : s₀.gpr .r12 = BitVec.ofNat 64 w) (hw' : w < 2 ^ 31) (hS : eS + 8 * w ≤ Z) (hD : eD + 8 * w ≤ Z)
    (hsep : eD = eS ∨ eD + 8 * w ≤ eS ∨ eS + 8 * w ≤ eD) {j : Nat} (hj1 : 1 ≤ j) (hj : j < w)
    {t : State} (hI : HInv s₀ B Z w eS eD mb j t) :
    WP isa (.block (([.mov .rax (.mem (ix .rsi .r14)), .mov .rdx (.reg .rax), .shift .shl .rdx 63,
        .mov .rcx (.reg .rbp), .shift .shr .rcx 1, .alu .or .rcx (.reg .rdx), .alu .xor .rcx (.reg .rbp),
        .alu .and .rcx (.reg .r15), .alu .xor .rcx (.reg .rbp), .store (ix .rbx .r14 (-8)) .rcx,
        .mov .rbp (.reg .rax)] : List Instr) ++ ([.alu .add .r14 (.imm 1), .alu .cmp .r14 (.reg .r12)] : List Instr))) t
      fun t' => t'.zf = some (decide (j + 1 = w)) ∧ HInv s₀ B Z w eS eD mb (j + 1) t' := by
  have hn := hI.scr.nowrap
  have tsi : t.gpr .rsi = off B eS := (hI.keep.gpr (by decide)).trans hsi
  have tbx : t.gpr .rbx = off B eD := (hI.keep.gpr (by decide)).trans hbx
  have t15 : t.gpr .r15 = mask mb := (hI.keep.gpr (by decide)).trans h15
  have t12 : t.gpr .r12 = BitVec.ofNat 64 w := (hI.keep.gpr (by decide)).trans h12
  have hSj : word t.mem B (eS + 8 * j) = word s₀.mem B (eS + 8 * j) := hI.src j (Nat.le_refl _) hj
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rax, .rdx, .rcx, .rbp] (Q := fun t₁ => t₁.mem = t.mem.writeW (off B (eD + 8 * (j - 1)))
      (hsel mb (word s₀.mem B (eS + 8 * (j - 1))) (word s₀.mem B (eS + 8 * j))) ∧
      t₁.gpr .rbp = word s₀.mem B (eS + 8 * j)) ?_ rfl) fun t₁ ⟨⟨hm, hbp⟩, k₁⟩ => ?_
  · xrun [State.ea, ix, addr0 tsi hI.r14, addrm8 tbx hI.r14 hj1, hI.scr.ld (show eS + 8 * j + 8 ≤ Z by omega_arith),
      hI.scr.st (show eD + 8 * (j - 1) + 8 ≤ Z by omega_arith), t15, hI.rbp, hSj, hsel_eq]
  have t₁14 : t₁.gpr .r14 = BitVec.ofNat 64 j := (k₁.gpr (by decide)).trans hI.r14
  have t₁12 : t₁.gpr .r12 = BitVec.ofNat 64 w := (k₁.gpr (by decide)).trans t12
  refine WP.mono (count_ok t₁ t₁14 t₁12 (by omega_arith) (by omega_arith)) fun t' ⟨hz, h14, hm', k'⟩ => ⟨hz, ?_⟩
  have hw8 : Outside B (eD + 8 * (j - 1)) 8 t.mem t'.mem := by
    rw [hm', hm]; exact writeW_outside _ _ _ (by omega_arith)
  refine ⟨hI.scr.congr (k'.2.2.trans k₁.2.2), ((hI.keep.trans k₁).trans k').mono (by decide), h14,
    by rw [(k'.gpr (by decide) : t'.gpr .rbp = t₁.gpr .rbp), hbp, show j + 1 - 1 = j by omega_arith], fun i hi => ?_,
    fun i hi hiw => ?_, ?_⟩
  · rw [hm', hm]
    rcases Nat.lt_succ_iff_lt_or_eq.mp (show i + 1 < j + 1 from hi) with hi | hi
    · rw [(writeW_outside t.mem B _ (by omega_arith)).word (by omega_arith) (by omega_arith)]; exact hI.done i hi
    · rw [show i = j - 1 by omega_arith, word_writeW_self, show j - 1 + 1 = j by omega_arith]
  · rw [hm', hm, (writeW_outside t.mem B _ (by omega_arith)).word (by omega_arith) (by omega_arith)]
    exact hI.src i (by omega_arith) hiw
  · exact (hI.out.mono (Nat.le_refl _) (by omega_arith)).trans (hw8.mono (by omega_arith) (by omega_arith))

theorem halfPass_eq : halfPass = [.block [.mov .rbp (.mem (at0 .rsi))],
    wordLoop 1 [.mov .rax (.mem (ix .rsi .r14)), .mov .rdx (.reg .rax), .shift .shl .rdx 63, .mov .rcx (.reg .rbp),
      .shift .shr .rcx 1, .alu .or .rcx (.reg .rdx), .alu .xor .rcx (.reg .rbp), .alu .and .rcx (.reg .r15),
      .alu .xor .rcx (.reg .rbp), .store (ix .rbx .r14 (-8)) .rcx, .mov .rbp (.reg .rax)],
    .block [.mov .rcx (.reg .rbp), .shift .shr .rcx 1, .alu .xor .rcx (.reg .rbp), .alu .and .rcx (.reg .r15),
      .alu .xor .rcx (.reg .rbp), .store (ix .rbx .r12 (-8)) .rcx]] := rfl

theorem top_sel (a : BitVec 64) (mb : Bool) :
    ((a >>> 1) ^^^ a) &&& mask mb ^^^ a = if mb then a >>> 1 else a := sel_word _ _ _

/-- A halving pass: `[eD] := mb ? [eS] / 2 : [eS]` over `w` words, in place
or not. -/
theorem halfPass_ok {s : State} {B : Addr} {Z w eS eD : Nat} {mb : Bool} (hs : Scr s B Z)
    (hsi : s.gpr .rsi = off B eS) (hbx : s.gpr .rbx = off B eD) (h15 : s.gpr .r15 = mask mb)
    (h12 : s.gpr .r12 = BitVec.ofNat 64 w) (hw : 2 ≤ w) (hw' : w < 2 ^ 31) (hS : eS + 8 * w ≤ Z)
    (hD : eD + 8 * w ≤ Z) (hsep : eD = eS ∨ eD + 8 * w ≤ eS ∨ eS + 8 * w ≤ eD) :
    WP isa (seqs halfPass) s fun t => wv t.mem B eD w = (if mb then wv s.mem B eS w / 2 else wv s.mem B eS w) ∧
      Outside B eD (8 * w) s.mem t.mem ∧ Keep [.rax, .rbp, .rcx, .rdx, .r14] s t := by
  have hn := hs.nowrap
  rw [halfPass_eq]
  simp only [seqs]
  refine WP.seq (WP.mono (WP.keep [.rbp] (Q := fun t => t.gpr .rbp = word s.mem B eS ∧ t.mem = s.mem) (by
    xrun [State.ea, at0, hsi, hs.ld (show eS + 8 ≤ Z by omega_arith), BitVec.ofInt_ofNat, BitVec.add_zero]) rfl) fun s₀ ⟨⟨hbp₀, hm₀⟩, k₀⟩ => ?_)
  have hs₀ := hs.congr k₀.2.2
  have hsi₀ : s₀.gpr .rsi = off B eS := (k₀.gpr (by decide)).trans hsi
  have hbx₀ : s₀.gpr .rbx = off B eD := (k₀.gpr (by decide)).trans hbx
  have h15₀ : s₀.gpr .r15 = mask mb := (k₀.gpr (by decide)).trans h15
  have h12₀ : s₀.gpr .r12 = BitVec.ofNat 64 w := (k₀.gpr (by decide)).trans h12
  refine WP.seq (WP.mono (wordLoop_ok (start := 1) (N := w) (by omega_arith) hw' (HInv s₀ B Z w eS eD mb)
    (fun t h14 hm k _ => ⟨hs₀.congr k.2.2, k.mono (by decide), h14,
      by rw [(k.gpr (by decide) : t.gpr .rbp = s₀.gpr .rbp), hbp₀, hm₀]; rfl,
      fun i hi => absurd hi (by omega_arith), fun i _ _ => by rw [hm], by rw [hm]; exact Outside.refl _ _ _ _⟩)
    (fun j hj1 hj t hI => halfStep_ok hsi₀ hbx₀ h15₀ h12₀ hw' hS hD hsep hj1 hj hI)) fun s₁ hI => ?_)
  have t12 : s₁.gpr .r12 = BitVec.ofNat 64 w := (hI.keep.gpr (by decide)).trans h12₀
  have t15 : s₁.gpr .r15 = mask mb := (hI.keep.gpr (by decide)).trans h15₀
  have tbx : s₁.gpr .rbx = off B eD := (hI.keep.gpr (by decide)).trans hbx₀
  refine WP.mono (WP.keep [.rcx] (Q := fun t => t.mem = s₁.mem.writeW (off B (eD + 8 * (w - 1)))
      (if mb then word s₀.mem B (eS + 8 * (w - 1)) >>> 1 else word s₀.mem B (eS + 8 * (w - 1)))) (by
    xrun [State.ea, ix, addrm8 tbx t12 (by omega_arith), hI.scr.st (show eD + 8 * (w - 1) + 8 ≤ Z by omega_arith), t15, hI.rbp,
      top_sel]) rfl) fun t ⟨hm, k⟩ => ?_
  have hw8 : Outside B (eD + 8 * (w - 1)) 8 s₁.mem t.mem := by rw [hm]; exact writeW_outside _ _ _ (by omega_arith)
  have hdone : ∀ i, i + 1 < w → word t.mem B (eD + 8 * i) =
      hsel mb (word s.mem B (eS + 8 * i)) (word s.mem B (eS + 8 * (i + 1))) := fun i hi => by
    rw [hw8.word (by omega_arith) (by omega_arith), hI.done i hi, hm₀]
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

theorem and_m2 (x : BitVec 64) :
    (x &&& BitVec.signExtend 64 (BitVec.ofInt 32 (-2))).toNat = x.toNat / 2 * 2 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [show BitVec.signExtend 64 (BitVec.ofInt 32 (-2)) = 0xFFFFFFFFFFFFFFFE#64 by decide, BitVec.toNat_and,
    Nat.testBit_and, show (0xFFFFFFFFFFFFFFFE#64).toNat = (2 ^ 63 - 1) * 2 ^ 1 by decide,
    show x.toNat / 2 * 2 = x.toNat / 2 ^ 1 * 2 ^ 1 from rfl, Nat.testBit_mul_two_pow, Nat.testBit_mul_two_pow,
    Nat.testBit_div_two_pow, Nat.testBit_two_pow_sub_one]
  rcases i with _ | i
  · simp
  · rw [show i + 1 - 1 + 1 = i + 1 by omega_arith]
    by_cases hi : i + 1 < 64
    · simp only [Nat.add_sub_cancel, show i < 63 by omega_arith, decide_true, Bool.and_true, Nat.le_add_left,
        Bool.true_and]
    · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by decide) (by omega_arith)))]
      simp

/-- Word `j` of `c − 1`, as the scan reads it: `c`'s, bit 0 of the first
cleared. -/
def nwv (m : Mem) (B : Addr) (w j : Nat) : BitVec 64 :=
  if j = 0 then word m B (slot w aN) &&& BitVec.signExtend 64 (BitVec.ofInt 32 (-2)) else word m B (slot w aN + 8 * j)

theorem nwv_toNat {m : Mem} {B : Addr} {w c : Nat} (hn : wv m B (slot w aN) w = c) (hodd : c % 2 = 1) {j : Nat}
    (hj : j < w) : (nwv m B w j).toNat = (c - 1) / 2 ^ (64 * j) % 2 ^ 64 := by
  unfold nwv
  split
  · rename_i hj0; subst hj0
    have h0 := word_of_wv m B (slot w aN) w (q := 0) hj
    rw [Nat.mul_zero, Nat.add_zero, hn, Nat.pow_zero, Nat.div_one] at h0
    rw [and_m2, h0, Nat.mul_zero, Nat.pow_zero, Nat.div_one]
    omega_arith
  · rw [word_of_wv m B (slot w aN) w hj, hn, odd_sub_one_div hodd (by omega_arith)]

/-- After `j` words of the scan from `s₀`: 0 below the word `i0`, then it. -/
structure LInv (s₀ : State) (i0 : Nat) (x : BitVec 64) (j : Nat) (t : State) : Prop where
  keep : Keep [.rax, .rdx, .rbp, .r14] s₀ t
  mem : t.mem = s₀.mem
  r14 : t.gpr .r14 = BitVec.ofNat 64 j
  rbp : t.gpr .rbp = if j ≤ i0 then 0 else x

theorem lw_val (v : BitVec 64) (x : BitVec 64) :
    x ||| v &&& mask (decide (x = 0)) = if x = 0 then v else x := by
  by_cases h : x = 0
  · rw [decide_eq_true h, mask_true, BitVec.and_allOnes, h, ite_eq_left rfl]; exact BitVec.zero_or
  · rw [decide_eq_false h, mask_false]; simp; intro h'; exact absurd h' h

/-- The lowest nonzero word of `c − 1` into `rbp`. -/
theorem lowWord_ok {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64} {c : Nat} (hg : Good s B Z w mi)
    (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31) (hn : wv s.mem B (slot w aN) w = c) (hodd : c % 2 = 1)
    (hc1 : 1 < c) :
    WP isa (seqs lowWord) s fun t =>
      (t.gpr .rbp).toNat = (c - 1) / 2 ^ (64 * (mrA c / 64)) % 2 ^ 64 ∧ t.mem = s.mem ∧
      Keep [.rax, .rdx, .rbp, .r8, .r12, .r14] s t := by
  have hnw := hg.scr.nowrap
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot w 8 hi; omega_arith)
  have sN := slot_le (w := w) (show aN < 8 by decide)
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
  have hz' : ∀ j, 1 ≤ j → j < i0 → word s.mem B (slot w aN + 8 * j) = 0 := fun j hj1 hj => by
    apply BitVec.eq_of_toNat_eq
    have := nwv_toNat (m := s.mem) (B := B) hn hodd (j := j) (by omega_arith)
    unfold nwv at this
    rw [ite_eq_right (show ¬ j = 0 by omega_arith)] at this
    rw [this, hz j hj]; rfl
  have hx : (nwv s.mem B w i0).toNat = (c - 1) / 2 ^ (64 * i0) % 2 ^ 64 := nwv_toNat hn hodd hi0w
  unfold lowWord
  simp only [seqs]
  refine WP.seq (WP.mono (WP.keep [.r12, .r8, .rbp] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 w ∧
      t.gpr .r8 = off B (slot w aN) ∧ t.gpr .rbp = nwv s.mem B w 0 ∧ t.mem = s.mem) (by
    xrun [State.ea, hdr, at0, hg.rdi, hdrOff, hl sW (by decide), hl (sArr aN) (by decide), hg.hdr.hw,
      hg.hdr.harr aN (by decide), BitVec.ofInt_ofNat, BitVec.add_zero, hg.scr.ld (show slot w aN + 8 ≤ Z by omega_arith)]
    rfl) rfl) fun s₁ ⟨⟨h12, h8, hbp, hm₁⟩, k₁⟩ => ?_)
  have h0 : nwv s.mem B w 0 = if 1 ≤ i0 then 0 else nwv s.mem B w i0 := by
    by_cases h : 1 ≤ i0
    · rw [ite_eq_left h]; apply BitVec.eq_of_toNat_eq
      rw [nwv_toNat hn hodd (by omega_arith), Nat.mul_zero, Nat.pow_zero, Nat.div_one]
      have := hz 0 (by omega_arith); rw [Nat.mul_zero, Nat.pow_zero, Nat.div_one] at this; rw [this]; rfl
    · rw [ite_eq_right h, show i0 = 0 by omega_arith]
  refine WP.mono (wordLoop_ok (start := 1) (N := w) (by omega_arith) hw' (LInv s₁ i0 (nwv s.mem B w i0))
    (fun t h14 hm k _ => ⟨k.mono (by decide), hm, h14, by rw [(k.gpr (by decide) : t.gpr .rbp = s₁.gpr .rbp), hbp, h0]⟩)
    (fun j hj1 hj t hI => ?_)) fun t hI => ⟨?_, by rw [hI.mem, hm₁], (k₁.trans hI.keep).mono (by decide)⟩
  · have t8 : t.gpr .r8 = off B (slot w aN) := (hI.keep.gpr (by decide)).trans h8
    have t12 : t.gpr .r12 = BitVec.ofNat 64 w := (hI.keep.gpr (by decide)).trans h12
    have hwj : word t.mem B (slot w aN + 8 * j) = nwv s.mem B w j := by
      rw [hI.mem, hm₁]; unfold nwv; rw [ite_eq_right (show ¬ j = 0 by omega_arith)]
    rw [WP.block_append_iff]
    refine WP.mono (WP.keep [.rax, .rdx, .rbp] (Q := fun t₁ => t₁.gpr .rbp = (if j + 1 ≤ i0 then 0 else
        nwv s.mem B w i0) ∧ t₁.mem = t.mem) ?_ rfl) fun t₁ ⟨⟨hbp₁, hm₁'⟩, k'⟩ => ?_
    · have hr : t.gpr .rbp ||| nwv s.mem B w j &&& mask (decide (t.gpr .rbp = 0)) =
          if j + 1 ≤ i0 then 0 else nwv s.mem B w i0 := by
        rw [lw_val, hI.rbp]
        rcases Nat.lt_trichotomy j i0 with h | rfl | h
        · have hz0 : nwv s.mem B w j = 0 :=
            BitVec.eq_of_toNat_eq (by rw [nwv_toNat hn hodd (by omega_arith), hz j h]; rfl)
          simp [show j ≤ i0 by omega_arith, show j + 1 ≤ i0 by omega_arith, hz0]
        · simp; intro h; omega_arith
        · have hne : nwv s.mem B w i0 ≠ 0 := fun h0 => by
            have := hx1
            rw [← hx, h0] at this; simp at this
          simp [show ¬ j ≤ i0 by omega_arith, show ¬ j + 1 ≤ i0 by omega_arith]; intro h; exact absurd h hne
      xrun [State.ea, ix, addr0 t8 hI.r14,
        ((hg.scr.congr k₁.2.2).congr hI.keep.2.2).ld (show slot w aN + 8 * j + 8 ≤ Z by omega_arith), hwj,
        decide_lt_one, mask_def', hr]
    have t₁14 : t₁.gpr .r14 = BitVec.ofNat 64 j := (k'.gpr (by decide)).trans hI.r14
    refine WP.mono (count_ok t₁ t₁14 ((k'.gpr (by decide)).trans t12) (by omega_arith) (by omega_arith))
      fun t' ⟨hz', h14, hm', k''⟩ => ⟨hz', ((hI.keep.trans k').trans k'').mono (by decide), by rw [hm', hm₁', hI.mem],
        h14, by rw [(k''.gpr (by decide) : t'.gpr .rbp = t₁.gpr .rbp), hbp₁]⟩
  · rw [hI.rbp, ite_eq_right (show ¬ w ≤ i0 by omega_arith), hx]

/-! ## The exponent -/

theorem expSetup_eq : expSetup = lowWord ++ (([.block (extBase aE .rbx ++ ([.mov .r12 (.mem (hdr sW)),
    .mov .rsi (.mem (hdr (sArr aN))), .mov .r15 (.imm (BitVec.ofInt 32 (-1))), .mov32 .rax (.imm 0),
    .alu .sub .rax (.reg .rbp), .alu .and .rax (.reg .rbp), .store (ix .rbx .r12) .rax] : List Instr))] : List (Prog isa)) ++
    (halfPass ++ (halfCond 1 ++ (halfCond 2 ++ halfCond 3)))) := by
  simp only [expSetup, List.append_assoc]

theorem low_bit {x : BitVec 64} {k : Nat} (hk : k < 64) (h1 : x.toNat.testBit k = true)
    (h0 : ∀ j < k, x.toNat.testBit j = false) :
    (BitVec.setWidth 64 (0 : BitVec 32) - x) &&& x = BitVec.twoPow 64 k := by
  rw [show BitVec.setWidth 64 (0 : BitVec 32) = 0#64 by decide, BitVec.zero_sub, BitVec.and_comm]
  exact and_neg_eq_twoPow hk h1 h0

/-- The lowest set bit of `c − 1`'s lowest nonzero word (in `rbp`) after
the words of `aE`, and the registers of the first halving: `rsi = aN`,
`rbx = aE`, `r12 = w`, `r15` all ones. -/
theorem lowBit_ok {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64} {c : Nat} (hg : Good s B Z w mi)
    (hd : MrDims B Z w) {x : BitVec 64} (hbp : s.gpr .rbp = x) (hx : x.toNat.testBit (mrA c % 64) = true)
    (hx0 : ∀ j < mrA c % 64, x.toNat.testBit j = false) :
    WP isa (.block (extBase aE .rbx ++ ([.mov .r12 (.mem (hdr sW)), .mov .rsi (.mem (hdr (sArr aN))),
        .mov .r15 (.imm (BitVec.ofInt 32 (-1))), .mov32 .rax (.imm 0), .alu .sub .rax (.reg .rbp),
        .alu .and .rax (.reg .rbp), .store (ix .rbx .r12) .rax] : List Instr))) s fun t =>
      t.mem = s.mem.writeW (off B (slot w aE + 8 * w)) (BitVec.twoPow 64 (mrA c % 64)) ∧
      t.gpr .rsi = off B (slot w aN) ∧ t.gpr .rbx = off B (slot w aE) ∧ t.gpr .r12 = BitVec.ofNat 64 w ∧
      t.gpr .r15 = mask true ∧ Keep [.rax, .rbx, .rsi, .r12, .r15] s t := by
  have hn := hg.scr.nowrap
  have hZ := hd.z
  have hw' : w < 2 ^ 31 := by have := hd.w128; omega_arith
  have hEZ := aE_fits hd
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot w 8 hi; omega_arith)
  rw [WP.block_append_iff]
  refine WP.mono (extBase_ok hg hZ hw' (j := aE) (by decide) (r := .rbx) (by decide) rfl rfl)
    fun s₁ ⟨hbx, hm₁, k₁⟩ => ?_
  have hbp₁ : s₁.gpr .rbp = x := (k₁.gpr (by decide)).trans hbp
  have hdi₁ : s₁.gpr .rdi = B := (k₁.gpr (by decide)).trans hg.rdi
  have hl₁ : ∀ i < 32, InRegions (s₁.rd ++ s₁.wr) (off B (8 * i)) 8 := fun i hi => by
    rw [k₁.2.1, k₁.2.2]; exact hl i hi
  refine WP.mono (WP.keep [.r12, .rax, .rsi, .r15] (Q := fun t => t.mem = s.mem.writeW (off B (slot w aE + 8 * w))
      (BitVec.twoPow 64 (mrA c % 64)) ∧ t.gpr .rsi = off B (slot w aN) ∧ t.gpr .r12 = BitVec.ofNat 64 w ∧
      t.gpr .r15 = mask true) (by
    xrun [State.ea, hdr, ix, hdi₁, hdrOff, hl₁ sW (by decide), hl₁ (sArr aN) (by decide), hm₁, hg.hdr.hw,
      hg.hdr.harr aN (by decide), hbx, addr0 rfl rfl, hbp₁, low_bit (Nat.mod_lt _ (by decide)) hx hx0,
      (hg.scr.congr k₁.2.2).st (show slot w aE + 8 * w + 8 ≤ Z by omega_arith)]) rfl) fun t ⟨⟨hm, hsi, h12, h15⟩, k⟩ =>
      ⟨hm, hsi, by rw [k.gpr (by decide)]; exact hbx, h12, h15, (k₁.trans k).mono (by decide)⟩

/-- The mask of `σ > j` into `r15`, from the bit after the words of `aE`
(its base in `rbx`, `w` in `r12`); `rsi := rbx`. -/
theorem sigMask_ok {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64} {c : Nat} (hg : Good s B Z w mi)
    (hd : MrDims B Z w) (hL : word s.mem B (slot w aE + 8 * w) = BitVec.twoPow 64 (mrA c % 64))
    (hbx : s.gpr .rbx = off B (slot w aE)) (h12 : s.gpr .r12 = BitVec.ofNat 64 w) {j : Nat} (hj : 1 ≤ j ∧ j ≤ 3) :
    WP isa (.block [.mov .rsi (.reg .rbx), .movImm64 .r15 (sigK j), .alu .and .r15 (.mem (ix .rbx .r12)),
        .alu .cmp .r15 (.imm 1), .alu .sbb .r15 (.reg .r15), .alu .xor .r15 (.imm (BitVec.ofInt 32 (-1)))]) s fun t =>
      t.gpr .r15 = mask (decide (j < mrSig c)) ∧ t.gpr .rsi = off B (slot w aE) ∧ t.mem = s.mem ∧
      Keep [.rsi, .r15] s t := by
  have hn := hg.scr.nowrap
  have hEZ := aE_fits hd
  have hσ : (!decide (sigK j &&& BitVec.twoPow 64 (mrA c % 64) = 0)) = decide (j < mrSig c) := by
    have h := sigK_and j hj (k := mrA c % 64) (Nat.mod_lt _ (by decide))
    rw [sigOf_mod] at h
    unfold mrSig; simp only [h, decide_not, Bool.not_not]
  refine WP.mono (WP.keep [.rsi, .r15] (Q := fun t => t.gpr .r15 = mask (decide (j < mrSig c)) ∧
      t.gpr .rsi = off B (slot w aE) ∧ t.mem = s.mem) (by
    xrun [State.ea, ix, hbx, h12, addr0 rfl rfl, hg.scr.ld (show slot w aE + 8 * w + 8 ≤ Z by omega_arith), hL, decide_lt_one,
      mask_def', mask_ne0, hσ]) rfl)
    fun t ⟨⟨h15, hsi, hm⟩, k⟩ => ⟨h15, hsi, hm, k⟩

/-- A conditional halving of `aE`, in place; `rbx` and `r12` kept. -/
theorem halfCond_ok {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64} {c : Nat} (hg : Good s B Z w mi)
    (hd : MrDims B Z w) (hL : word s.mem B (slot w aE + 8 * w) = BitVec.twoPow 64 (mrA c % 64))
    (hbx : s.gpr .rbx = off B (slot w aE)) (h12 : s.gpr .r12 = BitVec.ofNat 64 w) {j : Nat} (hj : 1 ≤ j ∧ j ≤ 3) :
    WP isa (seqs (halfCond j)) s fun t =>
      wv t.mem B (slot w aE) w = (if j < mrSig c then wv s.mem B (slot w aE) w / 2 else wv s.mem B (slot w aE) w) ∧
      Outside B (slot w aE) (8 * w) s.mem t.mem ∧ Keep [.rax, .rbp, .rcx, .rdx, .r14, .rsi, .r15] s t := by
  have hEZ := aE_fits hd
  have hw' : w < 2 ^ 31 := by have := hd.w128; omega_arith
  rw [show seqs (halfCond j) = .seq (.block [.mov .rsi (.reg .rbx), .movImm64 .r15 (sigK j),
      .alu .and .r15 (.mem (ix .rbx .r12)), .alu .cmp .r15 (.imm 1), .alu .sbb .r15 (.reg .r15),
      .alu .xor .r15 (.imm (BitVec.ofInt 32 (-1)))]) (seqs halfPass) from rfl]
  refine WP.seq (WP.mono (sigMask_ok hg hd hL hbx h12 hj) fun s₁ ⟨h15, hsi, hm₁, k₁⟩ => ?_)
  refine WP.mono (halfPass_ok (hg.scr.congr k₁.2.2) hsi ((k₁.gpr (by decide)).trans hbx) h15
    ((k₁.gpr (by decide)).trans h12) (by have := hd.w4; omega_arith) hw' (by omega_arith) (by omega_arith) (Or.inl rfl))
    fun t ⟨hv, ho, k⟩ => ⟨?_, by rw [← hm₁]; exact ho, (k₁.trans k).mono (by decide)⟩
  rw [hv, hm₁]
  simp only [decide_eq_true_eq]

/-- `expSetup`: `E` in `aE`, and the bit after it (`ECtx`). -/
theorem expSetup_ok {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64} {c : Nat} (hg : Good s B Z w mi)
    (hd : MrDims B Z w) (hn : wv s.mem B (slot w aN) w = c) (hodd : c % 2 = 1) (hc1 : 1 < c) :
    WP isa (seqs expSetup) s fun t => ECtx t.mem B w c ∧ Frm B [(slot w aE, 8 * (w + 1))] s.mem t.mem ∧
      Good t B Z w mi ∧ Keep mmRegs s t := by
  have hnw := hg.scr.nowrap
  have hZ := hd.z
  have hw4 := hd.w4
  have hw' : w < 2 ^ 31 := by have := hd.w128; omega_arith
  have hEZ := aE_fits hd
  have hN8 := slot_le (w := w) (show aN < 8 by decide)
  have h8E : slot w 8 ≤ slot w aE := by
    have e1 : slot w 8 = 256 + 8 * (8 * (w + 2)) := rfl
    have e2 : slot w aE = 256 + 24 * (8 * (w + 2)) := rfl
    omega_arith
  have hEh : 128 ≤ slot w aE := by have := hdr_lt_slot w aE (show 31 < 32 by decide); omega_arith
  obtain ⟨hN, hm2⟩ := splitTwos_spec (c - 1) (by omega_arith)
  change c - 1 = (Spec.Rsa.splitTwos (c - 1)).2 * 2 ^ mrA c at hN
  obtain ⟨-, hx1, hx0⟩ := lowWord_bits hN hm2
  rw [expSetup_eq]
  refine wp_seqs_append (by simp [lowWord]) (by simp) (WP.mono (lowWord_ok hg hZ (by omega_arith) hw' hn hodd hc1)
    fun s₁ ⟨hbp, hm₁, k₁⟩ => ?_)
  have hg₁ : Good s₁ B Z w mi := ⟨hg.scr.congr k₁.2.2, (k₁.gpr (by decide)).trans hg.rdi, by rw [hm₁]; exact hg.hdr⟩
  refine wp_seqs_append (by simp) (by simp [halfPass]) (WP.mono (lowBit_ok (c := c) hg₁ hd rfl (by rw [hbp]; exact hx1)
    (fun j hj => by rw [hbp]; exact hx0 j hj)) fun s₂ ⟨hm₂, hsi, hbx, h12, h15, k₂⟩ => ?_)
  rw [hm₁] at hm₂
  have hf₂ : Frm B [(slot w aE, 8 * (w + 1))] s.mem s₂.mem := by
    rw [hm₂]; exact Frm.of_outside ((writeW_outside _ B _ (by omega_arith)).mono (o' := slot w aE) (n' := 8 * (w + 1))
      (by omega_arith) (by omega_arith)) (by simp)
  have hg₂ : Good s₂ B Z w mi := ⟨hg₁.scr.congr k₂.2.2, (k₂.gpr (by decide)).trans hg₁.rdi,
    Hdr.of_frm hg.hdr hf₂ (by simp; omega_arith)⟩
  have hL₂ : word s₂.mem B (slot w aE + 8 * w) = BitVec.twoPow 64 (mrA c % 64) := by rw [hm₂, word_writeW_self]
  have hN₂ : wv s₂.mem B (slot w aN) w = c := by
    rw [hf₂.wv_eq (fun r hr => by simp at hr; subst hr; left; simp only; omega_arith) (by omega_arith)]; exact hn
  -- `E := c / 2`.
  refine wp_seqs_append (by simp [halfPass]) (by simp [halfCond]) (WP.mono (halfPass_ok hg₂.scr hsi hbx h15 h12
    (by omega_arith) hw' (by omega_arith) (by omega_arith) (Or.inr (Or.inr (by omega_arith)))) fun s₃ ⟨hv₃, ho₃, k₃⟩ => ?_)
  rw [hN₂] at hv₃
  simp only [↓reduceIte] at hv₃
  have hf₃ : Frm B [(slot w aE, 8 * (w + 1))] s₂.mem s₃.mem :=
    Frm.of_outside (ho₃.mono (o' := slot w aE) (n' := 8 * (w + 1)) (by omega_arith) (by omega_arith)) (by simp)
  have hg₃ : Good s₃ B Z w mi := ⟨hg₂.scr.congr k₃.2.2, (k₃.gpr (by decide)).trans hg₂.rdi,
    Hdr.of_frm hg₂.hdr hf₃ (by simp; omega_arith)⟩
  have hL₃ : word s₃.mem B (slot w aE + 8 * w) = BitVec.twoPow 64 (mrA c % 64) := by
    rw [ho₃.word (Or.inr (by omega_arith)) (by omega_arith)]; exact hL₂
  have hbx₃ : s₃.gpr .rbx = off B (slot w aE) := (k₃.gpr (by decide)).trans hbx
  have h12₃ : s₃.gpr .r12 = BitVec.ofNat 64 w := (k₃.gpr (by decide)).trans h12
  -- The three conditional halvings.
  refine wp_seqs_append (by simp [halfCond]) (by simp [halfCond]) (WP.mono (halfCond_ok hg₃ hd hL₃ hbx₃ h12₃
    (j := 1) (by decide)) fun s₄ ⟨hv₄, ho₄, k₄⟩ => ?_)
  have hf₄ : Frm B [(slot w aE, 8 * (w + 1))] s₃.mem s₄.mem :=
    Frm.of_outside (ho₄.mono (o' := slot w aE) (n' := 8 * (w + 1)) (by omega_arith) (by omega_arith)) (by simp)
  have hg₄ : Good s₄ B Z w mi := ⟨hg₃.scr.congr k₄.2.2, (k₄.gpr (by decide)).trans hg₃.rdi,
    Hdr.of_frm hg₃.hdr hf₄ (by simp; omega_arith)⟩
  have hL₄ : word s₄.mem B (slot w aE + 8 * w) = BitVec.twoPow 64 (mrA c % 64) := by
    rw [ho₄.word (Or.inr (by omega_arith)) (by omega_arith)]; exact hL₃
  refine wp_seqs_append (by simp [halfCond]) (by simp [halfCond]) (WP.mono (halfCond_ok hg₄ hd hL₄
    ((k₄.gpr (by decide)).trans hbx₃) ((k₄.gpr (by decide)).trans h12₃) (j := 2) (by decide))
    fun s₅ ⟨hv₅, ho₅, k₅⟩ => ?_)
  have hf₅ : Frm B [(slot w aE, 8 * (w + 1))] s₄.mem s₅.mem :=
    Frm.of_outside (ho₅.mono (o' := slot w aE) (n' := 8 * (w + 1)) (by omega_arith) (by omega_arith)) (by simp)
  have hg₅ : Good s₅ B Z w mi := ⟨hg₄.scr.congr k₅.2.2, (k₅.gpr (by decide)).trans hg₄.rdi,
    Hdr.of_frm hg₄.hdr hf₅ (by simp; omega_arith)⟩
  have hL₅ : word s₅.mem B (slot w aE + 8 * w) = BitVec.twoPow 64 (mrA c % 64) := by
    rw [ho₅.word (Or.inr (by omega_arith)) (by omega_arith)]; exact hL₄
  refine WP.mono (halfCond_ok hg₅ hd hL₅ ((k₅.gpr (by decide)).trans ((k₄.gpr (by decide)).trans hbx₃))
    ((k₅.gpr (by decide)).trans ((k₄.gpr (by decide)).trans h12₃)) (j := 3) (by decide)) fun t ⟨hv, ho, k⟩ => ?_
  have hft : Frm B [(slot w aE, 8 * (w + 1))] s₅.mem t.mem :=
    Frm.of_outside (ho.mono (o' := slot w aE) (n' := 8 * (w + 1)) (by omega_arith) (by omega_arith)) (by simp)
  have hf : Frm B [(slot w aE, 8 * (w + 1))] s.mem t.mem :=
    (((hf₂.trans hf₃).trans hf₄).trans hf₅).trans hft
  refine ⟨⟨?_, by rw [ho.word (Or.inr (by omega_arith)) (by omega_arith)]; exact hL₅⟩, hf,
    ⟨hg₅.scr.congr k.2.2, (k.gpr (by decide)).trans hg₅.rdi, Hdr.of_frm hg.hdr hf (by simp; omega_arith)⟩,
    ((((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).trans k).mono (by decide))⟩
  rw [hv, hv₅, hv₄, hv₃, ← mrE_halves hodd]

end VG.Proof.RsaKeyGen.X86_64
