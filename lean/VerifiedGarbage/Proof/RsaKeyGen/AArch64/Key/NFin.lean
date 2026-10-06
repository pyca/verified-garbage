import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.Shared
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.LoadC

/-!
# An RSA key from its primes on AArch64: `n` and the final mask

`n = p q` (`nPart_k`), and `kOk &= ` the masks of `n`'s top bit, `p` and
`q` odd, and `e` valid, and'ed in `x10` (`finalMask_k`).
-/

namespace VG.Proof.RsaKeyGen.AArch64.Key

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Key
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.RsaKeyGen.AArch64.Candidate (loadE kE kElen)

/-- `nPart`: `[aQt] := [aPa] [aQa]`, `w` words each, for `W = 2 w`. -/
theorem nPart_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) {w : Nat} (hW : I.W = 2 * w)
    {a b : Nat} (ha : av I s.mem aPa = a) (hb : av I s.mem aQa = b) (ha' : a < 2 ^ (64 * w))
    (hb' : b < 2 ^ (64 * w)) :
    WP isa (seqs nPart) s fun t => KS I s₀ t ∧ KF I.B I.W [.arr aQt] s.mem t.mem ∧
      wv t.mem I.B (slot I.W aQt) (I.W + 2) = a * b :=
  mulTo_k h hW (o := aQt) (a := aPa) (b := aQa) (by decide) (by decide) (by decide) (by decide) (by decide)
    ha hb ha' hb'

/-! ## The final mask -/

/-- The top bit of a `W`-word number: of its word `W − 1`. -/
theorem top_bit_k {m : Mem} {B : Addr} {d W : Nat} (hW : 1 ≤ W) :
    (word m B (d + 8 * (W - 1))).toNat / 2 ^ 63 = if 2 ^ (64 * W - 1) ≤ wv m B d W then 1 else 0 := by
  have e : wv m B d W = wv m B d (W - 1) + 2 ^ (64 * (W - 1)) * (word m B (d + 8 * (W - 1))).toNat := by
    rw [show W = W - 1 + 1 from by omega, wv]; simp
  have ha := wv_lt m B d (W - 1)
  have ht := (word m B (d + 8 * (W - 1))).isLt
  generalize wv m B d (W - 1) = a at e ha
  generalize (word m B (d + 8 * (W - 1))).toNat = t at e ht
  have hp : 2 ^ (64 * W - 1) = 2 ^ (64 * (W - 1)) * 2 ^ 63 := by rw [← Nat.pow_add]; congr 1; omega
  generalize 2 ^ (64 * (W - 1)) = R at e ha hp
  rw [e, hp]
  by_cases h63 : 2 ^ 63 ≤ t
  · have : R * 2 ^ 63 ≤ R * t := Nat.mul_le_mul_left _ h63
    rw [ite_eq_left (show R * 2 ^ 63 ≤ a + R * t by omega)]; omega
  · have : R * t + R ≤ R * 2 ^ 63 := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega)
    rw [ite_eq_right (show ¬ R * 2 ^ 63 ≤ a + R * t by omega)]; omega

/-- The mask of a word's top bit. -/
theorem shr63_mask_k (x : BitVec 64) :
    BitVec.setWidth 64 (0#16) - x >>> 63 = mask (decide (x.toNat / 2 ^ 63 = 1)) := by
  have h : x >>> 63 = BitVec.ofNat 64 (x.toNat / 2 ^ 63) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    have := x.isLt; omega
  rw [h]
  have := x.isLt
  rcases (show x.toNat / 2 ^ 63 = 0 ∨ x.toNat / 2 ^ 63 = 1 by omega) with e | e <;> rw [e] <;> decide

theorem ite_mask_k (c : Bool) : (if c = true then mask true else mask false) = mask c := by cases c <;> rfl

theorem ite_mask_not_k (c : Bool) : (if (!c) = true then mask false else mask true) = mask c := by cases c <;> rfl

/-- The mask `finalMask` leaves in `kOk`. -/
abbrev finalOk (W n P Q e : Nat) (ok : Bool) : Bool :=
  decide (2 ^ (64 * W - 1) ≤ n) && ok && decide (P % 2 = 1) && decide (Q % 2 = 1) && Spec.Rsa.exponentValid e

/-- `finalMask`'s pieces: the top bit and `ok`, an `and` of `x15`, and the
three tests of `e`. -/
def finTop : List Instr :=
  [.lsl .x .x3 .x12 3, .add .x .x16 .x16 .x3, .subImm .x .x16 .x16 8, ld .x3 .x16, .lsr .x .x3 .x3 63, movi .x7 0,
    .sub .x .x10 .x7 .x3, ldh .x3 kOk, .logic .and .x .x10 .x10 .x3]
def finAnd : List Instr := [.logic .and .x .x10 .x10 .x15]
def finE1 : List Instr := [ldh .x3 kEv] ++ oddMask ++ finAnd
def finE2 : List Instr := [ldh .x3 kEv, movi .x4 3, .subs .x .x3 .x3 .x4]
def finE3 : List Instr := [ldh .x3 kEv, .lsr .x .x3 .x3 33, movi .x4 1, .subs .x .x3 .x3 .x4]
def finSt : List Instr := [.logic .and .x .x10 .x10 .x15, sth .x10 kOk]

theorem finalMask_eq : finalMask = ws ++ (base aQt .x16 ++ (finTop ++ (oddMaskOf aPa ++ (finAnd ++ (oddMaskOf aQa ++
    (finAnd ++ (finE1 ++ (finE2 ++ ((carryMask ++ finAnd) ++ (finE3 ++ (borrowMask ++ finSt))))))))))) := by
  simp only [finalMask, finTop, finAnd, finE1, finE2, finE3, finSt, List.append_assoc, List.cons_append,
    List.nil_append]

/-- `finalMask`, for `[aQt] = n`, `[aPa] = P`, `[aQa] = Q` and `kOk` the
mask of `ok`. -/
theorem finalMask_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) {n P Q e : Nat} {ok : Bool}
    (hn : av I s.mem aQt = n) (hP : av I s.mem aPa = P) (hQ : av I s.mem aQa = Q) (he64 : e < 2 ^ 64)
    (hev : word s.mem I.B (8 * kEv) = BitVec.ofNat 64 e) (hok : word s.mem I.B (8 * kOk) = mask ok) :
    WP isa (.block finalMask) s fun t => KS I s₀ t ∧ KF I.B I.W [.hdr kOk] s.mem t.mem ∧
      word t.mem I.B (8 * kOk) = mask (finalOk I.W n P Q e ok) := by
  have hnw := h.ws.scr.nowrap
  have hw1 : 1 ≤ I.W := by have := h.ws.w1; omega
  have hw2 := h.ws.w2
  have sN := h.ws.sl (j := aQt) (by decide)
  have h256 := h.ws.h256
  rw [finalMask_eq, ← List.append_assoc, WP.block_append_iff]
  refine WP.mono (wsBase16_ok h aQt) fun s₁ ⟨⟨h16, h12, _, m₁⟩, k₁⟩ => WP.block_append_iff.mpr ?_
  have hs₁ := h.ws.scr.congr k₁.wr
  have h0₁ : s₁.gpr .x0 = I.B := (k₁.gpr .x0 (by decide)).trans h.ws.x0
  have htop : (word s.mem I.B (slot I.W aQt + 8 * (I.W - 1))).toNat / 2 ^ 63 = 1 ↔ 2 ^ (64 * I.W - 1) ≤ n := by
    rw [top_bit_k hw1, show wv s.mem I.B (slot I.W aQt) I.W = n from hn]; split <;> simp_all
  have hok' : s.mem.readW (off I.B (8 * kOk)) 64 = mask ok := hok
  -- `x10 := ` the masks of the top bit and `ok`.
  refine WP.mono (WP.keep [.x3, .x7, .x10, .x16] (Q := fun t =>
      t.gpr .x10 = mask (decide (2 ^ (64 * I.W - 1) ≤ n) && ok) ∧ t.mem = s.mem) (by
    brun [finTop, h16, h12, h0₁, m₁, top_addr I.B (d := slot I.W aQt) (w := I.W) hw1 (by omega),
      hs₁.ld (d := slot I.W aQt + 8 * (I.W - 1)) (by omega), hdr_enc (show kOk < 32 by decide),
      hs₁.ld (d := 8 * kOk) (by unfold kOk sFn; omega), shr63_mask_k, hok', mask_and', decide_eq_decide.mpr htop])
    (by decide) (by decide) (by decide +kernel)) fun s₂ ⟨⟨h10₂, m₂⟩, k₂⟩ => WP.block_append_iff.mpr ?_
  have h₂ := h.regs m₂ (k₁.trans k₂)
  -- `p` odd.
  refine WP.mono (oddMaskOf_k h₂ (j := aPa) (by decide)) fun s₃ ⟨h₃, m₃, h15₃, _, _, _, k₃⟩ =>
    WP.block_append_iff.mpr ?_
  rw [m₂, hP] at h15₃
  have h10₃ : s₃.gpr .x10 = mask (decide (2 ^ (64 * I.W - 1) ≤ n) && ok) := by rw [k₃.gpr .x10 (by decide), h10₂]
  refine WP.mono (WP.keep [.x10] (Q := fun t => t.gpr .x10 = mask (decide (2 ^ (64 * I.W - 1) ≤ n) && ok &&
    decide (P % 2 = 1)) ∧ t.mem = s₃.mem) (by brun [finAnd, h15₃, h10₃, mask_and']) (by decide) (by decide)
      (by decide +kernel)) fun s₄ ⟨⟨h10₄, m₄⟩, k₄⟩ => WP.block_append_iff.mpr ?_
  have h₄ := h₃.regs m₄ k₄
  -- `q` odd.
  refine WP.mono (oddMaskOf_k h₄ (j := aQa) (by decide)) fun s₅ ⟨h₅, m₅, h15₅, h7₅, _, _, k₅⟩ => ?_
  rw [m₄, m₃, m₂, hQ] at h15₅
  have h10₅ : s₅.gpr .x10 = mask (decide (2 ^ (64 * I.W - 1) ≤ n) && ok && decide (P % 2 = 1)) := by
    rw [k₅.gpr .x10 (by decide), h10₄]
  have hm₅ : s₅.mem = s.mem := by rw [m₅, m₄, m₃, m₂]
  have hs₅ := h₅.ws.scr
  have h0₅ : s₅.gpr .x0 = I.B := h₅.x0
  have hev₅ : s₅.mem.readW (off I.B (8 * kEv)) 64 = BitVec.ofNat 64 e := by rw [hm₅]; exact hev
  have hte : (BitVec.ofNat 64 e).toNat = e := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt he64]
  -- `q` odd.
  refine WP.block_append_iff.mpr (WP.mono (WP.keep [.x10] (Q := fun t => t.gpr .x10 =
      mask (decide (2 ^ (64 * I.W - 1) ≤ n) && ok && decide (P % 2 = 1) && decide (Q % 2 = 1)) ∧ t.mem = s₅.mem) (by
    brun [finAnd, h15₅, h10₅, mask_and']) (by decide) (by decide) (by decide +kernel))
    fun s₆ ⟨⟨h10₆, m₆⟩, k₆⟩ => WP.block_append_iff.mpr ?_)
  have hev₆ : s₆.mem.readW (off I.B (8 * kEv)) 64 = BitVec.ofNat 64 e := by rw [m₆]; exact hev₅
  have h0₆ : s₆.gpr .x0 = I.B := (k₆.gpr .x0 (by decide)).trans h0₅
  have h7₆ : s₆.gpr .x7 = 0 := (k₆.gpr .x7 (by decide)).trans h7₅
  have hs₆ := hs₅.congr k₆.wr
  -- `e` odd.
  refine WP.mono (WP.keep [.x3, .x4, .x10, .x15] (Q := fun t => t.gpr .x10 =
      mask (decide (2 ^ (64 * I.W - 1) ≤ n) && ok && decide (P % 2 = 1) && decide (Q % 2 = 1) &&
        decide (e % 2 = 1)) ∧ t.mem = s₆.mem ∧ t.gpr .x7 = 0) (by
    brun [finE1, oddMask, finAnd, h0₆, h7₆, hdr_enc (show kEv < 32 by decide),
      hs₆.ld (d := 8 * kEv) (by unfold kEv sFn; omega), hev₆, h10₆, mask_low, mask_low', hte, mask_and'])
    (by decide) (by decide) (by decide +kernel)) fun s₇ ⟨⟨h10₇, m₇, h7₇⟩, k₇⟩ => WP.block_append_iff.mpr ?_
  have hev₇ : s₇.mem.readW (off I.B (8 * kEv)) 64 = BitVec.ofNat 64 e := by rw [m₇]; exact hev₆
  have h0₇ : s₇.gpr .x0 = I.B := (k₇.gpr .x0 (by decide)).trans h0₆
  have hs₇ := hs₆.congr k₇.wr
  -- `e ≥ 3`: the carry, its mask, and'ed.
  refine WP.mono (WP.keep [.x3, .x4] (Q := fun t => t.c = decide (3 ≤ e) ∧ t.mem = s₇.mem) (by
    brun [finE2, h0₇, hdr_enc (show kEv < 32 by decide), hs₇.ld (d := 8 * kEv) (by unfold kEv sFn; omega), hev₇]
    rw [BitVec.toNat_not, show (BitVec.setWidth 64 3#16 : BitVec 64).toNat = 3 from rfl, Bool.toNat_true, hte]
    exact decide_eq_decide.mpr (by omega))
    (by decide) (by decide) (by decide +kernel)) fun s₈ ⟨⟨c₈, m₈⟩, k₈⟩ => WP.block_append_iff.mpr ?_
  have h10₈ := (k₈.gpr .x10 (by decide)).trans h10₇
  have h7₈ := (k₈.gpr .x7 (by decide)).trans h7₇
  refine WP.mono (WP.keep [.x4, .x10, .x15] (Q := fun t => t.gpr .x10 =
      mask (decide (2 ^ (64 * I.W - 1) ≤ n) && ok && decide (P % 2 = 1) && decide (Q % 2 = 1) &&
        decide (e % 2 = 1) && decide (3 ≤ e)) ∧ t.mem = s₈.mem) (by
    brun [carryMask, finAnd, h7₈, h10₈, c₈]
    rw [show (0 : BitVec 64) - 1#64 = mask true from rfl, show (0 : BitVec 64) = mask false from rfl, ite_mask_k,
      mask_and'])
    (by decide) (by decide) (by decide +kernel)) fun s₉ ⟨⟨h10₉, m₉⟩, k₉⟩ => WP.block_append_iff.mpr ?_
  have hev₉ : s₉.mem.readW (off I.B (8 * kEv)) 64 = BitVec.ofNat 64 e := by rw [m₉, m₈]; exact hev₇
  have h0₉ : s₉.gpr .x0 = I.B := ((k₈.trans k₉).gpr .x0 (by decide)).trans h0₇
  have hs₉ := hs₇.congr (k₈.trans k₉).wr
  -- `e < 2^33`: the borrow of `(e >> 33) − 1`.
  refine WP.mono (WP.keep [.x3, .x4] (Q := fun t => t.c = !decide (e < 2 ^ 33) ∧ t.mem = s₉.mem) (by
    brun [finE3, h0₉, hdr_enc (show kEv < 32 by decide), hs₉.ld (d := 8 * kEv) (by unfold kEv sFn; omega), hev₉]
    rw [BitVec.toNat_not, show (BitVec.setWidth 64 1#16 : BitVec 64).toNat = 1 from rfl, Bool.toNat_true,
      BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hte]
    rw [Bool.eq_iff_iff]
    simp only [decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]
    omega)
    (by decide) (by decide) (by decide +kernel)) fun s₁₀ ⟨⟨c₁₀, m₁₀⟩, k₁₀⟩ => ?_
  have h10₁₀ := (k₁₀.gpr .x10 (by decide)).trans h10₉
  have h7₁₀ := (((k₈.trans k₉).trans k₁₀).gpr .x7 (by decide)).trans h7₇
  have h0₁₀ : s₁₀.gpr .x0 = I.B := (k₁₀.gpr .x0 (by decide)).trans h0₉
  have hs₁₀ := hs₉.congr k₁₀.wr
  have hexp : (decide (e % 2 = 1) && decide (3 ≤ e) && decide (e < 2 ^ 33)) = Spec.Rsa.exponentValid e := by
    unfold Spec.Rsa.exponentValid
    rw [Bool.eq_iff_iff]
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  have hfin : (decide (2 ^ (64 * I.W - 1) ≤ n) && ok && decide (P % 2 = 1) && decide (Q % 2 = 1) &&
      decide (e % 2 = 1) && decide (3 ≤ e) && decide (e < 2 ^ 33)) = finalOk I.W n P Q e ok := by
    simp only [finalOk, ← hexp, Bool.and_assoc]
  refine WP.mono (WP.keep [.x4, .x10, .x15] (Q := fun t => t.mem = s₁₀.mem.writeW (off I.B (8 * kOk))
      (mask (finalOk I.W n P Q e ok))) (by
    brun [borrowMask, finSt, h7₁₀, h10₁₀, c₁₀, h0₁₀, hdr_enc (show kOk < 32 by decide),
      hs₁₀.st (d := 8 * kOk) (by unfold kOk sFn; omega)]
    rw [show (0 : BitVec 64) - 1#64 = mask true from rfl, show (0 : BitVec 64) = mask false from rfl, ite_mask_not_k,
      mask_and', hfin])
    (by decide) (by decide) (by decide +kernel)) fun t ⟨mt, kt⟩ => ?_
  have hm₁₀ : s₁₀.mem = s₅.mem := by rw [m₁₀, m₉, m₈, m₇, m₆]
  rw [hm₁₀] at mt
  obtain ⟨ht, ft, okt⟩ := h₅.hdrW (i := kOk) (by unfold kOk sFn; omega) mt
    (((((k₆.trans k₇).trans k₈).trans k₉).trans k₁₀).trans kt)
  exact ⟨ht, by rw [← hm₅]; exact ft, okt⟩

end VG.Proof.RsaKeyGen.AArch64.Key
