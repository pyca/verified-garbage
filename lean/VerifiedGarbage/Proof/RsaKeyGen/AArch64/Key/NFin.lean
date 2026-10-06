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
def finE2 : List Instr := [ldh .x3 kEv, movi .x4 3, .subs .x .x3 .x3 .x4] ++ carryMask ++ finAnd
def finE3 : List Instr :=
  [ldh .x3 kEv, .lsr .x .x3 .x3 33, movi .x4 1, .subs .x .x3 .x3 .x4] ++ borrowMask ++ [.logic .and .x .x10 .x10 .x15,
    sth .x10 kOk]

theorem finalMask_eq : finalMask = ws ++ (base aQt .x16 ++ (finTop ++ (oddMaskOf aPa ++ (finAnd ++ (oddMaskOf aQa ++
    (finAnd ++ (finE1 ++ (finE2 ++ finE3)))))))) := by
  simp only [finalMask, finTop, finAnd, finE1, finE2, finE3, List.append_assoc, List.cons_append, List.nil_append]

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
  -- `e` valid, and the store.
  refine WP.mono (WP.keep [.x3, .x4, .x10, .x15] (Q := fun t => t.mem = s₅.mem.writeW (off I.B (8 * kOk))
    (mask (finalOk I.W n P Q e ok))) (by
      brun [h0₅, hdr_enc (show kOk < 32 by decide), hdr_enc (show kEv < 32 by decide),
        hs₅.ld (d := 8 * kEv) (by unfold kEv sFn; omega), hs₅.st (d := 8 * kOk) (by unfold kOk sFn; omega),
        hev₅, h15₅, h10₅, h7₅, carryMask, borrowMask, oddMask, mask_and', mask_low])
      (by decide) (by decide) (by decide +kernel)) fun t ⟨mt, kt⟩ => ?_
  obtain ⟨ht, ft, okt⟩ := h₅.hdrW (i := kOk) (by unfold kOk sFn; omega) mt kt
  exact ⟨ht, by rw [← hm₅]; exact ft, okt⟩

end VG.Proof.RsaKeyGen.AArch64.Key
