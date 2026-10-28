module

import VerifiedGarbage.Proof.Rsa.AArch64.KeyLoops
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
public meta import VerifiedGarbage.Impl.Ffdh.AArch64.Domain
public import VerifiedGarbage.Impl.Ffdh.AArch64.Domain
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Bignum.CrtRedc
import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks
import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
import VerifiedGarbage.Proof.Bignum.AArch64.Copy
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.AArch64.MulAdd

/-!
# FFDH on AArch64: comparisons of arrays

In a workspace (`Good`), each leaves 1 or 0 in `x9`: `ltArr` (`[a] < [b]`),
`geArr` (`[a] ≥ [b]`), `eqArr` (`[a] = [b]`), `ltP` (`[a] | 1 < m`, through
the temporary array) and `isOdd`; correctness (`…_ok`) and constant time
in runs on workspaces of the same layout (`…_ct`), whatever the numbers.
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Impl.Rsa.AArch64.Crt
open VG.Impl.Ffdh.AArch64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem or1_toNat (x : BitVec 64) : (x ||| 1).toNat = x.toNat + (1 - x.toNat % 2) := by
  rw [BitVec.toNat_or, show (1 : BitVec 64).toNat = 1 from rfl]
  have h1 : (x.toNat ||| 1) / 2 = x.toNat / 2 := by
    have := Nat.or_div_two_pow (a := x.toNat) (b := 1) (n := 1); simpa using this
  have h2 : (x.toNat ||| 1) % 2 = 1 := Nat.or_mod_two_eq_one.mpr (Or.inr rfl)
  omega_arith

/-- A workspace after a change of memory past its header. -/
theorem _root_.VG.Proof.Bignum.AArch64.Good.of_outside {s t : State} {G : Addr} {Zx w : Nat} {mi : BitVec 64}
    (hg : Good s G Zx w mi) {o n : Nat} (ho : 8 * 16 ≤ o) (hout : Outside G o n s.mem t.mem)
    (hwr : t.wr = s.wr) (h0 : t.gpr .x0 = s.gpr .x0) : Good t G Zx w mi := by
  have hn := hg.scr.nowrap
  have hh : ∀ i < 16, word t.mem G (8 * i) = word s.mem G (8 * i) := fun i hi =>
    hout.word (Or.inl (by omega_arith)) (by omega_arith)
  exact ⟨hg.scr.congr hwr, h0.trans hg.x0, ⟨(hh _ (by decide)).trans hg.hdr.hw, (hh _ (by decide)).trans hg.hdr.hminv,
    fun j hj => (hh _ (by unfold sArr; omega_arith)).trans (hg.hdr.harr j hj)⟩⟩

/-- The 0 or 1 of a proposition. -/
abbrev bit (p : Prop) [Decidable p] : BitVec 64 := if p then 1 else 0

/-! ## Comparisons -/

/-- `ptrs a b`, then `x7 := 0`, `x14 := w` and the carry set. -/
theorem cmpHead_ok {t : State} {G : Addr} {Zx w : Nat} {mi : BitVec 64} (hg : Good t G Zx w mi) (hZ : slot w 8 ≤ Zx)
    {a b : Nat} (ha : a < 8) (hb : b < 8) :
    WP isa (.block (ptrs a b ++ [movi .x7 0, mov .x14 .x12, .subs .x .x3 .x7 .x7])) t fun t' =>
      t'.gpr .x16 = off G (slot w a) ∧ t'.gpr .x17 = off G (slot w b) ∧ t'.gpr .x14 = BitVec.ofNat 64 w ∧
      t'.gpr .x12 = BitVec.ofNat 64 w ∧ t'.c = true ∧ t'.mem = t.mem ∧ Keep [.x3, .x7, .x12, .x14, .x16, .x17] t t' := by
  refine WP.mono (WP.keep [.x3, .x7, .x12, .x14, .x16, .x17] (Q := fun t' => t'.gpr .x16 = off G (slot w a) ∧
      t'.gpr .x17 = off G (slot w b) ∧ t'.gpr .x14 = BitVec.ofNat 64 w ∧ t'.gpr .x12 = BitVec.ofNat 64 w ∧
      t'.c = true ∧ t'.mem = t.mem)
    (by unfold ptrs; brun [hg.x0, hdr_enc (sArr_lt ha), hdr_enc (sArr_lt hb), hdr_enc (show sW < 32 by decide),
      hg.ld hZ (sArr_lt ha), hg.ld hZ (sArr_lt hb), hg.ld hZ (show sW < 32 by decide), hg.hdr.harr a ha,
      hg.hdr.harr b hb, hg.hdr.hw])
    rfl rfl rfl) fun t' ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
      h.2.2.2.2.2, k⟩

/-- `cmpArr a b`: the carry flag clear iff `[a] < [b]`. -/
theorem cmpArr_ok {t : State} {G : Addr} {Zx w : Nat} {mi : BitVec 64} (hg : Good t G Zx w mi) (hZ : slot w 8 ≤ Zx)
    (hw : 1 ≤ w) (hw' : w < 2 ^ 31) {a b : Nat} (ha : a < 8) (hb : b < 8) :
    WP isa (seqs (cmpArr a b)) t fun t' =>
      t'.c = !decide (wv t.mem G (slot w a) w < wv t.mem G (slot w b) w) ∧ t'.mem = t.mem ∧
      Keep [.x3, .x4, .x7, .x12, .x14, .x16, .x17] t t' := by
  have sa := Nat.le_trans (slot_le (w := w) ha) hZ
  have sb := Nat.le_trans (slot_le (w := w) hb) hZ
  unfold cmpArr
  simp only [seqs]
  refine WP.seq (WP.mono (cmpHead_ok hg hZ ha hb) fun t₁ ⟨h16, h17, h14, _, hc, hm₁, k₁⟩ => ?_)
  refine WP.mono (cmpLoop_ok (hg.scr.congr k₁.wr) h16 h17 h14 hc hw hw' (by omega_arith) (by omega_arith))
    fun t' ⟨hc', hm', k'⟩ => ⟨by rw [hc', hm₁], hm'.trans hm₁, (k₁.trans k').mono (by decide)⟩

theorem borrow1_ok (t : State) :
    WP isa (.block borrow1) t fun t' => (t'.gpr .x9 = (if t.c then 0 else 1) ∧ t'.mem = t.mem ∧ t'.c = t.c) ∧
      Keep [.x7, .x8, .x9] t t' :=
  WP.keep [.x7, .x8, .x9] (c := .block borrow1)
    (Q := fun t' => t'.gpr .x9 = (if t.c then 0 else 1) ∧ t'.mem = t.mem ∧ t'.c = t.c)
    (by unfold borrow1; brun; cases t.c <;> simp) (by decide) (by decide) (by decide +kernel)

theorem carry1_ok (t : State) :
    WP isa (.block carry1) t fun t' => (t'.gpr .x9 = (if t.c then 1 else 0) ∧ t'.mem = t.mem ∧ t'.c = t.c) ∧
      Keep [.x7, .x8, .x9] t t' :=
  WP.keep [.x7, .x8, .x9] (c := .block carry1)
    (Q := fun t' => t'.gpr .x9 = (if t.c then 1 else 0) ∧ t'.mem = t.mem ∧ t'.c = t.c)
    (by unfold carry1; brun; cases t.c <;> simp) (by decide) (by decide) (by decide +kernel)

/-- `ltArr a b`: `x9 := [a] < [b]`. -/
theorem ltArr_ok {t : State} {G : Addr} {Zx w : Nat} {mi : BitVec 64} (hg : Good t G Zx w mi) (hZ : slot w 8 ≤ Zx)
    (hw : 1 ≤ w) (hw' : w < 2 ^ 31) {a b : Nat} (ha : a < 8) (hb : b < 8) :
    WP isa (seqs (ltArr a b)) t fun t' =>
      t'.gpr .x9 = bit (wv t.mem G (slot w a) w < wv t.mem G (slot w b) w) ∧ t'.mem = t.mem ∧
      Keep mmRegs t t' := by
  unfold ltArr
  refine wp_seqs_append (by simp [cmpArr]) (by simp) (WP.mono (cmpArr_ok hg hZ hw hw' ha hb) fun t₁ ⟨hc, hm, k₁⟩ => ?_)
  refine WP.mono (borrow1_ok t₁) fun t' ⟨⟨h9, hm', _⟩, k'⟩ => ⟨?_, hm'.trans hm, (k₁.trans k').mono (by decide)⟩
  rw [h9, hc]
  by_cases h : wv t.mem G (slot w a) w < wv t.mem G (slot w b) w <;> simp [h]

/-- `geArr a b`: `x9 := [a] ≥ [b]`. -/
theorem geArr_ok {t : State} {G : Addr} {Zx w : Nat} {mi : BitVec 64} (hg : Good t G Zx w mi) (hZ : slot w 8 ≤ Zx)
    (hw : 1 ≤ w) (hw' : w < 2 ^ 31) {a b : Nat} (ha : a < 8) (hb : b < 8) :
    WP isa (seqs (geArr a b)) t fun t' =>
      t'.gpr .x9 = bit (¬ wv t.mem G (slot w a) w < wv t.mem G (slot w b) w) ∧ t'.mem = t.mem ∧
      Keep mmRegs t t' := by
  unfold geArr
  refine wp_seqs_append (by simp [cmpArr]) (by simp) (WP.mono (cmpArr_ok hg hZ hw hw' ha hb) fun t₁ ⟨hc, hm, k₁⟩ => ?_)
  refine WP.mono (carry1_ok t₁) fun t' ⟨⟨h9, hm', _⟩, k'⟩ => ⟨?_, hm'.trans hm, (k₁.trans k').mono (by decide)⟩
  rw [h9, hc]
  by_cases h : wv t.mem G (slot w a) w < wv t.mem G (slot w b) w <;> simp [h]

/-- `eqArr a b`: `x9 := [a] = [b]`. -/
theorem eqArr_ok {t : State} {G : Addr} {Zx w : Nat} {mi : BitVec 64} (hg : Good t G Zx w mi) (hZ : slot w 8 ≤ Zx)
    (hw : 1 ≤ w) (hw' : w < 2 ^ 31) {a b : Nat} (ha : a < 8) (hb : b < 8) :
    WP isa (seqs (eqArr a b)) t fun t' =>
      t'.gpr .x9 = bit (wv t.mem G (slot w a) w = wv t.mem G (slot w b) w) ∧ t'.mem = t.mem ∧
      Keep mmRegs t t' := by
  have sa := Nat.le_trans (slot_le (w := w) ha) hZ
  have sb := Nat.le_trans (slot_le (w := w) hb) hZ
  unfold eqArr
  simp only [seqs]
  refine WP.seq (WP.mono (WP.keep [.x9, .x12, .x14, .x16, .x17] (Q := fun t' => t'.gpr .x16 = off G (slot w a) ∧
      t'.gpr .x17 = off G (slot w b) ∧ t'.gpr .x14 = BitVec.ofNat 64 w ∧ t'.gpr .x9 = 0 ∧ t'.mem = t.mem)
    (by unfold ptrs; brun [hg.x0, hdr_enc (sArr_lt ha), hdr_enc (sArr_lt hb), hdr_enc (show sW < 32 by decide),
      hg.ld hZ (sArr_lt ha), hg.ld hZ (sArr_lt hb), hg.ld hZ (show sW < 32 by decide), hg.hdr.harr a ha,
      hg.hdr.harr b hb, hg.hdr.hw])
    rfl rfl rfl) fun t₁ ⟨⟨h16, h17, h14, h9, hm₁⟩, k₁⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Rsa.AArch64.xor_ok (hg.scr.congr k₁.wr) h16 h17 h14 hw hw' (by omega_arith) (by omega_arith))
    fun t₂ ⟨hv, hm₂, _, k₂⟩ => ?_)
  rw [h9, hm₁] at hv
  refine WP.mono (WP.keep [.x3, .x7, .x8, .x9] (Q := fun t' =>
      t'.gpr .x9 = (if t₂.gpr .x9 = 0 then 1 else 0) ∧ t'.mem = t₂.mem)
    (by brun [VG.Proof.Bignum.AArch64.subs_one_c]; by_cases h : t₂.gpr .x9 = 0 <;> simp [h])
    (by decide) (by decide) (by decide +kernel)) fun t' ⟨⟨h9', hm'⟩, k'⟩ =>
      ⟨?_, by rw [hm', hm₂, hm₁], ((k₁.trans k₂).trans k').mono (by decide)⟩
  rw [h9']
  by_cases h : wv t.mem G (slot w a) w = wv t.mem G (slot w b) w
  · simp only [bit, h, hv.mpr ⟨rfl, h⟩, ↓reduceIte]
  · have : t₂.gpr .x9 ≠ 0 := fun h0 => h (hv.mp h0).2
    simp only [bit, h, this, ↓reduceIte]

/-- `ltP a` (`a ≠ aTmp`): `x9 := 2 ⌊[a] / 2⌋ + 1 < m`; only the temporary array
changes. -/
theorem ltP_ok {t : State} {G : Addr} {Zx w : Nat} {mi : BitVec 64} (hg : Good t G Zx w mi) (hZ : slot w 8 ≤ Zx)
    (hw : 1 ≤ w) (hw' : w < 2 ^ 31) {a : Nat} (ha : a < 8) (haT : a ≠ aTmp) :
    WP isa (seqs (ltP a)) t fun t' =>
      t'.gpr .x9 = bit (2 * (wv t.mem G (slot w a) w / 2) + 1 < wv t.mem G (slot w aN) w) ∧
      Outside G (slot w aTmp) (8 * w) t.mem t'.mem ∧ Keep mmRegs t t' := by
  have hn := hg.scr.nowrap
  have sT := Nat.le_trans (slot_le (w := w) (show aTmp < 8 by decide)) hZ
  have sN := slot_sep (w := w) (show aN ≠ aTmp by decide)
  have sa := slot_sep (w := w) haT
  have sa8 := Nat.le_trans (slot_le (w := w) ha) hZ
  unfold ltP
  rw [List.append_assoc]
  refine wp_seqs_append (by simp [copyArr]) (by simp) (WP.mono (copyArr_ok hg hZ hw hw' (show aTmp < 8 by decide) ha
    (Ne.symm haT)) fun t₁ ⟨hv₁, ho₁, k₁⟩ => ?_)
  have hT0 := hdr_lt_slot w aTmp (show 31 < 32 by decide)
  have hg₁ : Good t₁ G Zx w mi := hg.of_outside (by omega_arith) ho₁ k₁.wr (k₁.gpr .x0 (by decide))
  simp only [List.cons_append, List.nil_append, seqs]
  refine WP.seq (WP.mono (WP.keep [.x16] (Q := fun t' => t'.gpr .x16 = off G (slot w aTmp) ∧ t'.mem = t₁.mem)
    (by brun [hg₁.x0, hdr_enc (sArr_lt (show aTmp < 8 by decide)), hg₁.ld hZ (sArr_lt (show aTmp < 8 by decide)),
      hg₁.hdr.harr aTmp (by decide)]) (by decide) (by decide) (by decide +kernel)) fun t₂ ⟨⟨h16, hm₂⟩, k₂⟩ => ?_)
  have hs₂ := hg.scr.congr (k₁.trans k₂).wr
  refine WP.seq (WP.mono (WP.keep [.x3, .x4] (Q := fun t' => t'.mem = t₂.mem.writeW (off G (slot w aTmp))
      (word t₂.mem G (slot w aTmp) ||| 1))
    (by brun [h16, hs₂.ld (show slot w aTmp + 8 ≤ Zx by omega_arith), hs₂.st (show slot w aTmp + 8 ≤ Zx by omega_arith)]; rfl)
    (by decide) (by decide) (by decide +kernel)) fun t₃ ⟨hm₃, k₃⟩ => ?_)
  have o₃ := writeW_outside t₂.mem G (d := slot w aTmp) (word t₂.mem G (slot w aTmp) ||| 1) (by omega_arith)
  rw [← hm₃] at o₃
  have K := (k₁.trans k₂).trans k₃
  have hg₃ : Good t₃ G Zx w mi := hg₁.of_outside (o := slot w aTmp) (n := 8) (by omega_arith)
    (by rw [hm₂] at o₃; exact o₃) (by rw [k₃.wr, k₂.wr]) (by rw [k₃.gpr .x0 (by decide), k₂.gpr .x0 (by decide)])
  refine WP.mono (ltArr_ok hg₃ hZ hw hw' (show aTmp < 8 by decide) (show aN < 8 by decide)) fun t' ⟨h9, hm', k'⟩ => ?_
  -- The temporary array is `[a]` with its low bit set.
  have hT : wv t₃.mem G (slot w aTmp) w = 2 * (wv t.mem G (slot w a) w / 2) + 1 := by
    have e₁ := wv_split t₃.mem G (slot w aTmp) (n := 1) (k := w - 1) (show 1 + (w - 1) = w by omega_arith)
    have e₂ := wv_split t₁.mem G (slot w aTmp) (n := 1) (k := w - 1) (show 1 + (w - 1) = w by omega_arith)
    have hh : wv t₃.mem G (slot w aTmp + 8 * 1) (w - 1) = wv t₁.mem G (slot w aTmp + 8 * 1) (w - 1) := by
      rw [o₃.wv (Or.inr (by omega_arith)) (by omega_arith), hm₂]
    have hl₃ : wv t₃.mem G (slot w aTmp) 1 = (word t₁.mem G (slot w aTmp)).toNat + (1 - (word t₁.mem G (slot w aTmp)).toNat % 2) := by
      simp only [wv, Nat.zero_add, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.add_zero]
      rw [hm₃, word_writeW_self, hm₂, or1_toNat]
    have hl₁ : wv t₁.mem G (slot w aTmp) 1 = (word t₁.mem G (slot w aTmp)).toNat := by
      simp only [wv, Nat.zero_add, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.add_zero]
    rw [e₁, hh, hl₃, ← hv₁, e₂, hl₁]
    have h64 : 2 ^ (64 * 1) = 2 * 2 ^ 63 := by decide
    rw [h64, Nat.mul_assoc]
    generalize 2 ^ 63 * wv t₁.mem G (slot w aTmp + 8 * 1) (w - 1) = M
    generalize (word t₁.mem G (slot w aTmp)).toNat = x
    omega_arith
  have hN : wv t₃.mem G (slot w aN) w = wv t.mem G (slot w aN) w := by
    have sN8 := Nat.le_trans (slot_le (w := w) (show aN < 8 by decide)) hZ
    rw [o₃.wv (by omega_arith) (by omega_arith), hm₂, ho₁.wv (by omega_arith) (by omega_arith)]
  refine ⟨by rw [h9, hT, hN], ?_, (K.trans k').mono (by decide)⟩
  intro x hx
  rw [hm', o₃ x (by omega_arith), hm₂, ho₁ x hx]

/-- `isOdd a`: `x9 := [a] mod 2`. -/
theorem isOdd_ok {t : State} {G : Addr} {Zx w : Nat} {mi : BitVec 64} (hg : Good t G Zx w mi) (hZ : slot w 8 ≤ Zx)
    (hw : 1 ≤ w) {a : Nat} (ha : a < 8) :
    WP isa (seqs (isOdd a)) t fun t' =>
      t'.gpr .x9 = bit (wv t.mem G (slot w a) w % 2 = 1) ∧ t'.mem = t.mem ∧ Keep [.x3, .x4, .x9, .x16] t t' := by
  have sa := Nat.le_trans (slot_le (w := w) ha) hZ
  unfold isOdd
  simp only [seqs]
  refine WP.seq (WP.mono (WP.keep [.x16] (Q := fun t' => t'.gpr .x16 = off G (slot w a) ∧ t'.mem = t.mem)
    (by brun [hg.x0, hdr_enc (sArr_lt ha), hg.ld hZ (sArr_lt ha), hg.hdr.harr a ha]) rfl rfl rfl)
    fun t₁ ⟨⟨h16, hm₁⟩, k₁⟩ => ?_)
  have hs₁ := hg.scr.congr k₁.wr
  refine WP.mono (WP.keep [.x3, .x4, .x9] (Q := fun t' => t'.gpr .x9 = word t₁.mem G (slot w a) &&& 1 ∧
      t'.mem = t₁.mem) (by brun [h16, hs₁.ld (show slot w a + 8 ≤ Zx by omega_arith)]; rfl)
    (by decide) (by decide) (by decide +kernel)) fun t' ⟨⟨h9, hm'⟩, k'⟩ =>
      ⟨?_, hm'.trans hm₁, (k₁.trans k').mono (by decide)⟩
  rw [h9, hm₁]
  have e : (word t.mem G (slot w a)).toNat % 2 = wv t.mem G (slot w a) w % 2 := by
    rw [← wv_mod64 _ _ _ hw, Nat.mod_mod_of_dvd _ (by decide)]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (1 : BitVec 64).toNat = 1 from rfl, Nat.and_one_is_mod, e]
  by_cases h : wv t.mem G (slot w a) w % 2 = 1
  · simp [bit, h]
  · have : wv t.mem G (slot w a) w % 2 = 0 := by omega_arith
    simp [bit, this]

/-- `range a` (`a ≠ aTmp`, with the number 1 in `aOne`): `x9` and the slot
`sF` hold `1 < [a] < m − 1`, as `1 < [a]` and `2 ⌊[a] / 2⌋ + 1 < m`. -/
theorem range_ok {t : State} {G : Addr} {Zx w : Nat} {mi : BitVec 64} (hg : Good t G Zx w mi) (hZ : slot w 8 ≤ Zx)
    (hw : 1 ≤ w) (hw' : w < 2 ^ 31) {a : Nat} (ha : a < 8) (haT : a ≠ aTmp)
    (hone : wv t.mem G (slot w aOne) w = 1) :
    WP isa (seqs (range a)) t fun t' =>
      t'.gpr .x9 = bit (1 < wv t.mem G (slot w a) w ∧
        2 * (wv t.mem G (slot w a) w / 2) + 1 < wv t.mem G (slot w aN) w) ∧
      word t'.mem G (8 * sF) = t'.gpr .x9 ∧
      Frm G [(slot w aTmp, 8 * w), (8 * sF, 8)] t.mem t'.mem ∧ Keep mmRegs t t' := by
  have hn := hg.scr.nowrap
  have sT := Nat.le_trans (slot_le (w := w) (show aTmp < 8 by decide)) hZ
  have hT0 := hdr_lt_slot w aTmp (show 31 < 32 by decide)
  have hF := hdr_lt_slot w 0 (show sF < 32 by decide)
  have hFa := hdr_lt_slot w a (show sF < 32 by decide)
  have hFN := hdr_lt_slot w aN (show sF < 32 by decide)
  have hFT := hdr_lt_slot w aTmp (show sF < 32 by decide)
  have h8 := hdr_lt_slot w 8 (show sF < 32 by decide)
  have eF : sF = 30 := rfl
  have sa := Nat.le_trans (slot_le (w := w) ha) hZ
  have sN := Nat.le_trans (slot_le (w := w) (show aN < 8 by decide)) hZ
  have sTa := slot_sep (w := w) haT
  have sTN := slot_sep (w := w) (show aN ≠ aTmp by decide)
  have sO := slot_le (w := w) (show aOne < 8 by decide)
  unfold range gt1
  rw [List.append_assoc, List.append_assoc]
  refine wp_seqs_append (by simp [ltArr, cmpArr]) (by simp) (WP.mono (ltArr_ok hg hZ hw hw' (show aOne < 8 by decide) ha)
    fun t₁ ⟨h9₁, hm₁, k₁⟩ => ?_)
  rw [hone] at h9₁
  have hg₁ : Good t₁ G Zx w mi := ⟨hg.scr.congr k₁.wr, (k₁.gpr .x0 (by decide)).trans hg.x0, by rw [hm₁]; exact hg.hdr⟩
  refine wp_seqs_append (by simp) (by simp [ltP, copyArr]) ?_
  simp only [seqs]
  refine WP.mono (WP.keep [] (Q := fun t' => t'.mem = t₁.mem.writeW (off G (8 * sF)) (t₁.gpr .x9))
    (by brun [hg₁.x0, hdr_enc (show sF < 32 by decide), hg₁.scr.st (show 8 * sF + 8 ≤ Zx by omega_arith)])
    rfl rfl rfl) fun t₂ ⟨hm₂, k₂⟩ => ?_
  have o₂ := writeW_outside t₁.mem G (d := 8 * sF) (t₁.gpr .x9) (by omega_arith)
  rw [← hm₂] at o₂
  have hg₂ : Good t₂ G Zx w mi := hg₁.of_outside (o := 8 * sF) (n := 8) (by omega_arith) o₂ k₂.wr
    (k₂.gpr .x0 (by decide))
  refine wp_seqs_append (by simp [ltP, copyArr]) (by simp) (WP.mono (ltP_ok hg₂ hZ hw hw' ha haT)
    fun t₃ ⟨h9₃, ho₃, k₃⟩ => ?_)
  have hA₂ : wv t₂.mem G (slot w a) w = wv t.mem G (slot w a) w := by
    rw [o₂.wv (by omega_arith) (by omega_arith), hm₁]
  have hN₂ : wv t₂.mem G (slot w aN) w = wv t.mem G (slot w aN) w := by
    rw [o₂.wv (by omega_arith) (by omega_arith), hm₁]
  rw [hA₂, hN₂] at h9₃
  have hg₃ : Good t₃ G Zx w mi := hg₂.of_outside (by omega_arith) ho₃ k₃.wr (k₃.gpr .x0 (by decide))
  have hF₃ : word t₃.mem G (8 * sF) = t₁.gpr .x9 := by
    rw [ho₃.word (Or.inl (by omega_arith)) (by omega_arith), hm₂]; exact word_writeW_self _ _ _ _
  refine WP.mono (WP.keep [.x3, .x9] (Q := fun t' => t'.gpr .x9 = t₃.gpr .x9 &&& t₁.gpr .x9 ∧
      t'.mem = t₃.mem.writeW (off G (8 * sF)) (t₃.gpr .x9 &&& t₁.gpr .x9))
    (by unfold andF; brun [hg₃.x0, hdr_enc (show sF < 32 by decide), hg₃.scr.ld (show 8 * sF + 8 ≤ Zx by omega_arith),
      hg₃.scr.st (show 8 * sF + 8 ≤ Zx by omega_arith), hF₃])
    (by decide) (by decide) (by decide +kernel)) fun t' ⟨⟨h9, hm'⟩, k'⟩ => ⟨?_, ?_, ?_, ?_⟩
  · rw [h9, h9₃, h9₁]
    by_cases h1 : 1 < wv t.mem G (slot w a) w <;>
      by_cases h2 : 2 * (wv t.mem G (slot w a) w / 2) + 1 < wv t.mem G (slot w aN) w <;> simp [bit, h1, h2]
  · rw [hm', h9]; exact word_writeW_self _ _ _ _
  · intro x hx
    have o' := writeW_outside t₃.mem G (d := 8 * sF) (t₃.gpr .x9 &&& t₁.gpr .x9) (by omega_arith)
    rw [hm', o' x (hx (8 * sF, 8) (by simp)), ho₃ x (hx (slot w aTmp, 8 * w) (by simp)),
      o₂ x (hx (8 * sF, 8) (by simp)), hm₁]
  · exact (((k₁.trans k₂).trans k₃).trans k').mono (by decide)

/-- What `range` changes: past the header's first 17 slots, within the arrays,
and not the modulus or the number 1. -/
theorem range_frame (w : Nat) : ∀ r ∈ [(slot w aTmp, 8 * w), (8 * sF, 8)],
    8 * 17 ≤ r.1 ∧ r.1 + r.2 ≤ slot w 8 ∧ (r.1 + r.2 ≤ slot w aN ∨ slot w aN + 8 * (w + 2) ≤ r.1) ∧
      (r.1 + r.2 ≤ slot w aOne ∨ slot w aOne + 8 * (w + 2) ≤ r.1) := by
  have h1 := hdr_lt_slot w aTmp (show 31 < 32 by decide)
  have h2 := slot_le (w := w) (show aTmp < 8 by decide)
  have h3 := slot_sep (w := w) (show aTmp ≠ aN by decide)
  have h4 := slot_sep (w := w) (show aTmp ≠ aOne by decide)
  simp only [List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
  refine ⟨⟨by omega, by omega, by omega, by omega⟩, by decide, hdr_lt_slot w 8 (by decide),
    Or.inl (hdr_lt_slot w aN (by decide)), Or.inl (hdr_lt_slot w aOne (by decide))⟩

end VG.Proof.Ffdh.AArch64
