module

public import VerifiedGarbage.Proof.Bignum.X86.R2Words.Quot
public import VerifiedGarbage.Proof.Mont.X86.Rt.Step
import VerifiedGarbage.Proof.Framework.Omega

/-!
# `R2Words` on x86: `t = x 2^32 - q̂ M`

A word of `mulSub` (`subBody_ok`): from the carry `c` in `t[i]`, `t[i] =
x[i - 1] - lo(q̂ Mᵢ + c)` and the next carry `hi(q̂ Mᵢ + c) + borrow` in
`t[i + 1]`, so that `t[i] + q̂ Mᵢ + c = x[i - 1] + 2^32 c'`.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.R2Words

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86.PublicRt VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86.PublicRt VG.Impl.Bignum.X86.R2Words VG.Proof.Bignum.X86.PrecomputeRt

/-- The carry of a word: `hi(p) + β < 2^32` for `p = q a + c` and the borrow
`β` of `x - lo(p)`. -/
theorem carry_fits {q a c x : Nat} (hq : q < 2 ^ 32) (ha : a < 2 ^ 32) (hc : c < 2 ^ 32) (hx : x < 2 ^ 32) :
    (q * a + c) / 2 ^ 32 + (if x < (q * a + c) % 2 ^ 32 then 1 else 0) < 2 ^ 32 := by
  have h : q * a ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) := Nat.mul_le_mul (by omega) (by omega)
  generalize q * a = P at h
  split <;> omega

/-- A word of `mulSub`, with `ebx` at `Mᵢ` (`a`), `esi` at `x[i - 1]` (`xx`),
`ebp` at `t[i]` (`tt`), holding the carry, and `q̂` in `ecx`. -/
theorem subBody_ok {t : State} {base : Addr} {bytes a xx tt : Nat} (ws : Ws t base bytes)
    (pb : PtrAt t base .ebx a) (ps : PtrAt t base .esi xx) (pp : PtrAt t base .ebp tt)
    (ha : a + 4 ≤ bytes) (hx : xx + 4 ≤ bytes) (ht : tt + 8 ≤ bytes) (hxt : xx + 4 ≤ tt ∨ tt + 8 ≤ xx) :
    WP isa (.block subBody) t fun t' =>
      w32 t'.mem base tt + (t.gpr .ecx).toNat * w32 t.mem base a + w32 t.mem base tt =
        w32 t.mem base xx + 2 ^ 32 * w32 t'.mem base (tt + 4) ∧
      Outside base tt 8 t.mem t'.mem ∧ PtrAt t' base .ebx (a + 4) ∧ PtrAt t' base .esi (xx + 4) ∧
      PtrAt t' base .ebp (tt + 4) ∧ t'.gpr .edi = t.gpr .edi - 4 ∧ t'.zf = some (t.gpr .edi - 4 == 0) ∧
      Keeps [.eax, .ebx, .edx, .esi, .ebp, .edi] t t' := by
  have nw := ws.nowrap
  simp only [subBody]
  refine wp_movS (readSrc_ptr ws pb (d := 0) (by omega)) fun t₁ U₁ _ => wp_mul fun t₂ U₂ => ?_
  have ws₂ := ws.of_wr (U₂.wr.trans U₁.wr)
  have pp₂ : PtrAt t₂ base .ebp tt := by rw [PtrAt, U₂.other _ (by decide) (by decide), U₁.other _ (by decide)]; exact pp
  refine wp_addS (readSrc_ptr ws₂ pp₂ (d := 0) (by omega)) fun t₃ U₃ c₃ => wp_adcS rfl c₃ fun t₄ U₄ _ => ?_
  have ws₄ := ws₂.of_wr (U₄.wr.trans U₃.wr)
  have pp₄ : PtrAt t₄ base .ebp tt := by rw [PtrAt, U₄.other _ (by decide), U₃.other _ (by decide)]; exact pp₂
  refine wp_storeS (ea_ptr ws₄ pp₄ (d := 4) (by omega)) (ws_write ws₄ (by omega)) fun t₅ M₅ => ?_
  have ws₅ := ws₄.of_wr M₅.wr
  have ps₅ : PtrAt t₅ base .esi xx := by
    rw [PtrAt, M₅.gpr, U₄.other _ (by decide), U₃.other _ (by decide), U₂.other _ (by decide) (by decide),
      U₁.other _ (by decide)]; exact ps
  refine wp_movS (readSrc_ptr ws₅ ps₅ (d := 0) (by omega)) fun t₆ U₆ _ => wp_subS rfl fun t₇ U₇ c₇ => ?_
  have ws₇ := ws₅.of_wr (U₇.wr.trans U₆.wr)
  have pp₇ : PtrAt t₇ base .ebp tt := by rw [PtrAt, U₇.other _ (by decide), U₆.other _ (by decide), M₅.gpr]; exact pp₄
  refine wp_storeS (ea_ptr ws₇ pp₇ (d := 0) (by omega)) (ws_write ws₇ (by omega)) fun t₈ M₈ => ?_
  have ws₈ := ws₇.of_wr M₈.wr
  have pp₈ : PtrAt t₈ base .ebp tt := by rw [PtrAt, M₈.gpr]; exact pp₇
  refine wp_sbbS rfl (by rw [M₈.cf]; exact c₇) fun t₉ U₉ _ => ?_
  have ws₉ := ws₈.of_wr U₉.wr
  have pp₉ : PtrAt t₉ base .ebp tt := by rw [PtrAt, U₉.other _ (by decide)]; exact pp₈
  refine wp_movS (readSrc_ptr ws₉ pp₉ (d := 4) (by omega)) fun t₁₀ U₁₀ _ => wp_subS rfl fun t₁₁ U₁₁ _ => ?_
  have ws₁₁ := ws₉.of_wr (U₁₁.wr.trans U₁₀.wr)
  have pp₁₁ : PtrAt t₁₁ base .ebp tt := by rw [PtrAt, U₁₁.other _ (by decide), U₁₀.other _ (by decide)]; exact pp₉
  refine wp_storeS (ea_ptr ws₁₁ pp₁₁ (d := 4) (by omega)) (ws_write ws₁₁ (by omega)) fun t₁₂ M₁₂ => ?_
  refine wp_addS rfl fun t₁₃ U₁₃ _ => wp_addS rfl fun t₁₄ U₁₄ _ => wp_addS rfl fun t₁₅ U₁₅ _ => ?_
  refine wp_subZ rfl fun t₁₆ U₁₆ z₁₆ => WP.block_nil ?_
  -- The words read.
  have hA : (t₁.gpr .eax).toNat = w32 t.mem base a := by rw [U₁.gpr, Nat.add_zero]
  have hq : t₁.gpr .ecx = t.gpr .ecx := U₁.other _ (by decide)
  have m₄ : t₄.mem = t.mem := by rw [U₄.mem, U₃.mem, U₂.mem, U₁.mem]
  have lo₃ : (t₃.gpr .eax).toNat = (w32 t.mem base a * (t.gpr .ecx).toNat + w32 t.mem base tt) % 2 ^ 32 := by
    rw [U₃.gpr, BitVec.toNat_add, U₂.eax, hA, hq, BitVec.toNat_ofNat, U₂.mem, U₁.mem, Nat.add_zero]
    simp only [w32] at *; omega
  have hi₄ : (t₄.gpr .edx).toNat = (w32 t.mem base a * (t.gpr .ecx).toNat + w32 t.mem base tt) / 2 ^ 32 := by
    rw [U₄.gpr, add3_toNat, U₃.other .edx (by decide), U₂.edx, U₂.eax, hA, hq, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, U₂.mem, U₁.mem, Nat.add_zero]
    have hb := (mul_words (t.mem.readW (off base a) 32) (t.gpr .ecx)).2
    have hc : w32 t.mem base tt < 2 ^ 32 := (t.mem.readW (off base tt) 32).isLt
    change (w32 t.mem base a * (t.gpr .ecx).toNat / 2 ^ 32 % 2 ^ 32 + 0 +
      (decide (2 ^ 32 ≤ w32 t.mem base a * (t.gpr .ecx).toNat % 2 ^ 32 + w32 t.mem base tt)).toNat) % 2 ^ 32 = _ at *
    generalize w32 t.mem base a * (t.gpr .ecx).toNat = P at *
    cases h : decide (2 ^ 32 ≤ P % 2 ^ 32 + w32 t.mem base tt) <;>
      simp only [decide_eq_true_eq, decide_eq_false_iff_not] at h <;> simp only [Bool.toNat_false, Bool.toNat_true] <;>
      omega
  have m₅ : t₅.mem = t.mem.writeW (off base (tt + 4)) (t₄.gpr .edx) := by rw [M₅.mem, m₄]
  have hX : (t₆.gpr .edx).toNat = w32 t.mem base xx := by
    rw [U₆.gpr, Nat.add_zero, m₅]
    exact w32_write_ne (size := bytes) nw (by omega) (by omega) (by omega) _
  have ax₆ : t₆.gpr .eax = t₃.gpr .eax := by rw [U₆.other _ (by decide), M₅.gpr, U₄.other _ (by decide)]
  have m₈ : t₈.mem = t₅.mem.writeW (off base tt) (t₇.gpr .edx) := by rw [M₈.mem, U₇.mem, U₆.mem, Nat.add_zero]
  have hi₁₀ : t₁₀.gpr .edx = t₄.gpr .edx := by
    rw [U₁₀.gpr, U₉.mem, m₈]
    apply BitVec.eq_of_toNat_eq
    change w32 _ base (tt + 4) = _
    rw [w32_write_ne (size := bytes) nw (by omega) (by omega) (by omega), m₅, w32_write_self]
  have b₁₀ : (t₁₀.gpr .eax).toNat = if (t₆.gpr .edx).toNat < (t₆.gpr .eax).toNat then 2 ^ 32 - 1 else 0 := by
    rw [U₁₀.other _ (by decide), U₉.gpr, sbb_self]
    by_cases e : (t₆.gpr .edx).toNat < (t₆.gpr .eax).toNat
    · rw [ite_eq_left (by simp only [decide_eq_true_eq]; exact e), ite_eq_left e]
    · rw [ite_eq_right (by simp only [decide_eq_true_eq]; exact e), ite_eq_right e]
  rw [ax₆, lo₃, hX] at b₁₀
  have hc : w32 t.mem base tt < 2 ^ 32 := (t.mem.readW (off base tt) 32).isLt
  have hxl : w32 t.mem base xx < 2 ^ 32 := (t.mem.readW (off base xx) 32).isLt
  have fits := carry_fits (t.mem.readW (off base a) 32).isLt (t.gpr .ecx).isLt hc hxl
  have c₁₁ : (t₁₁.gpr .edx).toNat = (w32 t.mem base a * (t.gpr .ecx).toNat + w32 t.mem base tt) / 2 ^ 32 +
      (if w32 t.mem base xx < (w32 t.mem base a * (t.gpr .ecx).toNat + w32 t.mem base tt) % 2 ^ 32 then 1 else 0) := by
    rw [U₁₁.gpr, BitVec.toNat_sub, b₁₀, hi₁₀, hi₄]
    by_cases e : w32 t.mem base xx < (w32 t.mem base a * (t.gpr .ecx).toNat + w32 t.mem base tt) % 2 ^ 32
    · simp only [e, ↓reduceIte] at fits ⊢; simp only [w32] at *; omega
    · simp only [e, ↓reduceIte] at fits ⊢; simp only [w32] at *; omega
  have lo₇ : (t₇.gpr .edx).toNat = (2 ^ 32 - (w32 t.mem base a * (t.gpr .ecx).toNat + w32 t.mem base tt) % 2 ^ 32 +
      w32 t.mem base xx) % 2 ^ 32 := by
    rw [U₇.gpr, BitVec.toNat_sub, ax₆, lo₃, hX]
  have m₁₂ : t₁₆.mem = (t₅.mem.writeW (off base tt) (t₇.gpr .edx)).writeW (off base (tt + 4)) (t₁₁.gpr .edx) := by
    rw [U₁₆.mem, U₁₅.mem, U₁₄.mem, U₁₃.mem, M₁₂.mem, U₁₁.mem, U₁₀.mem, U₉.mem, m₈]
  -- Pointers and the count.
  have pb₁₂ : PtrAt t₁₂ base .ebx a := by
    rw [PtrAt, M₁₂.gpr, U₁₁.other _ (by decide), U₁₀.other _ (by decide), U₉.other _ (by decide), M₈.gpr,
      U₇.other _ (by decide), U₆.other _ (by decide), M₅.gpr, U₄.other _ (by decide), U₃.other _ (by decide),
      U₂.other _ (by decide) (by decide), U₁.other _ (by decide)]; exact pb
  have ps₁₂ : PtrAt t₁₂ base .esi xx := by
    rw [PtrAt, M₁₂.gpr, U₁₁.other _ (by decide), U₁₀.other _ (by decide), U₉.other _ (by decide), M₈.gpr,
      U₇.other _ (by decide), U₆.other _ (by decide)]; exact ps₅
  have pp₁₂ : PtrAt t₁₂ base .ebp tt := by rw [PtrAt, M₁₂.gpr]; exact pp₁₁
  have di₁₂ : t₁₂.gpr .edi = t.gpr .edi := by
    rw [M₁₂.gpr, U₁₁.other _ (by decide), U₁₀.other _ (by decide), U₉.other _ (by decide), M₈.gpr,
      U₇.other _ (by decide), U₆.other _ (by decide), M₅.gpr, U₄.other _ (by decide), U₃.other _ (by decide),
      U₂.other _ (by decide) (by decide), U₁.other _ (by decide)]
  have K : Keeps [.eax, .ebx, .edx, .esi, .ebp, .edi] t t₁₆ := by
    refine ((((U₁.keeps.mono (by decide)).trans (U₂.keeps.mono (by decide))).trans
      (((U₃.keeps.mono (by decide)).trans (U₄.keeps.mono (by decide))).trans (M₅.keeps _))).trans
      ((((U₆.keeps.mono (by decide)).trans (U₇.keeps.mono (by decide))).trans
      ((M₈.keeps _).trans (U₉.keeps.mono (by decide)))).trans
      (((U₁₀.keeps.mono (by decide)).trans (U₁₁.keeps.mono (by decide))).trans (M₁₂.keeps _)))).trans
      (((U₁₃.keeps.mono (by decide)).trans (U₁₄.keeps.mono (by decide))).trans
      ((U₁₅.keeps.mono (by decide)).trans (U₁₆.keeps.mono (by decide))))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, K⟩
  · rw [m₁₂, w32_write_ne (size := bytes) nw (by omega) (by omega) (by omega), w32_write_self, w32_write_self,
      lo₇, c₁₁, Nat.mul_comm (t.gpr .ecx).toNat, Nat.add_assoc]
    simp only [w32] at *
    generalize (t.mem.readW (off base a) 32).toNat * (t.gpr .ecx).toNat + (t.mem.readW (off base tt) 32).toNat = P at *
    split <;> omega
  · rw [m₁₂, m₅]
    exact (((writeW32_outside _ base _ (d := tt + 4) (by omega)).mono (by omega) (by omega)).trans
      ((writeW32_outside _ base _ (d := tt) (by omega)).mono (by omega) (by omega))).trans
      ((writeW32_outside _ base _ (d := tt + 4) (by omega)).mono (by omega) (by omega))
  · rw [PtrAt, U₁₆.other _ (by decide), U₁₅.other _ (by decide), U₁₄.other _ (by decide), U₁₃.gpr,
      ptr_add pb₁₂]; rfl
  · rw [PtrAt, U₁₆.other _ (by decide), U₁₅.other _ (by decide), U₁₄.gpr, U₁₃.other _ (by decide),
      ptr_add ps₁₂]; rfl
  · rw [PtrAt, U₁₆.other _ (by decide), U₁₅.gpr, U₁₄.other _ (by decide), U₁₃.other _ (by decide),
      ptr_add pp₁₂]; rfl
  · rw [U₁₆.gpr, U₁₅.other _ (by decide), U₁₄.other _ (by decide), U₁₃.other _ (by decide), di₁₂]
  · rw [z₁₆, U₁₅.other _ (by decide), U₁₄.other _ (by decide), U₁₃.other _ (by decide), di₁₂]

end VG.Proof.Bignum.X86.R2Words
