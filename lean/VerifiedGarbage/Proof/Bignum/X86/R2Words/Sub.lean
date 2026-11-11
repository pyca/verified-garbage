module

public import VerifiedGarbage.Proof.Bignum.X86.R2Words.Quot
public import VerifiedGarbage.Proof.Mont.X86.Rt.Step
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Bignum.X86.PublicCall

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

/-- Word 0 of `mulSub`, with `ebx` at `M₀` (`a`), `ebp` at `t₀` (`tt`) and `q̂`
in `ecx`: `t₀ + q̂ M₀ = 2^32 c` for the carry `c` in `t₁`; then `ebx` and
`ebp` a word on and `edi = 4 (W' - 1)`. -/
theorem subHead_ok {t : State} {is : List Instr} {Q : State → Prop} {base : Addr} {bytes len a tt : Nat}
    (ws : Ws t base bytes) (pb : PtrAt t base .ebx a) (pp : PtrAt t base .ebp tt) (ha : a + 4 ≤ bytes)
    (ht : tt + 8 ≤ bytes) (ca : CallArgument t base bytes 1 (BitVec.ofNat 32 len)) (hl : 1 ≤ len) (hl' : len ≤ 1024)
    (kk : ∀ t', w32 t'.mem base tt + (t.gpr .ecx).toNat * w32 t.mem base a = 2 ^ 32 * w32 t'.mem base (tt + 4) →
      Outside base tt 8 t.mem t'.mem → PtrAt t' base .ebx (a + 4) → PtrAt t' base .ebp (tt + 4) →
      t'.gpr .edi = BitVec.ofNat 32 (4 * wp len - 4) → Keeps [.eax, .ebx, .edx, .ebp, .edi] t t' →
      WP isa (.block is) t' Q) :
    WP isa (.block (subHead ++ is)) t Q := by
  have nw := ws.nowrap
  simp only [subHead, List.append_assoc, List.cons_append]
  refine wp_movS (readSrc_ptr ws pb (d := 0) (by omega)) fun t₁ U₁ _ => wp_mul fun t₂ U₂ => ?_
  have ws₂ := ws.of_wr (U₂.wr.trans U₁.wr)
  have pp₂ : PtrAt t₂ base .ebp tt := by rw [PtrAt, U₂.other _ (by decide) (by decide), U₁.other _ (by decide)]; exact pp
  refine wp_storeS (ea_ptr ws₂ pp₂ (d := 4) (by omega)) (ws_write ws₂ (by omega)) fun t₃ M₃ => ?_
  refine wp_movS rfl fun t₄ U₄ _ => wp_subS rfl fun t₅ U₅ c₅ => ?_
  have ws₅ := ws₂.of_wr (U₅.wr.trans (U₄.wr.trans M₃.wr))
  have pp₅ : PtrAt t₅ base .ebp tt := by rw [PtrAt, U₅.other _ (by decide), U₄.other _ (by decide), M₃.gpr]; exact pp₂
  refine wp_storeS (ea_ptr ws₅ pp₅ (d := 0) (by omega)) (ws_write ws₅ (by omega)) fun t₆ M₆ => ?_
  refine wp_sbbS rfl (by rw [M₆.cf]; exact c₅) fun t₇ U₇ _ => ?_
  have ws₇ := ws₅.of_wr (U₇.wr.trans M₆.wr)
  have pp₇ : PtrAt t₇ base .ebp tt := by rw [PtrAt, U₇.other _ (by decide), M₆.gpr]; exact pp₅
  refine wp_movS (readSrc_ptr ws₇ pp₇ (d := 4) (by omega)) fun t₈ U₈ _ => wp_subS rfl fun t₉ U₉ _ => ?_
  have ws₉ := ws₇.of_wr (U₉.wr.trans U₈.wr)
  have pp₉ : PtrAt t₉ base .ebp tt := by rw [PtrAt, U₉.other _ (by decide), U₈.other _ (by decide)]; exact pp₇
  refine wp_storeS (ea_ptr ws₉ pp₉ (d := 4) (by omega)) (ws_write ws₉ (by omega)) fun t₁₀ M₁₀ => ?_
  have K₁₀ : Keeps [.eax, .edx] t t₁₀ :=
    ((((U₁.keeps.mono (by decide)).trans U₂.keeps).trans (M₃.keeps _)).trans
      (((U₄.keeps.mono (by decide)).trans (U₅.keeps.mono (by decide))).trans (M₆.keeps _))).trans
      (((U₇.keeps.mono (by decide)).trans (U₈.keeps.mono (by decide))).trans
      ((U₉.keeps.mono (by decide)).trans (M₁₀.keeps _)))
  -- The values.
  have hA : (t₁.gpr .eax).toNat = w32 t.mem base a := by rw [U₁.gpr, Nat.add_zero]
  have hq : t₁.gpr .ecx = t.gpr .ecx := U₁.other _ (by decide)
  have lo : (t₂.gpr .eax).toNat = w32 t.mem base a * (t.gpr .ecx).toNat % 2 ^ 32 := by
    rw [U₂.eax, hA, hq, BitVec.toNat_ofNat]
  have hb := (mul_words (t.mem.readW (off base a) 32) (t.gpr .ecx)).2
  have hi : (t₂.gpr .edx).toNat = w32 t.mem base a * (t.gpr .ecx).toNat / 2 ^ 32 := by
    rw [U₂.edx, hA, hq, BitVec.toNat_ofNat]; simp only [w32] at *; omega
  have m₃ : t₃.mem = t.mem.writeW (off base (tt + 4)) (t₂.gpr .edx) := by rw [M₃.mem, U₂.mem, U₁.mem]
  have b₇ : (t₇.gpr .eax).toNat = if 0 < w32 t.mem base a * (t.gpr .ecx).toNat % 2 ^ 32 then 2 ^ 32 - 1 else 0 := by
    rw [U₇.gpr, sbb_self, U₄.gpr, U₄.other .eax (by decide), M₃.gpr, lo]
    by_cases e : 0 < w32 t.mem base a * (t.gpr .ecx).toNat % 2 ^ 32
    · rw [ite_eq_left (by simp only [decide_eq_true_eq]; exact e), ite_eq_left e]
    · rw [ite_eq_right (by simp only [decide_eq_true_eq]; exact e), ite_eq_right e]
  have t₀ : (t₅.gpr .edx).toNat = (2 ^ 32 - w32 t.mem base a * (t.gpr .ecx).toNat % 2 ^ 32) % 2 ^ 32 := by
    rw [U₅.gpr, BitVec.toNat_sub, U₄.gpr, U₄.other .eax (by decide), M₃.gpr, lo]; rfl
  have m₆ : t₆.mem = t₃.mem.writeW (off base tt) (t₅.gpr .edx) := by rw [M₆.mem, U₅.mem, U₄.mem, Nat.add_zero]
  have hi₈ : t₈.gpr .edx = t₂.gpr .edx := by
    rw [U₈.gpr, U₇.mem, m₆]
    apply BitVec.eq_of_toNat_eq
    change w32 _ base (tt + 4) = _
    rw [w32_write_ne (size := bytes) nw (by omega) (by omega) (by omega), m₃, w32_write_self]
  have c₉ : (t₉.gpr .edx).toNat = w32 t.mem base a * (t.gpr .ecx).toNat / 2 ^ 32 +
      (if 0 < w32 t.mem base a * (t.gpr .ecx).toNat % 2 ^ 32 then 1 else 0) := by
    rw [U₉.gpr, BitVec.toNat_sub, U₈.other .eax (by decide), b₇, hi₈, hi]
    by_cases e : 0 < w32 t.mem base a * (t.gpr .ecx).toNat % 2 ^ 32
    · simp only [e, ↓reduceIte]; simp only [w32] at *; omega
    · simp only [e, ↓reduceIte]; simp only [w32] at *; omega
  have m₁₀ : t₁₀.mem = (t₃.mem.writeW (off base tt) (t₅.gpr .edx)).writeW (off base (tt + 4)) (t₉.gpr .edx) := by
    rw [M₁₀.mem, U₉.mem, U₈.mem, U₇.mem, m₆]
  have O₁₀ : Outside base tt 8 t.mem t₁₀.mem := by
    rw [m₁₀, m₃]
    exact (((writeW32_outside _ base _ (d := tt + 4) (by omega)).mono (by omega) (by omega)).trans
      ((writeW32_outside _ base _ (d := tt) (by omega)).mono (by omega) (by omega))).trans
      ((writeW32_outside _ base _ (d := tt + 4) (by omega)).mono (by omega) (by omega))
  have ca₁₀ := ca.keep K₁₀ (by decide) (O₁₀.mono (by omega) (by omega))
  refine width4_ok ca₁₀.readSrc hl' fun u Ku mu eu => ?_
  refine wp_subS rfl fun u₁ V₁ _ => wp_addS rfl fun u₂ V₂ _ => wp_addS rfl fun u₃ V₃ _ => ?_
  have pb₁₀ : PtrAt t₁₀ base .ebx a := by
    rw [PtrAt, K₁₀.1 _ (by decide)]; exact pb
  have pp₁₀ : PtrAt t₁₀ base .ebp tt := by rw [PtrAt, M₁₀.gpr]; exact pp₉
  have hw : 1 ≤ wp len := by simp only [wp]; omega
  have hw' : 4 * wp len < 2 ^ 32 := by simp only [wp]; omega
  refine kk u₃ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [V₃.mem, V₂.mem, V₁.mem, mu, m₁₀, w32_write_ne (size := bytes) nw (by omega) (by omega) (by omega),
      w32_write_self, w32_write_self, t₀, c₉, Nat.mul_comm (t.gpr .ecx).toNat]
    simp only [w32] at *
    generalize (t.mem.readW (off base a) 32).toNat * (t.gpr .ecx).toNat = P at *
    split <;> omega
  · rw [V₃.mem, V₂.mem, V₁.mem, mu]; exact O₁₀
  · rw [PtrAt, V₃.other _ (by decide), V₂.gpr, V₁.other _ (by decide), Ku.1 _ (by decide), ptr_add pb₁₀]; rfl
  · rw [PtrAt, V₃.gpr, V₂.other _ (by decide), V₁.other _ (by decide), Ku.1 _ (by decide), ptr_add pp₁₀]; rfl
  · rw [V₃.other _ (by decide), V₂.other _ (by decide), V₁.gpr, eu]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (4 : BitVec 32).toNat = 4 from rfl]
    omega
  · exact (K₁₀.mono (by decide)).trans ((Ku.mono (by decide)).trans
      (((V₁.keeps.mono (by decide)).trans (V₂.keeps.mono (by decide))).trans (V₃.keeps.mono (by decide))))

/-- Word `W'` of `mulSub`, with `esi` at `x[W' - 1]` (`xx`) and `ebp` at
`t[W']` (`tt`), holding the carry: `t[W'] + c = x[W' - 1] + 2^32 b`; and
`edi` set back from argument 4. -/
theorem subTop_ok {t : State} {base : Addr} {bytes xx tt : Nat} {v : BitVec 32} (ws : Ws t base bytes)
    (ps : PtrAt t base .esi xx) (pp : PtrAt t base .ebp tt) (hx : xx + 4 ≤ bytes) (ht : tt + 4 ≤ bytes)
    (ca : CallArgument t base bytes 4 v) :
    WP isa (.block subTop) t fun t' => ∃ b, b < 2 ∧
      w32 t'.mem base tt + w32 t.mem base tt = w32 t.mem base xx + 2 ^ 32 * b ∧
      t'.mem = t.mem.writeW (off base tt) (BitVec.ofNat 32 (w32 t'.mem base tt)) ∧
      t'.gpr .edi = v ∧ Keeps [.edx, .edi] t t' := by
  have nw := ws.nowrap
  simp only [subTop]
  refine wp_movS (readSrc_ptr ws ps (d := 0) (by omega)) fun t₁ U₁ _ => ?_
  have pp₁ : PtrAt t₁ base .ebp tt := by rw [PtrAt, U₁.other _ (by decide)]; exact pp
  have ws₁ := ws.of_wr U₁.wr
  refine wp_subS (readSrc_ptr ws₁ pp₁ (d := 0) (by omega)) fun t₂ U₂ _ => ?_
  have pp₂ : PtrAt t₂ base .ebp tt := by rw [PtrAt, U₂.other _ (by decide)]; exact pp₁
  have ws₂ := ws₁.of_wr U₂.wr
  refine wp_storeS (ea_ptr ws₂ pp₂ (d := 0) (by omega)) (ws_write ws₂ (by omega)) fun t₃ M₃ => ?_
  have K₃ : Keeps [.edx, .edi] t t₃ := ((U₁.keeps.mono (by decide)).trans (U₂.keeps.mono (by decide))).trans (M₃.keeps _)
  have m₃ : t₃.mem = t.mem.writeW (off base tt) (t₂.gpr .edx) := by rw [M₃.mem, U₂.mem, U₁.mem, Nat.add_zero]
  have O₃ : Outside base 0 bytes t.mem t₃.mem := by
    rw [m₃]; exact (writeW32_outside _ base _ (d := tt) (by omega)).mono (by omega) (by omega)
  refine wp_movS (ca.keep K₃ (by decide) O₃).readSrc fun t₄ U₄ _ => WP.block_nil ?_
  have e₂ : (t₂.gpr .edx).toNat = (2 ^ 32 - w32 t.mem base tt + w32 t.mem base xx) % 2 ^ 32 := by
    rw [U₂.gpr, BitVec.toNat_sub, U₁.gpr, U₁.mem, Nat.add_zero, Nat.add_zero]
  have hw : w32 t₄.mem base tt = (t₂.gpr .edx).toNat := by rw [U₄.mem, m₃, w32_write_self]
  have hc : w32 t.mem base tt < 2 ^ 32 := (t.mem.readW (off base tt) 32).isLt
  have hxl : w32 t.mem base xx < 2 ^ 32 := (t.mem.readW (off base xx) 32).isLt
  refine ⟨if w32 t.mem base xx < w32 t.mem base tt then 1 else 0, by split <;> omega, ?_, ?_, U₄.gpr,
    K₃.trans (U₄.keeps.mono (by decide))⟩
  · rw [hw, e₂]; split <;> omega
  · rw [hw, BitVec.ofNat_toNat, BitVec.setWidth_eq, U₄.mem, m₃]

/-- After words `0, …, j - 1` of `mulSub` from `s`, for `q̂ = q` in `ecx`: the
words `T_j` of `t` and the carry `c` in `t[j]`:
`T_j + q M_j = X_(j-1) 2^32 + 2^(32 j) c`. -/
structure SubI (s : State) (base : Addr) (len q j : Nat) (u : State) : Prop where
  bx : PtrAt u base .ebx (numAt len 0 + 4 * j)
  si : PtrAt u base .esi (numAt len 4 + 4 * (j - 1))
  bp : PtrAt u base .ebp (numAt len 5 + 4 * j)
  di : u.gpr .edi = BitVec.ofNat 32 (4 * (wp len - j))
  cx : u.gpr .ecx = BitVec.ofNat 32 q
  qlt : q < 2 ^ 32
  keep : Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp, .edi] s u
  out : Outside base (numAt len 5) (4 * (j + 1)) s.mem u.mem
  val : val32 u.mem base (numAt len 5) j + q * val32 s.mem base (numAt len 0) j =
    val32 s.mem base (numAt len 4) (j - 1) * 2 ^ 32 + 2 ^ (32 * j) * w32 u.mem base (numAt len 5 + 4 * j)

/-- The arithmetic of a word of `mulSub`. -/
theorem subStep_val {T q M X G t' A C c' Xw : Nat}
    (hI : T + q * M = X * 2 ^ 32 + G * 2 ^ 32 * C) (hv : t' + q * A + C = Xw + 2 ^ 32 * c') :
    T + G * 2 ^ 32 * t' + q * (M + G * 2 ^ 32 * A) = (X + G * Xw) * 2 ^ 32 + G * 2 ^ 32 * 2 ^ 32 * c' := by
  have e := congrArg (G * 2 ^ 32 * ·) hv
  simp only [Nat.mul_add] at e
  grind

/-- A word of `mulSub`'s loop. -/
theorem subStep_ok {s u : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {q j : Nat}
    (h : PcIn base bytes len args s) (hj1 : 1 ≤ j) (hj : j < wp len) (I : SubI s base len q j u) :
    WP isa (.block subBody) u fun u' => u'.zf = some (decide (j + 1 = wp len)) ∧ SubI s base len q (j + 1) u' := by
  have nw := h.scratch.nowrap
  have dims := h.dimensions
  have f5 := (h.fits (j := 5) (by decide)).2
  have hwp := wp_le_nw (len := len)
  have e0 : numAt len 0 = 256 := by simp [numAt, numOff]
  have e4 : numAt len 4 = 256 + 4 * wb len := by simp [numAt, numOff]
  have e5 : numAt len 5 = 256 + 5 * wb len := by simp [numAt, numOff]
  have ws : Ws u base bytes := h.ws.of_wr I.keep.2.2
  refine WP.mono (subBody_ok ws I.bx I.si I.bp (by omega) (by omega) (by omega) (.inl (by omega)))
    fun u' ⟨hv, O', pb', ps', pp', di', z', K'⟩ => ?_
  have hc := VG.Proof.Mont.X86.Rt.count_zf (N := wp len) (x := u.gpr .edi)
    (by rw [I.di, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]) hj
  refine ⟨by rw [z', hc.2], ⟨?_, ?_, ?_, ?_, ?_, I.qlt, I.keep.trans (K'.mono (by decide)), ?_, ?_⟩⟩
  · rw [show numAt len 0 + 4 * (j + 1) = numAt len 0 + 4 * j + 4 by omega]; exact pb'
  · rw [show numAt len 4 + 4 * (j + 1 - 1) = numAt len 4 + 4 * (j - 1) + 4 by omega]; exact ps'
  · rw [show numAt len 5 + 4 * (j + 1) = numAt len 5 + 4 * j + 4 by omega]; exact pp'
  · apply BitVec.eq_of_toNat_eq
    rw [di', hc.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  · rw [K'.1 _ (by decide)]; exact I.cx
  · exact (I.out.mono (by omega) (by omega)).trans (O'.mono (by omega) (by omega))
  · -- The words read, as in `s`.
    have hA : w32 u.mem base (numAt len 0 + 4 * j) = w32 s.mem base (numAt len 0 + 4 * j) :=
      I.out.w32 (.inl (by omega)) (by omega)
    have hX : w32 u.mem base (numAt len 4 + 4 * (j - 1)) = w32 s.mem base (numAt len 4 + 4 * (j - 1)) :=
      I.out.w32 (.inl (by omega)) (by omega)
    have hT : val32 u'.mem base (numAt len 5) j = val32 u.mem base (numAt len 5) j := O'.val32 (.inl (by omega)) (by omega)
    have hq : (u.gpr .ecx).toNat = q := by
      rw [I.cx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt I.qlt]
    rw [hA, hX, hq] at hv
    rw [val32_succ, val32_succ, hT, show j + 1 - 1 = (j - 1) + 1 by omega, val32_succ,
      show 32 * (j + 1) = 32 * (j - 1) + 32 + 32 by omega, show 32 * j = 32 * (j - 1) + 32 by omega,
      show numAt len 5 + 4 * (j + 1) = numAt len 5 + 4 * j + 4 by omega,
      show numAt len 4 + 4 * (j - 1) = numAt len 4 + 4 * (j - 1) from rfl, Nat.pow_add, Nat.pow_add]
    have hI := I.val
    rw [show 32 * j = 32 * (j - 1) + 32 by omega, Nat.pow_add] at hI
    rw [Nat.pow_add]
    exact subStep_val hI hv

/-- `mulSub`'s loop: words `1, …, W' - 1`. -/
theorem subLoop_ok {s u : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {q : Nat}
    (h : PcIn base bytes len args s) (I : SubI s base len q 1 u) :
    WP isa (.loop (.block subBody) .ne) u fun u' => SubI s base len q (wp len) u' := by
  have hl := h.lower
  have hw : 2 ≤ wp len := by simp only [wp]; omega
  refine WP.loop (M := isa) (fun n u => ∃ j, n = wp len - j ∧ 1 ≤ j ∧ j < wp len ∧ SubI s base len q j u) ?_ _ u
    ⟨1, rfl, Nat.le_refl _, by omega, I⟩
  rintro n u ⟨j, rfl, hj1, hj, I⟩
  refine WP.mono (subStep_ok h hj1 hj I) fun u' ⟨z, I'⟩ => ?_
  by_cases e : j + 1 = wp len
  · exact .inl ⟨by simp only [eval, z, e, decide_true, Option.map_some, Bool.not_true], e ▸ I'⟩
  · exact .inr ⟨by simp only [eval, z, e, decide_false, Option.map_some, Bool.not_false], wp len - (j + 1),
      by omega, j + 1, rfl, by omega, by omega, I'⟩

/-- The arithmetic of `mulSub`'s top word. -/
theorem subTop_val {T q M X G t' C x b : Nat}
    (hI : T + q * M = X * 2 ^ 32 + G * 2 ^ 32 * C) (hv : t' + C = x + 2 ^ 32 * b) :
    T + G * 2 ^ 32 * t' + q * M = (X + G * x) * 2 ^ 32 + G * 2 ^ 32 * 2 ^ 32 * b := by
  have e := congrArg (G * 2 ^ 32 * ·) hv
  simp only [Nat.mul_add] at e
  grind

theorem subFinal_val {mt mu ms : Mem} {base : Addr} {T M X q W b : Nat} (hW : 1 ≤ W)
    (hT : val32 mt base T W = val32 mu base T W)
    (hI : val32 mu base T W + q * val32 ms base M W =
      val32 ms base X (W - 1) * 2 ^ 32 + 2 ^ (32 * W) * w32 mu base (T + 4 * W))
    (hv : w32 mt base (T + 4 * W) + w32 mu base (T + 4 * W) = w32 ms base (X + 4 * (W - 1)) + 2 ^ 32 * b) :
    val32 mt base T (W + 1) + q * val32 ms base M W = val32 ms base X W * 2 ^ 32 + 2 ^ (32 * (W + 1)) * b := by
  obtain ⟨k, rfl⟩ : ∃ k, W = k + 1 := ⟨W - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hI hv
  rw [val32_succ mt base T (k + 1), hT, val32_succ ms base X k, show 32 * (k + 1 + 1) = 32 * k + 32 + 32 by omega,
    show 32 * (k + 1) = 32 * k + 32 by omega, Nat.pow_add, Nat.pow_add]
  rw [show 32 * (k + 1) = 32 * k + 32 by omega, Nat.pow_add] at hI
  rw [Nat.pow_add]
  exact subTop_val hI hv

/-- `mulSub`'s top word, and `edi` set back. -/
theorem subFinal_ok {s u : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {q : Nat}
    (h : PcIn base bytes len args s) (I : SubI s base len q (wp len) u) :
    WP isa (.block subTop) u fun t => ∃ b, b < 2 ∧
      val32 t.mem base (numAt len 5) (wp len + 1) + q * val32 s.mem base (numAt len 0) (wp len) =
        val32 s.mem base (numAt len 4) (wp len) * 2 ^ 32 + 2 ^ (32 * (wp len + 1)) * b ∧
      Outside base (numAt len 5) (4 * (wp len + 1)) s.mem t.mem ∧ Keeps k6 s t := by
  have nw := h.scratch.nowrap
  have dims := h.dimensions
  have f5 := (h.fits (j := 5) (by decide)).2
  have hwp := wp_le_nw (len := len)
  have hl := h.lower
  have hw : 2 ≤ wp len := by simp only [wp]; omega
  have e4 : numAt len 4 = 256 + 4 * wb len := by simp [numAt, numOff]
  have e5 : numAt len 5 = 256 + 5 * wb len := by simp [numAt, numOff]
  have ws : Ws u base bytes := h.ws.of_wr I.keep.2.2
  have ca := (h.stack 4 (by decide)).keep I.keep (by decide) (I.out.mono (by omega) (by omega))
  refine WP.mono (subTop_ok ws I.si I.bp (by omega) (by omega) ca) fun t ⟨b, hb, hv, hm, hdi, K⟩ => ⟨b, hb, ?_, ?_, ?_⟩
  · have hX : w32 u.mem base (numAt len 4 + 4 * (wp len - 1)) = w32 s.mem base (numAt len 4 + 4 * (wp len - 1)) :=
      I.out.w32 (.inl (by omega)) (by omega)
    have O := writeW32_outside u.mem base (d := numAt len 5 + 4 * wp len) (BitVec.ofNat 32 (w32 t.mem base
      (numAt len 5 + 4 * wp len))) (by omega)
    rw [← hm] at O
    have hT : val32 t.mem base (numAt len 5) (wp len) = val32 u.mem base (numAt len 5) (wp len) :=
      O.val32 (.inl (by omega)) (by omega)
    rw [hX] at hv
    exact subFinal_val (by omega) hT I.val hv
  · rw [hm]
    exact (I.out.mono (by omega) (by omega)).trans
      ((writeW32_outside _ base _ (d := numAt len 5 + 4 * wp len) (by omega)).mono (by omega) (by omega))
  · refine ⟨fun r hr => ?_, by rw [K.2.1, I.keep.2.1], by rw [K.2.2, I.keep.2.2]⟩
    by_cases e : r = .edi
    · subst e; rw [hdi, h.edi_eq]
    · have e' : r = .esp := by revert hr e; cases r <;> decide
      subst e'; rw [K.1 _ (by decide), I.keep.1 _ (by decide)]

/-- `mulSub`: `t = x 2^32 - q̂ M` over `W' + 1` words, for `q̂ = q` at 180:
`t + q M = x 2^32 + 2^(32 (W' + 1)) b`, over `M`'s and `x`'s `W'` words. -/
theorem mulSub_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (h : PcIn base bytes len args s) :
    WP isa mulSub s fun t => ∃ b, b < 2 ∧
      val32 t.mem base (numAt len 5) (wp len + 1) + w32 s.mem base oQ * val32 s.mem base (numAt len 0) (wp len) =
        val32 s.mem base (numAt len 4) (wp len) * 2 ^ 32 + 2 ^ (32 * (wp len + 1)) * b ∧
      Outside base (numAt len 5) (4 * (wp len + 1)) s.mem t.mem ∧ Keeps k6 s t := by
  have nw := h.scratch.nowrap
  have dims := h.dimensions
  have f5 := (h.fits (j := 5) (by decide)).2
  have hwp := wp_le_nw (len := len)
  have hl := h.lower
  have hwp16 : 16 ≤ wp len := by simp only [wp]; omega
  have e0 : numAt len 0 = 256 := by simp [numAt, numOff]
  have e4 : numAt len 4 = 256 + 4 * wb len := by simp [numAt, numOff]
  have e5 : numAt len 5 = 256 + 5 * wb len := by simp [numAt, numOff]
  have ws := h.ws
  obtain ⟨q, hq⟩ : ∃ q, q = w32 s.mem base oQ := ⟨_, rfl⟩
  rw [← hq]
  unfold mulSub
  simp only [seqs, subPtrs, List.append_assoc, List.cons_append, List.nil_append]
  -- The pointers, `q̂` and word 0.
  refine WP.seq (slotPtr_ok (r := .ebx) (j := 0) (t := .edx) (by decide) (by decide) h.edi h.width h.upper
    (by decide) fun u₁ K₁ m₁ p₁ _ => ?_)
  · refine slotPtr_ok (r := .esi) (j := 4) (t := .edx) (by decide) (by decide) (by rw [K₁.1 _ (by decide)]; exact h.edi)
      ((h.stack 1 (by decide)).keep K₁ (by decide) (by rw [m₁]; exact Outside.refl _ _ _ _) |>.readSrc |>.trans
        (by rw [h.wLen])) h.upper (by decide) fun u₂ K₂ m₂ p₂ _ => ?_
    have K₁₂ : Keeps [.ebx, .edx, .esi] s u₂ := (K₁.mono (by decide)).trans (K₂.mono (by decide))
    refine slotPtr_ok (r := .ebp) (j := 5) (t := .edx) (by decide) (by decide) (by rw [K₁₂.1 _ (by decide)]; exact h.edi)
      ((h.stack 1 (by decide)).keep K₁₂ (by decide) (by rw [m₂, m₁]; exact Outside.refl _ _ _ _) |>.readSrc |>.trans
        (by rw [h.wLen])) h.upper (by decide) fun u₃ K₃ m₃ p₃ _ => ?_
    have K₁₃ : Keeps [.ebx, .edx, .esi, .ebp] s u₃ := (K₁₂.mono (by decide)).trans (K₃.mono (by decide))
    have hu₃ := h.keep K₁₃ (by decide) (by decide) (by rw [m₃, m₂, m₁]; exact Outside.refl _ _ _ _)
    have di₃ : PtrAt u₃ base .edi 0 := by rw [PtrAt, Nat.add_zero, Nat.mod_eq_of_lt (by omega)]; exact hu₃.edi
    have rq := readSrc_ptr hu₃.ws di₃ (d := oQ) (by simp only [oQ]; omega)
    rw [Nat.zero_add] at rq
    refine wp_movS rq fun u₄ U₄ _ => ?_
    have K₁₄ : Keeps [.ebx, .ecx, .edx, .esi, .ebp] s u₄ := (K₁₃.mono (by decide)).trans (U₄.keeps.mono (by decide))
    have hu₄ := h.keep K₁₄ (by decide) (by decide) (by rw [U₄.mem, m₃, m₂, m₁]; exact Outside.refl _ _ _ _)
    have pb₄ : PtrAt u₄ base .ebx (numAt len 0) := by
      rw [PtrAt, U₄.other _ (by decide), K₃.1 _ (by decide), K₂.1 _ (by decide)]; exact p₁
    have ps₄ : PtrAt u₄ base .esi (numAt len 4) := by
      rw [PtrAt, U₄.other _ (by decide), K₃.1 _ (by decide)]; exact p₂
    have pp₄ : PtrAt u₄ base .ebp (numAt len 5) := by rw [PtrAt, U₄.other _ (by decide)]; exact p₃
    have hq32 : q < 2 ^ 32 := by rw [hq]; exact (s.mem.readW _ 32).isLt
    have q₄ : u₄.gpr .ecx = BitVec.ofNat 32 q := by
      apply BitVec.eq_of_toNat_eq
      rw [U₄.gpr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hq32, hq, m₃, m₂, m₁]
    have m₄ : u₄.mem = s.mem := by rw [U₄.mem, m₃, m₂, m₁]
    rw [← List.append_nil subHead]
    refine subHead_ok hu₄.ws pb₄ pp₄ (by rw [e0]; omega) (by rw [e5]; omega)
      (by have := hu₄.stack 1 (by decide); rw [h.wLen] at this; exact this)
      (by omega) h.upper fun t v O pb pp di K => WP.block_nil ?_
    refine WP.seq (WP.mono (subLoop_ok h ⟨by rw [Nat.mul_one]; exact pb, ?_, by rw [Nat.mul_one]; exact pp, ?_,
      by rw [K.1 _ (by decide)]; exact q₄, hq32, (K₁₄.mono (by decide)).trans (K.mono (by decide)), ?_, ?_⟩) fun u hu => subFinal_ok h hu)
    · rw [PtrAt, K.1 _ (by decide), Nat.sub_self, Nat.mul_zero, Nat.add_zero]; exact ps₄
    · rw [di]; congr 1; omega
    · rw [← m₄]; exact O
    · rw [val32, val32, val32, val32, Nat.mul_one, ← m₄]
      have hq' : (u₄.gpr .ecx).toNat = q := by rw [q₄, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hq32]
      rw [hq'] at v
      simp only [Nat.mul_zero, Nat.add_zero, Nat.zero_mul, Nat.zero_add, Nat.mul_one]
      exact v

end VG.Proof.Bignum.X86.R2Words
