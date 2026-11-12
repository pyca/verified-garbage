module

public import VerifiedGarbage.Proof.Rsa.X86.Rd.SqrtWBase
import VerifiedGarbage.Proof.Rsa.X86.Rd.Loops
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Chain
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.Omega

/-! # The square root by words on i686: a digit step's window

`winPtrs`, with `j` digits left (`m = j - 1`): `esi` at the remainder's window, word `2 m` of
`sqZ`, `ebx` at word `m` of `sqD`, `edx` the window's bytes `4 L` (`L = W' - m + 2`). Every block of
the digit step starts with it.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.Recover

/-! ## The window -/

section
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Proof.Rsa.X86.Keys (Keep arr num S slot)
open VG.Proof.Rsa.X86.KeyRt (RtWs kw arrPtr_ok lenSrc)
open VG.Proof.Rsa.X86.WordRt (wq MLen width4_ok)
open VG.Impl.Rsa.X86.RecoverRt (wid)
open VG.Impl.Rsa.X86.RecoverDetRt (sCt sqZ sqD sqT winPtrs nl)

variable {B : Addr} {Z len : Nat}

theorem sCt_val : sCt = 96 := rfl

/-- `winPtrs`, with `j` digits left (`m = j - 1`): `esi` at word `2 m` of `sqZ`, `ebx` at word `m`
of `sqD`, `edx = 4 L` for `L = W' - m + 2`, `eax = 4 m`. -/
theorem winPtrs_ok {s : State} {is : List Instr} {Q : State → Prop} (h : RtWs wid s B Z len 22) {a j : Nat}
    (hm : MLen s B Z nl a) (hC : slot s.mem B sCt = j) (hj1 : 1 ≤ j) (hj : j ≤ wq a)
    (k : ∀ u, Keeps [.eax, .ebx, .edx, .esi] s u → u.mem = s.mem →
      PtrAt u B .esi (arr (kw len) sqZ + 8 * (j - 1)) → PtrAt u B .ebx (arr (kw len) sqD + 4 * (j - 1)) →
      (u.gpr .edx).toNat = 4 * (wq a - (j - 1) + 2) → (u.gpr .eax).toNat = 4 * (j - 1) →
      WP isa (.block is) u Q) :
    WP isa (.block (winPtrs ++ is)) s Q := by
  have nw := h.ws.workspace.nowrap
  have fz := h.ws.arr_fit (j := sqZ) (by decide)
  have fd := h.ws.arr_fit (j := sqD) (by decide)
  have kb := VG.Proof.Rsa.X86.KeyRt.kw_bound h.lenLe
  have hle := hm.le
  simp only [S] at fz fd
  have hj32 : j < 2 ^ 32 := by simp only [wq] at hj; omega
  have hwa : wq a ≤ 256 := by simp only [wq]; omega
  simp only [winPtrs, List.append_assoc, List.cons_append, List.nil_append]
  refine wp_movS (readHdr h.ws (by rw [sCt_val]; decide)) fun u₁ U₁ _ => ?_
  refine wp_subS rfl fun u₂ U₂ _ => wp_addS rfl fun u₃ U₃ _ => wp_addS rfl fun u₄ U₄ _ => ?_
  have e₄ : (u₄.gpr .eax).toNat = 4 * (j - 1) := by
    have e1 : (1 : BitVec 32).toNat = 1 := rfl
    rw [U₄.gpr, U₃.gpr, U₂.gpr, U₁.gpr, hC]
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj32, e1, Nat.reducePow]
    omega
  have K₄ : Keeps [.eax] s u₄ := U₁.keeps.trans (U₂.keeps.trans (U₃.keeps.trans U₄.keeps))
  have m₄ : u₄.mem = s.mem := by rw [U₄.mem, U₃.mem, U₂.mem, U₁.mem]
  have h₄ := h.keep K₄ (by decide) (by decide) (by rw [m₄]; exact Outside.refl _ _ _ _)
  refine arrPtr_ok (lenSrc h₄) h₄.lenLe h₄.edi (r := .esi) (t := .edx) (j := sqZ) (by decide) (by decide)
    (by omega) fun u₅ U₅ m₅ p₅ _ => ?_
  refine wp_addS rfl fun u₆ U₆ _ => wp_addS rfl fun u₇ U₇ _ => ?_
  have a₅ : (u₅.gpr .eax).toNat = 4 * (j - 1) := by rw [U₅.1 _ (by decide)]; exact e₄
  have p₆ : PtrAt u₆ B .esi (arr (kw len) sqZ + 4 * (j - 1)) := by rw [PtrAt, U₆.gpr, ptr_add p₅, a₅]
  have a₆ : (u₆.gpr .eax).toNat = 4 * (j - 1) := by rw [U₆.other _ (by decide)]; exact a₅
  have p₇ : PtrAt u₇ B .esi (arr (kw len) sqZ + 8 * (j - 1)) := by
    rw [PtrAt, U₇.gpr, ptr_add p₆, a₆]; congr 2; omega
  have K₇ : Keeps [.eax, .edx, .esi] s u₇ :=
    (K₄.mono (by decide)).trans ((U₅.mono (by decide)).trans ((U₆.keeps.mono (by decide)).trans (U₇.keeps.mono (by decide))))
  have m₇ : u₇.mem = s.mem := by rw [U₇.mem, U₆.mem, m₅, m₄]
  have h₇ := h.keep K₇ (by decide) (by decide) (by rw [m₇]; exact Outside.refl _ _ _ _)
  refine arrPtr_ok (lenSrc h₇) h₇.lenLe h₇.edi (r := .ebx) (t := .edx) (j := sqD) (by decide) (by decide)
    (by omega) fun u₈ U₈ m₈ p₈ _ => ?_
  refine wp_addS rfl fun u₉ U₉ _ => ?_
  have a₈ : (u₈.gpr .eax).toNat = 4 * (j - 1) := by rw [U₈.1 _ (by decide), U₇.other _ (by decide)]; exact a₆
  have p₉ : PtrAt u₉ B .ebx (arr (kw len) sqD + 4 * (j - 1)) := by
    rw [PtrAt, U₉.gpr, ptr_add p₈, a₈]
  have K₉ : Keeps [.eax, .ebx, .edx, .esi] s u₉ :=
    (K₇.mono (by decide)).trans ((U₈.mono (by decide)).trans (U₉.keeps.mono (by decide)))
  have m₉ : u₉.mem = s.mem := by rw [U₉.mem, m₈, m₇]
  have hm₉ : MLen u₉ B Z nl a := hm.keep K₉ (by decide) (by rw [m₉]; exact Outside.refl _ _ _ _)
  refine width4_ok hm₉ fun u₁₀ U₁₀ m₁₀ e₁₀ => wp_subS rfl fun u₁₁ U₁₁ _ => wp_addS rfl fun u₁₂ U₁₂ _ => ?_
  have a₁₀ : (u₁₀.gpr .eax).toNat = 4 * (j - 1) := by
    rw [U₁₀.1 _ (by decide), U₉.other _ (by decide)]; exact a₈
  refine k u₁₂ ((K₉.mono (by decide)).trans ((U₁₀.mono (by decide)).trans
      ((U₁₁.keeps.mono (by decide)).trans (U₁₂.keeps.mono (by decide)))))
    (by rw [U₁₂.mem, U₁₁.mem, m₁₀, m₉]) ?_ ?_ ?_ ?_
  · rw [PtrAt, U₁₂.other _ (by decide), U₁₁.other _ (by decide), U₁₀.1 _ (by decide), U₉.other _ (by decide),
      U₈.1 _ (by decide)]; exact p₇
  · rw [PtrAt, U₁₂.other _ (by decide), U₁₁.other _ (by decide), U₁₀.1 _ (by decide)]; exact p₉
  · rw [U₁₂.gpr, U₁₁.gpr, e₁₀, U₁₀.1 _ (by decide)]
    have a₉ : (u₉.gpr .eax).toNat = 4 * (j - 1) := by rw [U₉.other _ (by decide)]; exact a₈
    have e8 : (8 : BitVec 32).toNat = 8 := rfl
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, a₉, e8, Nat.reducePow]
    omega
  · rw [U₁₂.other _ (by decide), U₁₁.other _ (by decide)]; exact a₁₀

end

end VG.Proof.Rsa.X86.Recover
