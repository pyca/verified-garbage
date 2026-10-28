module

public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Virtualize
public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Slots
public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.State
public import VerifiedGarbage.Proof.Rsa.Divstep.OddInputDef
import VerifiedGarbage.Proof.Rsa.X86.GcdBatch.InitWords
import VerifiedGarbage.Proof.Mont.X86.Inverse
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Ptr
import VerifiedGarbage.Proof.Weierstrass.X86.InvRead
import VerifiedGarbage.Proof.Framework.Omega

/-! # The inverse's initial state at a run-time width

`operands_ok`: the virtual modulus `p` into `[2]` and the start values `f = p`,
`g = oddInput p x` (`InvBatch.operands_ok`); `init_ok`: then the coefficients, `delta`, the inverse
word and the batch count (`InvBatch.init_ok`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.InvBatchRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Impl.Rsa.X86.InvBatchRt
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Rsa.X86.KeyRt VG.Proof.Weierstrass
open VG.Proof.Weierstrass.X86.Inv (wordClob)
open VG.Proof.Rsa.Divstep (oddInput)

variable {L : Lay} {B : Addr} {Z len N : Nat}

/-- `1` replaced by `3`, an odd modulus the batches can run on. -/
def virtualMod (m : Nat) : Nat := if m = 1 then 3 else m

theorem virtualMod_odd {m : Nat} (odd : m % 2 = 1) : virtualMod m % 2 = 1 := by
  unfold virtualMod; split <;> omega

/-- The operands: `[2] = p`, `[4] = p` and `[5] = oddInput p x`, `n + 1` words. -/
theorem operands_ok {s : State} (h : Bx L s B Z len N) (hn2 : 2 ≤ nw len) {m x : Nat}
    (hm : val32 s.mem B (rv (kw len) (a 8)) (nw len) = m) (hx : val32 s.mem B (rv (kw len) (a 0)) (nw len) = x)
    {rest : Prog isa} {Q : State → Prop}
    (k : ∀ u, Bx L u B Z len N → val32 u.mem B (rv (kw len) (a 2)) (nw len) = virtualMod m →
      val32 u.mem B (rv (kw len) (a 4)) (nw len + 1) = virtualMod m →
      val32 u.mem B (rv (kw len) (a 5)) (nw len + 1) = oddInput (virtualMod m) x →
      Keeps wordClob s u →
      Unch B [(rv (kw len) (a 2), 4 * (8 * nw len + 8)), (rv (kw len) (a 12), 8 * nw len + 8)] s.mem u.mem →
      WP isa rest u Q) :
    WP isa (.seq (VG.Impl.Rsa.X86.InvBatchRt.copy L (a 2) (a 8) (nBytes .edi 0)) <|
      .seq (virtualize L) <|
      .seq (VG.Impl.Rsa.X86.InvBatchRt.copy L (a 4) (a 2) (nBytes .edi 0)) <|
      .seq (.block (zeroWord L { arr := 4, half := 1 })) <|
      .seq (VG.Impl.Rsa.X86.InvBatchRt.copy L (a 5) (a 0) (nBytes .edi 0)) <|
      .seq (.block (zeroWord L { arr := 5, half := 1 })) <|
      .seq (VG.Impl.Rsa.X86.InvBatchRt.zeros L (a 12) (nBytes .ecx 1)) <|
      .seq (.block (VG.Impl.Rsa.X86.GcdBatch.evenMask (VG.Impl.Rsa.X86.InvBatch.offset 0 0))) <|
      .seq (selIn L (a 12) (a 2) (nBytes .edi 0)) <|
      .seq (VG.Impl.Rsa.X86.InvBatchRt.chain L .adc (a 5) (a 5) (a 12) (nBytes .edx 1)) rest) s Q := by
  have hn := h.nowrap
  have hZ := h.halfZ
  have hf16 := h.fits16
  have hpos := h.ws.kw_pos
  have hw := kw_bound h.ws.lenLe
  have ke := kw_eq len
  have r0 := rv_a len 0; have r2 := rv_a len 2; have r4 := rv_a len 4; have r5 := rv_a len 5
  have r8 := rv_a len 8; have r12 := rv_a len 12
  have h41 := rv_half1' len 4; have h51 := rv_half1' len 5
  have hS : 0 < 8 * nw len + 8 := by omega
  have CS : CountSpec (nBytes .ecx 1) .ecx B Z (kw len) (nw len + 1) := by
    have := nBytes_spec (r := .ecx) (e := 1) (B := B) hZ (w := kw len) (by omega) (by decide) (by omega)
    rwa [show kw len / 2 + 1 = nw len + 1 by omega] at this
  -- `[2] = m`, then `p`.
  refine WP.seq (WP.mono (copy_ok h (o := a 2) (a := a 8) (e := 0) (by decide) (by omega) (by omega) (by omega))
    fun s₁ ⟨H₁, O₁, V₁, K₁⟩ => ?_)
  simp only [Nat.add_zero] at O₁ V₁
  rw [hm] at V₁
  refine WP.seq (WP.mono (virtualize_ok H₁ hn2) fun s₂ ⟨H₂, V₂, K₂, O₂⟩ => ?_)
  rw [V₁] at V₂
  change val32 s₂.mem B (rv (kw len) (a 2)) (nw len) = virtualMod m at V₂
  have X₂ : val32 s₂.mem B (rv (kw len) (a 0)) (nw len) = x := by
    rw [O₂.val32 (by omega) (by omega), O₁.val32 (by omega) (by omega), hx]
  -- `[4] = p`.
  refine WP.seq (WP.mono (copy_ok H₂ (o := a 4) (a := a 2) (e := 0) (by decide) (by omega) (by omega) (by omega))
    fun s₃ ⟨H₃, O₃, V₃, K₃⟩ => ?_)
  simp only [Nat.add_zero] at O₃ V₃
  rw [V₂] at V₃
  refine WP.seq (zeroWord_ok H₃ (x := { arr := 4, half := 1 }) (by omega) fun s₄ H₄ K₄ O₄ z₄ => WP.block_nil ?_)
  rw [h41] at O₄ z₄
  have F₄ : val32 s₄.mem B (rv (kw len) (a 4)) (nw len + 1) = virtualMod m := by
    rw [val32_succ, z₄, Nat.mul_zero, Nat.add_zero, O₄.val32 (by omega) (by omega), V₃]
  -- `[5] = x`.
  refine WP.seq (WP.mono (copy_ok H₄ (o := a 5) (a := a 0) (e := 0) (by decide) (by omega) (by omega) (by omega))
    fun s₅ ⟨H₅, O₅, V₅, K₅⟩ => ?_)
  simp only [Nat.add_zero] at O₅ V₅
  rw [O₄.val32 (by omega) (by omega), O₃.val32 (by omega) (by omega), X₂] at V₅
  refine WP.seq (zeroWord_ok H₅ (x := { arr := 5, half := 1 }) (by omega) fun s₆ H₆ K₆ O₆ z₆ => WP.block_nil ?_)
  rw [h51] at O₆ z₆
  have G₆ : val32 s₆.mem B (rv (kw len) (a 5)) (nw len + 1) = x := by
    rw [val32_succ, z₆, Nat.mul_zero, Nat.add_zero, O₆.val32 (by omega) (by omega), V₅]
  -- `[12] = 0`, then `p` where `x` is even.
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86.InvBatchRt.zeros_ok H₆ (o := a 12) CS (by omega) (by omega))
    fun s₇ ⟨H₇, O₇, V₇, K₇⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86.GcdBatch.evenMask_ok H₇.ws.ws.workspace
    (src := VG.Impl.Rsa.X86.InvBatch.offset 0 0) (by simp only [VG.Impl.Rsa.X86.InvBatch.offset]; omega))
    fun s₈ ⟨C₈, K₈, m₈⟩ => ?_)
  have H₈ : Bx L s₈ B Z len N := H₇.keep K₈ (by decide) (by decide) (o := 160) (c := 0)
    (by rw [m₈]; exact Outside.refl _ _ _ _) (Nat.le_refl _) (by omega)
  have o00 : VG.Impl.Rsa.X86.InvBatch.offset 0 0 = rv (kw len) (a 0) := by
    simp only [VG.Impl.Rsa.X86.InvBatch.offset]; omega
  rw [o00, O₇.w32 (by omega) (by omega), O₆.w32 (by omega) (by omega), O₅.w32 (by omega) (by omega),
    O₄.w32 (by omega) (by omega), O₃.w32 (by omega) (by omega), O₂.w32 (by omega) (by omega),
    O₁.w32 (by omega) (by omega)] at C₈
  have even : x % 2 = w32 s.mem B (rv (kw len) (a 0)) % 2 := by
    obtain ⟨j, hj⟩ : ∃ j, nw len = j + 1 := ⟨nw len - 1, by omega⟩
    rw [← hx, hj, val32]
    omega
  refine WP.seq (WP.mono (selIn_ok H₈ (o := a 12) (a := a 2) (e := 0) (k := decide (x % 2 = 0))
    (by rw [C₈, even]; by_cases he : w32 s.mem B (rv (kw len) (a 0)) % 2 = 0 <;> simp [he, cmask])
    (by decide) (by omega) (by omega) (by omega)) fun s₉ ⟨H₉, O₉, V₉, K₉⟩ => ?_)
  simp only [Nat.add_zero] at O₉ V₉
  rw [m₈, O₇.val32 (d := rv (kw len) (a 2)) (by omega) (by omega), O₆.val32 (by omega) (by omega),
    O₅.val32 (by omega) (by omega), O₄.val32 (by omega) (by omega), O₃.val32 (by omega) (by omega), V₂] at V₉
  have T₉ : val32 s₉.mem B (rv (kw len) (a 12)) (nw len + 1) = if x % 2 = 0 then virtualMod m else 0 := by
    have top7 : w32 s₇.mem B (rv (kw len) (a 12) + 4 * nw len) = 0 := by
      have := val32_succ s₇.mem B (rv (kw len) (a 12)) (nw len)
      rw [V₇] at this
      have p := Nat.two_pow_pos (32 * nw len)
      rcases Nat.eq_zero_or_pos (w32 s₇.mem B (rv (kw len) (a 12) + 4 * nw len)) with e | e
      · exact e
      · have := Nat.mul_le_mul_left (2 ^ (32 * nw len)) e; omega
    have low7 : val32 s₇.mem B (rv (kw len) (a 12)) (nw len) = 0 := by
      have := val32_succ s₇.mem B (rv (kw len) (a 12)) (nw len)
      rw [V₇] at this; omega
    rw [val32_succ, V₉, O₉.w32 (by omega) (by omega), m₈, top7, Nat.mul_zero, Nat.add_zero, low7]
    by_cases he : x % 2 = 0 <;> simp [he]
  -- `[5] += [12]`.
  refine WP.seq (WP.mono (chainAdd_ok H₉ (o := a 5) (a := a 5) (b := a 12) (e := 1) (by decide) rfl
    (by omega) (by omega) (by omega) (.inl (Nat.le_refl _)) (by omega)) fun u ⟨Hu, Ou, ⟨c, _, Vu⟩, Ku⟩ => ?_)
  have G₉ : val32 s₉.mem B (rv (kw len) (a 5)) (nw len + 1) = x := by
    rw [O₉.val32 (by omega) (by omega), m₈, O₇.val32 (by omega) (by omega), G₆]
  rw [G₉, T₉] at Vu
  have pv : virtualMod m < 2 ^ (32 * nw len) := V₂ ▸ val32_lt _ _ _ _
  have xv : x < 2 ^ (32 * nw len) := hx ▸ val32_lt _ _ _ _
  have sum : x + (if x % 2 = 0 then virtualMod m else 0) < 2 ^ (32 * (nw len + 1)) := by
    rw [pow32_succ]; split <;> omega
  have Gu : val32 u.mem B (rv (kw len) (a 5)) (nw len + 1) = oddInput (virtualMod m) x := by
    unfold oddInput
    cases c <;> simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one, Nat.add_zero] at Vu <;>
      omega
  refine k u Hu ?_ ?_ Gu ?_ ?_
  · rw [Ou.val32 (by omega) (by omega), O₉.val32 (by omega) (by omega), m₈, O₇.val32 (by omega) (by omega),
      O₆.val32 (by omega) (by omega), O₅.val32 (by omega) (by omega), O₄.val32 (by omega) (by omega),
      O₃.val32 (by omega) (by omega), V₂]
  · rw [Ou.val32 (by omega) (by omega), O₉.val32 (by omega) (by omega), m₈, O₇.val32 (by omega) (by omega),
      O₆.val32 (by omega) (by omega), O₅.val32 (by omega) (by omega), F₄]
  · exact ((((((((K₁.mono (by decide)).trans K₂).trans (K₃.mono (by decide))).trans (K₄.mono (by decide))).trans
      (K₅.mono (by decide))).trans (K₆.mono (by decide))).trans (K₇.mono (by decide))).trans
      ((K₈.mono (by decide)).trans (K₉.mono (by decide)))).trans (Ku.mono (by decide))
  · intro y hy
    have hA := hy (rv (kw len) (a 2), 4 * (8 * nw len + 8)) (by simp)
    have hT := hy (rv (kw len) (a 12), 8 * nw len + 8) (by simp)
    rw [Ou y (by omega), O₉ y (by omega), m₈, O₇ y (by omega), O₆ y (by omega), O₅ y (by omega), O₄ y (by omega),
      O₃ y (by omega), O₂ y (by omega), O₁ y (by omega)]

end VG.Proof.Rsa.X86.InvBatchRt
