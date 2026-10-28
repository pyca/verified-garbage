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
import VerifiedGarbage.Proof.Divstep.Alg32Def

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

/-- What `init` writes: the header from the window on, arrays 2 to 7, and array 12. -/
def initWrites (len : Nat) : List (Nat × Nat) :=
  [(win, 88), (rv (kw len) (a 2), 6 * (8 * nw len + 8)), (rv (kw len) (a 12), 8 * nw len + 8)]

/-- `init` (`InvBatch.init_ok`). -/
theorem init_ok {s : State} (h : RtWs L s B Z len N) (room : 16 ≤ N) (hn2 : 2 ≤ nw len) {m x : Nat}
    (hm : val32 s.mem B (rv (kw len) (a 8)) (nw len) = m) (hx : val32 s.mem B (rv (kw len) (a 0)) (nw len) = x)
    (odd : m % 2 = 1) :
    WP isa (init L) s fun z => ∃ iv, Bx L z B Z len N ∧
      StateAt len B (virtualMod m) iv
        (Divstep.W32.invRun 30 (virtualMod m) iv (oddInput (virtualMod m) x) 0) z ∧
      (virtualMod m * iv + 1) % 2 ^ 32 = 0 ∧ w32 z.mem B 100 = 3 * (nw len + 1) ∧
      Keeps wordClob s z ∧ Unch B (initWrites len) s.mem z.mem := by
  have hn := h.ws.workspace.nowrap
  have hw := kw_bound h.lenLe
  have ke := kw_eq len
  have e16 : win = 16 := rfl
  have e52 : slotBase = 52 := rfl
  have e96 : halfSlot = 96 := rfl
  unfold init
  simp only [VG.Impl.Rsa.X86.Keys.seqs]
  -- The slots.
  rw [show slots L = slots L ++ [] from (List.append_nil _).symm]
  refine WP.seq (slots_ok h room fun s₀ H₀ K₀ O₀ => WP.block_nil ?_)
  have hZ := H₀.halfZ
  have hf16 := H₀.fits16
  have hpos := H₀.ws.kw_pos
  have r0 := rv_a len 0; have r2 := rv_a len 2; have r6 := rv_a len 6; have r7 := rv_a len 7
  have r8 := rv_a len 8; have r12 := rv_a len 12
  have hm₀ : val32 s₀.mem B (rv (kw len) (a 8)) (nw len) = m := by rw [O₀.val32 (by omega) (by omega), hm]
  have hx₀ : val32 s₀.mem B (rv (kw len) (a 0)) (nw len) = x := by rw [O₀.val32 (by omega) (by omega), hx]
  refine operands_ok H₀ hn2 hm₀ hx₀ fun u Hu P₂ F₄ G₅ Ku Uu => ?_
  have CS : CountSpec (nBytes .ecx 1) .ecx B Z (kw len) (nw len + 1) := by
    have := nBytes_spec (r := .ecx) (e := 1) (B := B) hZ (w := kw len) (by omega) (by decide) (by omega)
    rwa [show kw len / 2 + 1 = nw len + 1 by omega] at this
  -- `delta = 1`.
  refine WP.seq (wp_movS rfl fun u₁ V₁ _ => ?_)
  have hs₁ := Hu.ws.ws.workspace.of_keeps V₁.keeps (by decide)
  refine wp_storeS (hs₁.ea (by omega)) (hs₁.write (d := win) (n := 4) (by omega)) fun u₂ V₂ => WP.block_nil ?_
  have O₂ : Outside B win 4 u.mem u₂.mem := by rw [V₂.mem, V₁.mem]; exact writeW32_outside _ _ _ (by omega)
  have H₂ : Bx L u₂ B Z len N := Hu.keepLow (V₁.keeps.trans (V₂.keeps _)) (by decide) (by decide) O₂ (by decide)
  have D₂ : u₂.mem.readW (off B win) 32 = 1 := by
    apply BitVec.eq_of_toNat_eq
    change w32 u₂.mem B win = _
    rw [V₂.mem, w32_write_self, V₁.gpr]
  -- The coefficients `0` and `1`.
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86.InvBatchRt.zeros_ok H₂ (o := a 6) CS (by omega) (by omega))
    fun u₃ ⟨H₃, O₃, A₃, K₃⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86.InvBatchRt.zeros_ok H₃ (o := a 7) CS (by omega) (by omega))
    fun u₄ ⟨H₄, O₄, B₄, K₄⟩ => ?_)
  refine WP.seq (ptr_ok H₄.ws H₄.slots hZ (r := .eax) (t := .edx) (x := a 7) (by decide) (by decide) (by decide)
    (by decide) (by intro e; cases e) (by omega) fun u₅ K₅ m₅ p₅ => ?_)
  refine wp_movS rfl fun u₆ V₆ _ => ?_
  have hw₆ := (H₄.ws.rt.of_keeps K₅).of_keeps V₆.keeps
  have p₆ : PtrAt u₆ B .eax (rv (kw len) (a 7)) := by rw [PtrAt, V₆.other _ (by decide)]; exact p₅
  have ea₆ : u₆.ea (at_ .eax 0) = off B (rv (kw len) (a 7)) := by simpa using ea_ptr hw₆ p₆ (d := 0) (by omega)
  refine wp_storeS ea₆ (ws_write hw₆ (by omega)) fun u₇ V₇ => WP.block_nil ?_
  have K₇ : Keeps [.eax, .ecx, .edx] u₄ u₇ := ((K₅.mono (by decide)).trans (V₆.keeps.mono (by decide))).trans
    (V₇.keeps _)
  have O₇ : Outside B (rv (kw len) (a 7)) 4 u₄.mem u₇.mem := by
    rw [V₇.mem, V₆.mem, m₅]; exact writeW32_outside _ _ _ (by omega)
  have H₇ : Bx L u₇ B Z len N := H₄.keep K₇ (by decide) (by decide) O₇ (by omega) (by omega)
  have W₇ : w32 u₇.mem B (rv (kw len) (a 7)) = 1 := by rw [V₇.mem, w32_write_self, V₆.gpr]; rfl
  -- The inverse word.
  refine WP.seq (ptr_ok H₇.ws H₇.slots hZ (r := .eax) (t := .edx) (x := a 2) (by decide) (by decide) (by decide)
    (by decide) (by intro e; cases e) (by omega) fun u₈ K₈ m₈ p₈ => ?_)
  have hw₈ := H₇.ws.rt.of_keeps K₈
  refine wp_movS (readSrc_ptr hw₈ p₈ (d := 0) (by omega)) fun u₉ V₉ _ => ?_
  -- `[2]` so far.
  have P₇ : val32 u₇.mem B (rv (kw len) (a 2)) (nw len) = virtualMod m := by
    rw [O₇.val32 (by omega) (by omega), O₄.val32 (by omega) (by omega), O₃.val32 (by omega) (by omega),
      O₂.val32 (by omega) (by omega), P₂]
  have low2 : w32 u₇.mem B (rv (kw len) (a 2)) % 2 = 1 := by
    obtain ⟨j, hj⟩ : ∃ j, nw len = j + 1 := ⟨nw len - 1, by omega⟩
    have := virtualMod_odd odd
    rw [← P₇, hj, val32] at this
    omega
  have odd₉ : (u₉.gpr .ebx).toNat % 2 = 1 := by rw [V₉.gpr, m₈, Nat.add_zero]; exact low2
  refine WP.block_append (WP.mono (VG.Proof.Mont.X86.Dynamic.inverse_ok u₉ odd₉) fun u₁₀ ⟨I₁₀, K₁₀, M₁₀⟩ => ?_)
  have K₁₀' : Keeps [.eax, .ebx, .ecx, .edx, .ebp] u₇ u₁₀ :=
    ((K₈.mono (by decide)).trans (V₉.keeps.mono (by decide))).trans (K₁₀.mono (by decide))
  have hs₁₀ := H₇.ws.ws.workspace.of_keeps K₁₀' (by decide)
  refine wp_storeS (hs₁₀.ea (by omega)) (hs₁₀.write (d := win + 28) (n := 4) (by omega)) fun u₁₁ V₁₁ =>
    WP.block_nil ?_
  have O₁₁ : Outside B (win + 28) 4 u₇.mem u₁₁.mem := by
    rw [V₁₁.mem, M₁₀, V₉.mem, m₈]; exact writeW32_outside _ _ _ (by omega)
  have H₁₁ : Bx L u₁₁ B Z len N := H₇.keepLow (K₁₀'.trans (V₁₁.keeps _)) (by decide) (by decide) O₁₁ (by decide)
  let iv := w32 u₁₁.mem B (win + 28)
  have inv : (virtualMod m * iv + 1) % 2 ^ 32 = 0 := by
    have e : iv = (u₁₀.gpr .eax).toNat := by
      show w32 u₁₁.mem B (win + 28) = _
      rw [V₁₁.mem, w32_write_self]
    have I : (w32 u₇.mem B (rv (kw len) (a 2)) * (u₁₀.gpr .eax).toNat + 1) % 2 ^ 32 = 0 := by
      rw [V₉.gpr, m₈, Nat.add_zero] at I₁₀; exact I₁₀
    have pm : virtualMod m % 2 ^ 32 = w32 u₇.mem B (rv (kw len) (a 2)) := by
      obtain ⟨j, hj⟩ : ∃ j, nw len = j + 1 := ⟨nw len - 1, by omega⟩
      rw [← P₇, hj, val32]
      have := (u₇.mem.readW (off B (rv (kw len) (a 2))) 32).isLt
      simp only [w32] at this ⊢
      omega
    have hp : virtualMod m = virtualMod m % 2 ^ 32 + 2 ^ 32 * (virtualMod m / 2 ^ 32) := (Nat.mod_add_div _ _).symm
    rw [hp, Nat.add_mul, Nat.mul_assoc, Nat.add_right_comm, Nat.add_mul_mod_self_left, pm, e]
    exact I
  -- The batch count.
  unfold batches
  refine nBytes_ok H₁₁.ws.ws.workspace H₁₁.slots hZ (by omega) (e := 1) (by decide) fun u₁₂ K₁₂ m₁₂ c₁₂ => ?_
  refine VG.Proof.Bignum.X86.PublicRt.wp_shr (by decide) fun u₁₃ V₁₃ => ?_
  refine wp_movS rfl fun u₁₄ V₁₄ _ => wp_addS rfl fun u₁₅ V₁₅ _ => wp_addS rfl fun u₁₆ V₁₆ _ => ?_
  have K₁₆ : Keeps [.eax, .ecx] u₁₁ u₁₆ :=
    ((((K₁₂.mono (by decide)).trans (V₁₃.keeps.mono (by decide))).trans (V₁₄.keeps.mono (by decide))).trans
      (V₁₅.keeps.mono (by decide))).trans (V₁₆.keeps.mono (by decide))
  have hs₁₆ := H₁₁.ws.ws.workspace.of_keeps K₁₆ (by decide)
  refine wp_storeS (hs₁₆.ea (by omega)) (hs₁₆.write (d := 100) (n := 4) (by omega)) fun z Vz => WP.block_nil ?_
  have m₁₆ : u₁₆.mem = u₁₁.mem := by rw [V₁₆.mem, V₁₅.mem, V₁₄.mem, V₁₃.mem, m₁₂]
  have Oz : Outside B 100 4 u₁₁.mem z.mem := by rw [Vz.mem, m₁₆]; exact writeW32_outside _ _ _ (by omega)
  have Hz : Bx L z B Z len N := H₁₁.keepHigh (K₁₆.trans (Vz.keeps _)) (by decide) (by decide) Oz (by decide)
    (by omega)
  have count : w32 z.mem B 100 = 3 * (nw len + 1) := by
    rw [Vz.mem, w32_write_self, V₁₆.gpr, V₁₅.gpr, V₁₅.other .ecx (by decide), V₁₄.gpr, V₁₄.other _ (by decide),
      V₁₃.gpr]
    have e₁₂ : (u₁₂.gpr .eax).toNat = 4 * (nw len + 1) := by rw [c₁₂]; omega
    have e₁₃ : (u₁₂.gpr .eax >>> 2).toNat = nw len + 1 := by
      rw [BitVec.toNat_ushiftRight, e₁₂, Nat.shiftRight_eq_div_pow]; omega
    simp only [BitVec.toNat_add, e₁₃]
    omega
  -- The frames back to `u`, after the operands.
  have Fz : ∀ y, (ofs B y < win ∨ win + 88 ≤ ofs B y) → (ofs B y < rv (kw len) (a 6) ∨
      rv (kw len) (a 6) + 2 * (8 * nw len + 8) ≤ ofs B y) → z.mem y = u.mem y := by
    intro y h1 h2
    rw [Oz y (by omega), O₁₁ y (by omega), O₇ y (by omega), O₄ y (by omega), O₃ y (by omega), O₂ y (by omega)]
  have val_z : ∀ d k, (d + 4 * k ≤ win ∨ win + 88 ≤ d) → (d + 4 * k ≤ rv (kw len) (a 6) ∨
      rv (kw len) (a 6) + 2 * (8 * nw len + 8) ≤ d) → d + 4 * k ≤ Z → val32 z.mem B d k = val32 u.mem B d k :=
    fun d k h1 h2 h3 => val32_congr fun j hj => congrArg BitVec.toNat (Mem.readW_congr fun i hi => Fz _
      (by rw [ofs_off B (by omega)]; omega) (by rw [ofs_off B (by omega)]; omega))
  -- The coefficients at the end.
  have A₄ : val32 u₄.mem B (rv (kw len) (a 6)) (nw len + 1) = 0 := by rw [O₄.val32 (by omega) (by omega), A₃]
  have Az : val32 z.mem B (rv (kw len) (a 6)) (nw len + 1) = 0 := by
    rw [Oz.val32 (by omega) (by omega), O₁₁.val32 (by omega) (by omega), O₇.val32 (by omega) (by omega), A₄]
  have Bz : val32 z.mem B (rv (kw len) (a 7)) (nw len + 1) = 1 := by
    rw [Oz.val32 (by omega) (by omega), O₁₁.val32 (by omega) (by omega), val32, W₇,
      O₇.val32 (d := rv (kw len) (a 7) + 4) (by omega) (by omega)]
    have := B₄
    rw [val32] at this
    omega
  have split (mm : Mem) (d : Nat) : val32 mm B d (nw len + 1) = val32 mm B d (nw len) + 2 ^ (32 * nw len) *
      w32 mm B (d + 4 * nw len) := val32_succ _ _ _ _
  have pos := Nat.two_pow_pos (32 * nw len)
  have zeroTop {d : Nat} {v : Nat} (hv : val32 z.mem B d (nw len + 1) = v) (hv1 : v ≤ 1) :
      val32 z.mem B d (nw len) = v ∧ w32 z.mem B (d + 4 * nw len) = 0 := by
    rw [split] at hv
    rcases Nat.eq_zero_or_pos (w32 z.mem B (d + 4 * nw len)) with e | e
    · rw [e, Nat.mul_zero, Nat.add_zero] at hv; exact ⟨hv, e⟩
    · have := Nat.mul_le_mul_left (2 ^ (32 * nw len)) e
      have : 2 ≤ 2 ^ (32 * nw len) := Nat.pow_le_pow_right (n := 2) (by decide) (show 1 ≤ 32 * nw len by omega)
      omega
  obtain ⟨Al, At⟩ := zeroTop Az (by decide)
  obtain ⟨Bl, Bt⟩ := zeroTop Bz (by decide)
  have rmo : rv (kw len) mo = rv (kw len) (a 2) := rfl
  have r4 := rv_a len 4; have r5 := rv_a len 5
  have Dz : z.mem.readW (off B win) 32 = 1 := by
    apply BitVec.eq_of_toNat_eq
    change w32 z.mem B win = (1 : BitVec 32).toNat
    rw [Oz.w32 (by omega) (by omega), O₁₁.w32 (by omega) (by omega), O₇.w32 (by omega) (by omega),
      O₄.w32 (by omega) (by omega), O₃.w32 (by omega) (by omega)]
    exact congrArg BitVec.toNat D₂
  refine ⟨iv, Hz, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, At, Bt⟩, inv, count, ?_, ?_⟩
  · rw [Dz]; rfl
  · rw [rmo, val_z _ _ (by omega) (by omega) (by omega), P₂]
  · exact Oz.w32 (by omega) (by omega)
  · rw [val_z _ _ (by omega) (by omega) (by omega), F₄]; rfl
  · rw [val_z _ _ (by omega) (by omega) (by omega), G₅]; rfl
  · rw [Al]; rfl
  · rw [Bl]; rfl
  · exact ((((((((K₀.mono (by decide)).trans Ku).trans ((V₁.keeps.trans (V₂.keeps _)).mono (by decide))).trans
      (K₃.mono (by decide))).trans (K₄.mono (by decide))).trans (K₇.mono (by decide))).trans
      ((K₁₀'.trans (V₁₁.keeps _)).mono (by decide))).trans ((K₁₆.trans (Vz.keeps _)).mono (by decide)))
  · intro y hy
    have h1 := hy (win, 88) (by simp [initWrites])
    have h2 := hy (rv (kw len) (a 2), 6 * (8 * nw len + 8)) (by simp [initWrites])
    have h3 := hy (rv (kw len) (a 12), 8 * nw len + 8) (by simp [initWrites])
    rw [Fz y (by omega) (by omega), Uu y (by
      intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> simp only <;> omega), O₀ y (by omega)]
