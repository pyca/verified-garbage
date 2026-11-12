module

public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.FBatchStep
public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.FScatter
public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Init
import VerifiedGarbage.Proof.Rsa.X86.GcdBatch.InitWords
import VerifiedGarbage.Proof.Mont.X86.Inverse
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Ptr
import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Red
import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Arrays
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Tactic.Linarith
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Power

-- separate module: builds in parallel with the end (`FFinish`)

/-! # The fused batches on i686: the start

`operandsF_ok`: the virtual modulus `p` into `[2]` (`n + 1` words) and `g = oddInput p x` into
`[7]`; `initF_ok`: then the interleaved state of no batches, the inverse word and the count.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.InvBatchRt.F

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Impl.Rsa.X86.InvBatchRt
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Rsa.X86.KeyRt VG.Proof.Weierstrass
open VG.Proof.Weierstrass.X86.Inv (wordClob)
open VG.Proof.Rsa.X86.InvBatchRt
open VG.Proof.Rsa.Divstep (oddInput)

variable {L : Lay} {B : Addr} {Z len N : Nat}

/-- The operands: `[2] = p` and `[7] = oddInput p x`, `n + 1` words each. -/
theorem operandsF_ok {s : State} (h : Bx L s B Z len N) (hn2 : 2 ≤ nw len) {m x : Nat}
    (hm : val32 s.mem B (rv (kw len) (a 8)) (nw len) = m) (hx : val32 s.mem B (rv (kw len) (a 0)) (nw len) = x)
    {rest : Prog isa} {Q : State → Prop}
    (k : ∀ u, Bx L u B Z len N → val32 u.mem B (rv (kw len) (a 2)) (nw len + 1) = virtualMod m →
      val32 u.mem B (rv (kw len) (a 7)) (nw len + 1) = oddInput (virtualMod m) x →
      Keeps wordClob s u →
      Unch B [(rv (kw len) (a 2), 6 * (8 * nw len + 8)), (rv (kw len) (a 12), 8 * nw len + 8)] s.mem u.mem →
      WP isa rest u Q) :
    WP isa (.seq (VG.Impl.Rsa.X86.InvBatchRt.copy L (a 2) (a 8) (nBytes .edi 0)) <|
      .seq (virtualize L) <|
      .seq (.block (zeroWord L { arr := 2, half := 1 })) <|
      .seq (VG.Impl.Rsa.X86.InvBatchRt.copy L (a 7) (a 0) (nBytes .edi 0)) <|
      .seq (.block (zeroWord L { arr := 7, half := 1 })) <|
      .seq (VG.Impl.Rsa.X86.InvBatchRt.zeros L (a 12) (nBytes .ecx 1)) <|
      .seq (.block (VG.Impl.Rsa.X86.GcdBatch.evenMask (VG.Impl.Rsa.X86.InvBatchRt.offset 0 0))) <|
      .seq (selIn L (a 12) (a 2) (nBytes .edi 0)) <|
      .seq (VG.Impl.Rsa.X86.InvBatchRt.chain L .adc (a 7) (a 7) (a 12) (nBytes .edx 1)) rest) s Q := by
  have hn := h.nowrap
  have hZ := h.halfZ
  have hf16 := h.fits16
  have hpos := h.ws.kw_pos
  have hw := kw_bound h.ws.lenLe
  have ke := kw_eq len
  have r0 := rv_a len 0; have r2 := rv_a len 2; have r7 := rv_a len 7
  have r8 := rv_a len 8; have r12 := rv_a len 12
  have h21 := rv_half1' len 2; have h71 := rv_half1' len 7
  have hS : 0 < 8 * nw len + 8 := by omega
  have CS : CountSpec (nBytes .ecx 1) .ecx B Z (kw len) (nw len + 1) := by
    have := nBytes_spec (r := .ecx) (e := 1) (B := B) hZ (w := kw len) (by omega) (by decide) (by omega)
    rwa [show kw len / 2 + 1 = nw len + 1 by omega] at this
  -- `[2] = m`, then `p`, its word `n` zero.
  refine WP.seq (WP.mono (copy_ok h (o := a 2) (a := a 8) (e := 0) (by decide) (by omega) (by omega) (by omega))
    fun s₁ ⟨H₁, O₁, V₁, K₁⟩ => ?_)
  simp only [Nat.add_zero] at O₁ V₁
  rw [hm] at V₁
  refine WP.seq (WP.mono (virtualize_ok H₁ hn2) fun s₂ ⟨H₂, V₂, K₂, O₂⟩ => ?_)
  rw [V₁] at V₂
  change val32 s₂.mem B (rv (kw len) (a 2)) (nw len) = virtualMod m at V₂
  have X₂ : val32 s₂.mem B (rv (kw len) (a 0)) (nw len) = x := by
    rw [O₂.val32 (by omega) (by omega), O₁.val32 (by omega) (by omega), hx]
  refine WP.seq (zeroWord_ok H₂ (x := { arr := 2, half := 1 }) (by omega) fun s₃ H₃ K₃ O₃ z₃ => WP.block_nil ?_)
  rw [h21] at O₃ z₃
  have P₃ : val32 s₃.mem B (rv (kw len) (a 2)) (nw len + 1) = virtualMod m := by
    rw [val32_succ, z₃, Nat.mul_zero, Nat.add_zero, O₃.val32 (by omega) (by omega), V₂]
  -- `[7] = x`.
  refine WP.seq (WP.mono (copy_ok H₃ (o := a 7) (a := a 0) (e := 0) (by decide) (by omega) (by omega) (by omega))
    fun s₅ ⟨H₅, O₅, V₅, K₅⟩ => ?_)
  simp only [Nat.add_zero] at O₅ V₅
  rw [O₃.val32 (by omega) (by omega), X₂] at V₅
  refine WP.seq (zeroWord_ok H₅ (x := { arr := 7, half := 1 }) (by omega) fun s₆ H₆ K₆ O₆ z₆ => WP.block_nil ?_)
  rw [h71] at O₆ z₆
  have G₆ : val32 s₆.mem B (rv (kw len) (a 7)) (nw len + 1) = x := by
    rw [val32_succ, z₆, Nat.mul_zero, Nat.add_zero, O₆.val32 (by omega) (by omega), V₅]
  -- `[12] = 0`, then `p` where `x` is even.
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86.InvBatchRt.zeros_ok H₆ (o := a 12) CS (by omega) (by omega))
    fun s₇ ⟨H₇, O₇, V₇, K₇⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86.GcdBatch.evenMask_ok H₇.ws.ws.workspace
    (src := VG.Impl.Rsa.X86.InvBatchRt.offset 0 0) (by simp only [VG.Impl.Rsa.X86.InvBatchRt.offset]; omega))
    fun s₈ ⟨C₈, K₈, m₈⟩ => ?_)
  have H₈ : Bx L s₈ B Z len N := H₇.keep K₈ (by decide) (by decide) (o := 160) (c := 0)
    (by rw [m₈]; exact Outside.refl _ _ _ _) (Nat.le_refl _) (by omega)
  have o00 : VG.Impl.Rsa.X86.InvBatchRt.offset 0 0 = rv (kw len) (a 0) := by
    simp only [VG.Impl.Rsa.X86.InvBatchRt.offset]; omega
  rw [o00, O₇.w32 (by omega) (by omega), O₆.w32 (by omega) (by omega), O₅.w32 (by omega) (by omega),
    O₃.w32 (by omega) (by omega), O₂.w32 (by omega) (by omega), O₁.w32 (by omega) (by omega)] at C₈
  have even : x % 2 = w32 s.mem B (rv (kw len) (a 0)) % 2 := by
    obtain ⟨j, hj⟩ : ∃ j, nw len = j + 1 := ⟨nw len - 1, by omega⟩
    rw [← hx, hj, val32]
    omega
  refine WP.seq (WP.mono (selIn_ok H₈ (o := a 12) (a := a 2) (e := 0) (k := decide (x % 2 = 0))
    (by rw [C₈, even]; by_cases he : w32 s.mem B (rv (kw len) (a 0)) % 2 = 0 <;> simp [he, cmask])
    (by decide) (by omega) (by omega) (by omega)) fun s₉ ⟨H₉, O₉, V₉, K₉⟩ => ?_)
  simp only [Nat.add_zero] at O₉ V₉
  rw [m₈, O₇.val32 (d := rv (kw len) (a 2)) (by omega) (by omega), O₆.val32 (by omega) (by omega),
    O₅.val32 (by omega) (by omega), O₃.val32 (by omega) (by omega), V₂] at V₉
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
  -- `[7] += [12]`.
  refine WP.seq (WP.mono (chainAdd_ok H₉ (o := a 7) (a := a 7) (b := a 12) (e := 1) (by decide) rfl
    (by omega) (by omega) (by omega) (.inl (Nat.le_refl _)) (by omega)) fun u ⟨Hu, Ou, ⟨c, _, Vu⟩, Ku⟩ => ?_)
  have G₉ : val32 s₉.mem B (rv (kw len) (a 7)) (nw len + 1) = x := by
    rw [O₉.val32 (by omega) (by omega), m₈, O₇.val32 (by omega) (by omega), G₆]
  rw [G₉, T₉] at Vu
  have pv : virtualMod m < 2 ^ (32 * nw len) := V₂ ▸ val32_lt _ _ _ _
  have xv : x < 2 ^ (32 * nw len) := hx ▸ val32_lt _ _ _ _
  have sum : x + (if x % 2 = 0 then virtualMod m else 0) < 2 ^ (32 * (nw len + 1)) := by
    rw [pow32_succ]; split <;> omega
  have Gu : val32 u.mem B (rv (kw len) (a 7)) (nw len + 1) = oddInput (virtualMod m) x := by
    unfold oddInput
    cases c <;> simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one, Nat.add_zero] at Vu <;>
      omega
  refine k u Hu ?_ Gu ?_ ?_
  · rw [Ou.val32 (by omega) (by omega), O₉.val32 (by omega) (by omega), m₈, O₇.val32 (by omega) (by omega),
      O₆.val32 (by omega) (by omega), O₅.val32 (by omega) (by omega), P₃]
  · exact (((((((K₁.mono (by decide)).trans K₂).trans (K₃.mono (by decide))).trans
      (K₅.mono (by decide))).trans (K₆.mono (by decide))).trans (K₇.mono (by decide))).trans
      ((K₈.mono (by decide)).trans (K₉.mono (by decide)))).trans (Ku.mono (by decide))
  · intro y hy
    have hA := hy (rv (kw len) (a 2), 6 * (8 * nw len + 8)) (by simp)
    have hT := hy (rv (kw len) (a 12), 8 * nw len + 8) (by simp)
    rw [Ou y (by omega), O₉ y (by omega), m₈, O₇ y (by omega), O₆ y (by omega), O₅ y (by omega),
      O₃ y (by omega), O₂ y (by omega), O₁ y (by omega)]

/-! ## The small blocks of the start -/


/-- `delta = 1`. -/
theorem winOne_ok {s : State} (h : Bx L s B Z len N) :
    WP isa (.block [.mov .eax (.imm 1), .store (sc win) .eax]) s fun t =>
      Bx L t B Z len N ∧ t.mem = s.mem.writeW (off B win) (1 : BitVec 32) ∧ Keeps [.eax] s t := by
  have hZ := h.halfZ
  have e16 : win = 16 := rfl; have e96 : halfSlot = 96 := rfl
  refine wp_movS rfl fun u₁ V₁ _ => ?_
  have hs₁ := h.ws.ws.workspace.of_keeps V₁.keeps (by decide)
  refine wp_storeS (hs₁.ea (by omega)) (hs₁.write (d := win) (n := 4) (by omega))
    fun u₂ V₂ => WP.block_nil ?_
  have m₂ : u₂.mem = s.mem.writeW (off B win) (1 : BitVec 32) := by rw [V₂.mem, V₁.mem, V₁.gpr]
  have K₂ : Keeps [.eax] s u₂ := V₁.keeps.trans (V₂.keeps _)
  have Om : Outside B win 4 s.mem u₂.mem := by rw [m₂]; exact writeW32_outside _ _ _ (by omega)
  exact ⟨h.keepLow K₂ (by decide) (by decide) Om (by decide), m₂, K₂⟩

/-- The inverse word, from `[2]`'s low word. -/
theorem invF_ok {s : State} (h : Bx L s B Z len N) (odd : w32 s.mem B (rv (kw len) (a 2)) % 2 = 1) :
    WP isa (.block (ptr L .eax (a 2) .edx ++ ([.mov .ebx (.mem (at_ .eax 0))] : List Instr) ++ VG.Impl.Mont.X86.Dynamic.inverse ++
      ([.store (sc (win + 28)) .eax] : List Instr))) s fun t => ∃ V : BitVec 32,
      Bx L t B Z len N ∧ t.mem = s.mem.writeW (off B (win + 28)) V ∧
      (w32 s.mem B (rv (kw len) (a 2)) * V.toNat + 1) % 2 ^ 32 = 0 ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  have hn := h.nowrap
  have hZ := h.halfZ
  have hf16 := h.fits16
  have r2 := rv_a len 2
  simp only [List.append_assoc]
  refine ptr_ok h.ws h.slots hZ (r := .eax) (t := .edx) (x := a 2) (by decide) (by decide) (by decide)
    (by decide) (by intro e; cases e) (by omega) fun u₈ K₈ m₈ p₈ => ?_
  have hw₈ := h.ws.rt.of_keeps K₈
  rw [List.singleton_append]
  refine wp_movS (readSrc_ptr hw₈ p₈ (d := 0) (by omega)) fun u₉ V₉ _ => ?_
  have odd₉ : (u₉.gpr .ebx).toNat % 2 = 1 := by rw [V₉.gpr, m₈, Nat.add_zero]; exact odd
  refine WP.block_append (WP.mono (VG.Proof.Mont.X86.Dynamic.inverse_ok u₉ odd₉) fun u₁₀ ⟨I₁₀, K₁₀, M₁₀⟩ => ?_)
  have K₁₀' : Keeps [.eax, .ebx, .ecx, .edx, .ebp] s u₁₀ :=
    ((K₈.mono (by decide)).trans (V₉.keeps.mono (by decide))).trans (K₁₀.mono (by decide))
  have hs₁₀ := h.ws.ws.workspace.of_keeps K₁₀' (by decide)
  have e16 : win = 16 := rfl
  refine wp_storeS (hs₁₀.ea (by omega)) (hs₁₀.write (d := win + 28) (n := 4) (by omega))
    fun u₁₁ V₁₁ => WP.block_nil ?_
  have m₁₁ : u₁₁.mem = s.mem.writeW (off B (win + 28)) (u₁₀.gpr .eax) := by rw [V₁₁.mem, M₁₀, V₉.mem, m₈]
  have K₁₁ := K₁₀'.trans (V₁₁.keeps _)
  have Om : Outside B (win + 28) 4 s.mem u₁₁.mem := by rw [m₁₁]; exact writeW32_outside _ _ _ (by omega)
  refine ⟨u₁₀.gpr .eax, h.keepLow K₁₁ (by decide) (by decide) Om (by decide), m₁₁, ?_, K₁₁⟩
  rw [V₉.gpr, m₈, Nat.add_zero] at I₁₀; exact I₁₀


/-! ## Words that stay, again -/

/-- Through a write apart from the elements. -/
theorem Same.apart {o c : Nat} {m m' : Mem} (h : Outside B o c m m') {A1 sz' x n : Nat} (hx : x + 4 ≤ sz')
    (hfar : A1 + sz' * (n + 2) ≤ o ∨ o + c ≤ A1) (hb : A1 + sz' * (n + 2) ≤ 2 ^ 32) :
    Same B (A1 + sz' + x) sz' (n + 1) m m' :=
  Same.of_unch h.unch (fun w hw r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    have := mul_step (sz := sz') (show w + 1 < n + 2 by omega); rw [elem_of]
    rcases hfar with h | h
    · exact .inl (by omega)
    · exact .inr (by omega))
    fun w hw => by have := mul_step (sz := sz') (show w + 1 < n + 2 by omega); rw [elem_of]; omega

/-- A number's words through a write apart from them. -/
theorem Same.ctg_out {o c : Nat} {m m' : Mem} (h : Outside B o c m m') {b K : Nat}
    (hb : b + 4 * K ≤ o ∨ o + c ≤ b) (hb' : b + 4 * K ≤ 2 ^ 32) : Same B b 4 K m m' :=
  Same.of_unch h.unch (fun w hw r hr => by
    simp only [List.mem_singleton] at hr; subst hr; omega) fun w hw => by omega

/-- A number's words through a row apart from them. -/
theorem Same.ctg_row {A0 sz o n : Nat} {m m' : Mem} (h : RowWr B A0 sz o n m m') (ho : o + 4 ≤ sz) {b K : Nat}
    (hb : b + 4 * K ≤ A0 ∨ A0 + sz * (n + 2) ≤ b) (hp : b + 4 * K ≤ sP ∨ sP + 8 ≤ b) (hb' : b + 4 * K ≤ 2 ^ 32) :
    Same B b 4 K m m' :=
  Same.of_row h ho fun w hw => ⟨by rcases hb with h | h <;> [exact .inl (by omega); exact .inr (.inl (by omega))],
    by rcases hp with h | h <;> [exact .inl (by omega); exact .inr (by omega)], by omega⟩

theorem sval_nat {m : Mem} {W : Addr} {b sz n v : Nat} (h : sv m W b sz (n + 1) = v)
    (hv : v < 2 ^ (32 * n) * 2 ^ 31) : sval m W b sz n = v := by
  have hM : (0 : Int) < 2 ^ (32 * (n + 1)) := two_pow_pos' _
  have e : (2 : Int) ^ (32 * (n + 1)) = 2 ^ (32 * n) * 2 ^ 32 := by
    rw [show 32 * (n + 1) = 32 * n + 32 by omega, pow_add]
  have hK : (0 : Int) < 2 ^ (32 * n) := two_pow_pos' _
  have hvI : (v : Int) < 2 ^ (32 * n) * 2 ^ 31 := by exact_mod_cast hv
  refine sval_of_mod (X := v) ?_ (by omega) hvI
  rw [h, Int.emod_eq_of_lt (by omega) (by rw [e]; nlinarith)]; rfl

/-! ## The start -/

theorem initF_ok {s : State} (h : RtWs L s B Z len N) (room : 16 ≤ N) (hn2 : 2 ≤ nw len) {m x : Nat}
    (hm : val32 s.mem B (rv (kw len) (a 8)) (nw len) = m) (hx : val32 s.mem B (rv (kw len) (a 0)) (nw len) = x)
    (odd : m % 2 = 1) :
    WP isa (initF L) s fun z => ∃ iv, Bx L z B Z len N ∧ RunAt len B (virtualMod m) iv x 0 0 z ∧
      (virtualMod m * iv + 1) % 2 ^ 32 = 0 ∧ VG.Proof.Mont.w32 z.mem B 100 = (3 * nw len + 2) / 2 ∧
      val32 z.mem B (rv (kw len) (a 2)) (nw len + 1) = virtualMod m ∧
      Keeps wordClob s z ∧ Unch B (bodyWrites len) s.mem z.mem := by
  have hn := h.ws.workspace.nowrap
  have hw := kw_bound h.lenLe
  have ke := kw_eq len
  unfold initF
  simp only [VG.Impl.Rsa.X86.Keys.seqs]
  rw [show slots L = slots L ++ [] from (List.append_nil _).symm]
  refine WP.seq (slots_ok h room fun s₀ H₀ K₀ O₀ => WP.block_nil ?_)
  have hZ := H₀.halfZ
  have hf16 := H₀.fits16
  have r0 := rv_a len 0; have r2 := rv_a len 2; have r3 := rv_a len 3; have r7 := rv_a len 7
  have r8 := rv_a len 8
  have hAF : rv (kw len) { arr := fgArr } = 160 + 4 * (8 * nw len + 8) := rv_a len 4
  have hAD : rv (kw len) { arr := deArr } = 160 + 11 * (8 * nw len + 8) := rv_a len 11
  have efs : fgSz = 16 := rfl; have eds : deSz = 20 := rfl; have eP : sP = 176 := rfl
  have e16 : win = 16 := rfl; have e52 : slotBase = 52 := rfl
  have hm₀ : val32 s₀.mem B (rv (kw len) (a 8)) (nw len) = m := by rw [O₀.val32 (by omega) (by omega), hm]
  have hx₀ : val32 s₀.mem B (rv (kw len) (a 0)) (nw len) = x := by rw [O₀.val32 (by omega) (by omega), hx]
  refine operandsF_ok H₀ hn2 hm₀ hx₀ fun u Hu P₂ G₇ Ku Uu => ?_
  have CS : CountSpec (nBytes .ecx 1) .ecx B Z (kw len) (nw len + 1) := by
    have := nBytes_spec (r := .ecx) (e := 1) (B := B) hZ (w := kw len) (by omega) (by decide) (by omega)
    rwa [show kw len / 2 + 1 = nw len + 1 by omega] at this
  have b32 : B.toNat + Z ≤ 2 ^ 32 := hn
  have fitF : rv (kw len) { arr := fgArr } + fgSz * (nw len + 2) ≤ 2 ^ 32 := by rw [efs]; omega
  have fitD : rv (kw len) { arr := deArr } + deSz * (nw len + 2) ≤ 2 ^ 32 := by rw [eds]; omega
  -- `f, g`.
  refine WP.seq (WP.mono (scatter_ok Hu (arr := fgArr) (sz := fgSz) (x := 0) (src := a 2) (by decide)
    (by rw [efs]; omega) (by omega) (by omega) (.inl (by omega))) fun s₁ ⟨H₁, R₁, V₁, K₁⟩ => ?_)
  have Q₂₁ : Same B (rv (kw len) (a 7)) 4 (nw len + 1) u.mem s₁.mem :=
    Same.ctg_row R₁ (by decide) (.inr (by rw [efs]; omega)) (.inr (by omega)) (by omega)
  refine WP.seq (WP.mono (scatter_ok H₁ (arr := fgArr) (sz := fgSz) (x := 4) (src := a 7) (by decide)
    (by rw [efs]; omega) (by omega) (by omega) (.inr (by rw [efs]; omega))) fun s₂ ⟨H₂, R₂, V₂, K₂⟩ => ?_)
  rw [val32_sv, Q₂₁.sv, ← val32_sv, G₇] at V₂
  rw [P₂] at V₁
  -- `d, e, p`.
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86.InvBatchRt.zeros_ok H₂ (o := a 3) CS (by omega) (by omega))
    fun s₃ ⟨H₃, O₃, Z₃, K₃⟩ => ?_)
  refine WP.seq (WP.mono (scatter_ok H₃ (arr := deArr) (sz := deSz) (x := 0) (src := a 3) (by decide)
    (by rw [eds]; omega) (by omega) (by omega) (.inl (by omega))) fun s₄ ⟨H₄, R₄, V₄, K₄⟩ => ?_)
  rw [Z₃] at V₄
  have Q₃₄ : Same B (rv (kw len) (a 3)) 4 (nw len + 1) s₃.mem s₄.mem :=
    Same.ctg_row R₄ (by decide) (.inl (by omega)) (.inr (by omega)) (by omega)
  refine WP.seq (WP.mono (scatter_ok H₄ (arr := deArr) (sz := deSz) (x := 4) (src := a 3) (by decide)
    (by rw [eds]; omega) (by omega) (by omega) (.inl (by omega))) fun s₅ ⟨H₅, R₅, V₅, K₅⟩ => ?_)
  rw [val32_sv, Q₃₄.sv, ← val32_sv, Z₃] at V₅
  have Q₂ : Same B (rv (kw len) (a 2)) 4 (nw len + 1) u.mem s₅.mem :=
    ((((Same.ctg_row R₁ (by decide) (.inl (by omega)) (.inr (by omega)) (by omega)).trans
      (Same.ctg_row R₂ (by decide) (.inl (by omega)) (.inr (by omega)) (by omega))).trans
      (Same.ctg_out O₃ (.inl (by omega)) (by omega))).trans
      (Same.ctg_row R₄ (by decide) (.inl (by omega)) (.inr (by omega)) (by omega))).trans
      (Same.ctg_row R₅ (by decide) (.inl (by omega)) (.inr (by omega)) (by omega))
  refine WP.seq (WP.mono (scatter_ok H₅ (arr := deArr) (sz := deSz) (x := 16) (src := a 2) (by decide)
    (by rw [eds]; omega) (by omega) (by omega) (.inl (by omega))) fun s₆ ⟨H₆, R₆, V₆, K₆⟩ => ?_)
  rw [val32_sv, Q₂.sv, ← val32_sv, P₂] at V₆
  -- `e`'s low word, `delta`, the inverse word, the count.
  refine WP.seq (WP.mono (eOne_ok H₆) fun s₇ ⟨H₇, m₇, K₇⟩ => ?_)
  refine WP.seq (WP.mono (winOne_ok H₇) fun s₈ ⟨H₈, m₈, K₈⟩ => ?_)
  have hde0 : de0 len = rv (kw len) { arr := deArr } + deSz := by simp only [de0, rv]; omega
  have O₇ : Outside B (de0 len + 4) 4 s₆.mem s₇.mem := by
    rw [m₇]; exact writeW32_outside _ _ _ (by rw [hde0]; omega)
  have O₈ : Outside B win 4 s₇.mem s₈.mem := by rw [m₈]; exact writeW32_outside _ _ _ (by omega)
  have Q₂' : Same B (rv (kw len) (a 2)) 4 (nw len + 1) u.mem s₈.mem :=
    ((Q₂.trans (Same.ctg_row R₆ (by decide) (.inl (by omega)) (.inr (by omega)) (by omega))).trans
      (Same.ctg_out O₇ (.inl (by rw [hde0]; omega)) (by omega))).trans (Same.ctg_out O₈ (.inr (by omega)) (by omega))
  have low : w32 s₈.mem B (rv (kw len) (a 2)) % 2 = 1 := by
    have := virtualMod_odd odd
    have e := Q₂' 0 (by omega)
    simp only [Nat.mul_zero, Nat.add_zero] at e
    rw [e]
    obtain ⟨j, hj⟩ : ∃ j, nw len = j + 1 := ⟨nw len - 1, by omega⟩
    rw [← P₂, hj, val32] at this; omega
  refine WP.seq (WP.mono (invF_ok H₈ low) fun s₉ ⟨V, H₉, m₉, I₉, K₉⟩ => ?_)
  refine WP.mono (countF_ok H₉) fun z ⟨Hz, mz, Kz⟩ => ?_
  have O₉ : Outside B (win + 28) 4 s₈.mem s₉.mem := by rw [m₉]; exact writeW32_outside _ _ _ (by omega)
  have Oz : Outside B 100 4 s₉.mem z.mem := by rw [mz]; exact writeW32_outside _ _ _ (by omega)
  have pv : virtualMod m < 2 ^ (32 * nw len) := by
    have mp : m < 2 ^ (32 * nw len) := hm ▸ val32_lt _ _ _ _
    have four : 4 ≤ 2 ^ (32 * nw len) := Nat.pow_le_pow_right (n := 2) (by decide) (show 2 ≤ 32 * nw len by omega)
    simp only [virtualMod]; split <;> omega
  have big : (2 : Nat) ^ (32 * nw len) ≤ 2 ^ (32 * nw len) * 2 ^ 31 := Nat.le_mul_of_pos_right _ (by decide)
  have xv : x < 2 ^ (32 * nw len) := hx ▸ val32_lt _ _ _ _
  have ox : oddInput (virtualMod m) x < 2 ^ (32 * nw len) * 2 ^ 31 := by
    unfold oddInput
    have : 2 * 2 ^ (32 * nw len) ≤ 2 ^ (32 * nw len) * 2 ^ 31 := by
      rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ (by decide)
    split <;> omega
  -- The frames after each write.
  have below : ∀ {o c : Nat} {m₁ m₂ : Mem}, Outside B o c m₁ m₂ → o + c ≤ 104 → ∀ {A1 sz' x' : Nat},
      x' + 4 ≤ sz' → 104 ≤ A1 → A1 + sz' * (nw len + 2) ≤ 2 ^ 32 → Same B (A1 + sz' + x') sz' (nw len + 1) m₁ m₂ :=
    fun O hc _ _ _ hx' hA hb => Same.apart O hx' (.inr (by omega)) hb
  have tailF : ∀ {x' : Nat}, x' + 4 ≤ fgSz → Same B (rv (kw len) { arr := fgArr } + fgSz + x') fgSz (nw len + 1) s₃.mem z.mem :=
    fun hx' => ((((((Same.row_far R₄ (by decide) hx' (.inl (by first | (rw [efs]; omega) | omega)) (by omega) fitF).trans
      (Same.row_far R₅ (by decide) hx' (.inl (by first | (rw [efs]; omega) | omega)) (by omega) fitF)).trans
      (Same.row_far R₆ (by decide) hx' (.inl (by first | (rw [efs]; omega) | omega)) (by omega) fitF)).trans
      (Same.apart O₇ hx' (.inl (by rw [hde0]; first | (rw [efs]; omega) | omega)) fitF)).trans
      (below O₈ (by omega) hx' (by omega) fitF)).trans (below O₉ (by omega) hx' (by omega) fitF)).trans
      (below Oz (by omega) hx' (by omega) fitF)
  have tailD : ∀ {x' : Nat}, x' + 4 ≤ deSz → Same B (rv (kw len) { arr := deArr } + deSz + x') deSz (nw len + 1) s₇.mem z.mem :=
    fun hx' => ((below O₈ (by omega) hx' (by omega) fitD).trans (below O₉ (by omega) hx' (by omega) fitD)).trans
      (below Oz (by omega) hx' (by omega) fitD)
  -- `e`'s words.
  have e₆ : sv s₆.mem B (rv (kw len) { arr := deArr } + deSz + 4) deSz (nw len + 1) = 0 := by
    rw [(Same.row_slot R₆ (by decide) (by decide) (.inl (by decide)) (by omega) fitD).sv]; rw [V₅]
  have e₇ : sv s₇.mem B (rv (kw len) { arr := deArr } + deSz + 4) deSz (nw len + 1) = 1 := by
    rw [sv_cons] at e₆ ⊢
    have hrest : sv s₇.mem B (rv (kw len) { arr := deArr } + deSz + 4 + deSz) deSz (nw len) =
        sv s₆.mem B (rv (kw len) { arr := deArr } + deSz + 4 + deSz) deSz (nw len) :=
      Same.sv (Same.of_unch O₇.unch (fun w hw r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [hde0, eds]; omega) fun w hw => by
          have := mul_step (sz := deSz) (show w + 2 < nw len + 2 by omega); rw [eds] at *; omega)
    have h1 : VG.Proof.Mont.w32 s₇.mem B (rv (kw len) { arr := deArr } + deSz + 4) = 1 := by
      rw [m₇, ← hde0, w32_write_self]; rfl
    rw [hrest, h1]; omega
  refine ⟨(V.toNat), Hz, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · show z.mem.readW (off B win) 32 = BitVec.ofInt 32 1
    rw [hdr_out Oz (.inl (by omega)) (by omega), hdr_out O₉ (.inl (by omega)) (by omega), m₈,
      Mem.readW_writeW_self32]; rfl
  · rw [Oz.w32 (.inl (by omega)) (by omega), m₉, w32_write_self]
  · show sval z.mem B _ fgSz (nw len) = (virtualMod m : Int)
    rw [((Same.row_slot R₂ (by decide) (by decide) (.inl (by decide)) (by omega) fitF).trans
      ((Same.apart O₃ (by decide) (.inr (by omega)) fitF).trans (tailF (by decide)))).sval_eq]
    exact sval_nat V₁ (by omega)
  · show sval z.mem B _ fgSz (nw len) = (oddInput (virtualMod m) x : Int)
    rw [((Same.apart O₃ (by decide) (.inr (by omega)) fitF).trans (tailF (by decide))).sval_eq]
    exact sval_nat V₂ ox
  · show sval z.mem B _ deSz (nw len) = (0 : Int)
    rw [((((Same.row_slot R₅ (by decide) (by decide) (.inl (by decide)) (by omega) fitD).trans
      (Same.row_slot R₆ (by decide) (by decide) (.inl (by decide)) (by omega) fitD)).trans
      (Same.of_unch O₇.unch (fun w hw r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        have := hde0; rw [eds] at this ⊢
        rcases Nat.eq_zero_or_pos w with rfl | hw0
        · exact .inl (by omega)
        · exact .inr (by omega))
        fun w hw => by have := mul_step (sz := deSz) (show w + 1 < nw len + 2 by omega); rw [eds] at *; omega)).trans
      (tailD (by decide))).sval_eq]
    exact sval_nat V₄ (by positivity)
  · show sval z.mem B _ deSz (nw len) = (1 : Int)
    rw [(tailD (by decide)).sval_eq]
    exact sval_nat e₇ (Nat.lt_of_lt_of_le (by decide) (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)))
  · rw [((Same.of_unch O₇.unch (fun w hw r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact .inr (by rw [hde0, eds]; omega))
        fun w hw => by have := mul_step (sz := deSz) (show w + 1 < nw len + 2 by omega); rw [eds] at *; omega).trans
      (tailD (by decide))).sv]
    exact V₆
  · have I : (w32 s₈.mem B (rv (kw len) (a 2)) * V.toNat + 1) % 2 ^ 32 = 0 := I₉
    have pm : virtualMod m % 2 ^ 32 = w32 s₈.mem B (rv (kw len) (a 2)) := by
      have e := Q₂' 0 (by omega)
      simp only [Nat.mul_zero, Nat.add_zero] at e
      rw [e]
      obtain ⟨j, hj⟩ : ∃ j, nw len = j + 1 := ⟨nw len - 1, by omega⟩
      rw [← P₂, hj, val32]
      have := (u.mem.readW (off B (rv (kw len) (a 2))) 32).isLt
      simp only [w32] at this ⊢
      omega
    have hp : virtualMod m = virtualMod m % 2 ^ 32 + 2 ^ 32 * (virtualMod m / 2 ^ 32) := (Nat.mod_add_div _ _).symm
    rw [hp, Nat.add_mul, Nat.mul_assoc, Nat.add_right_comm, Nat.add_mul_mod_self_left, pm]
    exact I
  · rw [mz, w32_write_self, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  · rw [val32_sv, ((Q₂'.trans (Same.ctg_out O₉ (.inr (by omega)) (by omega))).trans
      (Same.ctg_out Oz (.inr (by omega)) (by omega))).sv, ← val32_sv, P₂]
  · exact ((((((((((((K₀.mono (by decide)).trans Ku).trans (K₁.mono (by decide))).trans (K₂.mono (by decide))).trans
      (K₃.mono (by decide))).trans (K₄.mono (by decide))).trans (K₅.mono (by decide))).trans (K₆.mono (by decide))).trans
      (K₇.mono (by decide))).trans (K₈.mono (by decide))).trans (K₉.mono (by decide))).trans (Kz.mono (by decide)))
  · have r11 := rv_a len 11
    have hb0 : rv (kw len) (a 0) = 160 := by rw [r0]; omega
    refine (((((((((((O₀.unch.trans Uu).trans (R₁.unch (by decide))).trans (R₂.unch (by decide))).trans
      O₃.unch).trans (R₄.unch (by decide))).trans (R₅.unch (by decide))).trans (R₆.unch (by decide))).trans
      O₇.unch).trans O₈.unch).trans O₉.unch).trans Oz.unch).cover ?_
    intro w hw
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hw
    simp only [bodyWrites, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left]
    rw [hb0, r11, hde0, efs, eds, hAF, hAD, r2, r3, rv_a len 12] at *
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only <;> omega

end VG.Proof.Rsa.X86.InvBatchRt.F
