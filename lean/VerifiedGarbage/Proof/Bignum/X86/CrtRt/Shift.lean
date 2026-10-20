module

import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Ctx
import VerifiedGarbage.Proof.Mont.X86.WindowWords
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Power
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Bignum.X86.CrtInputs
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.MulOk
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Power
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Loops

/-! # The next window of a run-time-width exponentiation

`shiftLoop` shifts a number up by four bits (`shiftLoop_ok`); `nextWindow`
stores the exponent's top four bits in the window word and shifts the
exponent past them (`nextWindow_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.CrtRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86
open VG.Proof.Mont.X86.Dynamic (times16_toNat shr28_toNat shift_top val32_top_bits)
open VG.Proof.Bignum.X86.PublicRt (countLoop ptr4)

theorem shiftLoop_ok {t₀ : State} {W : Addr} {L : Nat} (hw : Ws t₀ W L) {x N : Nat} (hN : 0 < N)
    (hx : x + 4 * N ≤ L) (hebp : PtrAt t₀ W .ebp x) (hedx : (t₀.gpr .edx).toNat = 4 * N)
    (hecx : t₀.gpr .ecx = 0) :
    WP isa shiftLoop t₀ fun u => Outside W x (4 * N) t₀.mem u.mem ∧
      val32 u.mem W x N = val32 t₀.mem W x N * 16 % 2 ^ (32 * N) ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp] t₀ u := by
  have hn := hw.nowrap
  refine WP.mono (countLoop hN (fun j t => Keeps [.eax, .ebx, .ecx, .edx, .ebp] t₀ t ∧ PtrAt t W .ebp (x + 4 * j) ∧
      (t.gpr .edx).toNat = 4 * (N - j) ∧ Outside W x (4 * j) t₀.mem t.mem ∧
      val32 t.mem W x j = val32 t₀.mem W x j * 16 % 2 ^ (32 * j) ∧
      (t.gpr .ecx).toNat = val32 t₀.mem W x j * 16 / 2 ^ (32 * j)) ?_
    ⟨Keeps.refl _ _, by simpa using hebp, by simpa using hedx, Outside.refl _ _ _ _,
      by simp only [val32, Nat.zero_mul, Nat.zero_mod],
      by rw [hecx]; simp only [val32, Nat.zero_mul, Nat.zero_div]; rfl⟩)
    fun u ⟨K, _, _, O, V, _⟩ => ⟨O, V, K⟩
  rintro j t hj ⟨Kt, ebp, edx, O, V, C⟩
  have ht := hw.of_keeps Kt
  refine wp_movS (readSrc_ptr ht ebp (d := 0) (by omega_using [hx, hj])) fun s₂ u₂ _ => ?_
  refine wp_movS rfl fun s₃ u₃ _ => VG.Proof.Bignum.X86.PublicRt.wp_shr (by decide) fun s₄ u₄ => ?_
  refine wp_addS rfl fun s₅ u₅ _ => wp_addS rfl fun s₆ u₆ _ => wp_addS rfl fun s₇ u₇ _ => ?_
  refine wp_addS rfl fun s₈ u₈ _ => wp_addS rfl fun s₉ u₉ _ => ?_
  have k₉ : Keeps [.eax, .ebx] t s₉ := (((((((u₂.keeps.mono (by decide)).widen u₃.keeps).widen
    u₄.keeps).widen u₅.keeps).widen u₆.keeps).widen u₇.keeps).widen u₈.keeps).widen u₉.keeps
  have ht₉ := ht.of_keeps k₉
  have ebp₉ : PtrAt s₉ W .ebp (x + 4 * j) := by rw [PtrAt, k₉.1 _ (by decide)]; exact ebp
  refine wp_storeS (ea_ptr ht₉ ebp₉ (d := 0) (by omega_using [hx, hj]))
    (ws_write ht₉ (y := x + 4 * j + 0) (n := 4) (by omega_using [hx, hj])) fun s₁₀ m₁₀ => ?_
  refine wp_movS rfl fun s₁₁ u₁₁ _ => wp_addS rfl fun s₁₂ u₁₂ _ => wp_subZ rfl fun s₁₃ u₁₃ z₁₃ => WP.block_nil ?_
  obtain ⟨c₁, c₂⟩ := count_zf edx hj
  have mem₉ : s₉.mem = t.mem := by
    rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem]
  have word : w32 t.mem W (x + 4 * j) = w32 t₀.mem W (x + 4 * j) :=
    O.w32 (by omega_using []) (by omega_using [hx, hj, hn])
  have ecx₈ : s₈.gpr .ecx = t.gpr .ecx := by
    rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide)]
  have value : (s₉.gpr .eax).toNat =
      w32 t₀.mem W (x + 4 * j) * 16 % 2 ^ 32 + val32 t₀.mem W x j * 16 / 2 ^ (32 * j) := by
    rw [u₉.gpr, BitVec.toNat_add, ecx₈, C, u₈.gpr, u₇.gpr, u₆.gpr, u₅.gpr,
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, times16_toNat]
    change (w32 t.mem W (x + 4 * j + 0) * 16 % 2 ^ 32 + _) % 2 ^ 32 = _
    rw [Nat.add_zero, word]
    have : val32 t₀.mem W x j * 16 / 2 ^ (32 * j) < 16 :=
      (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).2 (by have := val32_lt t₀.mem W x j; omega)
    omega
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact Kt.trans ((((k₉.mono (by decide)).trans (m₁₀.keeps _)).trans (u₁₁.keeps.mono (by decide))).trans
      ((u₁₂.keeps.mono (by decide)).trans (u₁₃.keeps.mono (by decide))))
  · rw [PtrAt, u₁₃.other _ (by decide), u₁₂.gpr, u₁₁.other _ (by decide), m₁₀.gpr]; exact ptr4 ebp₉
  · rw [u₁₃.gpr, u₁₂.other _ (by decide), u₁₁.other _ (by decide), m₁₀.gpr, k₉.1 _ (by decide)]; exact c₁
  · rw [u₁₃.mem, u₁₂.mem, u₁₁.mem, m₁₀.mem, mem₉, Nat.add_zero]
    exact (O.mono (Nat.le_refl _) (by omega_using [])).trans
      ((writeW32_outside _ _ _ (by omega_using [hx, hj, hn])).mono (by omega_using []) (by omega_using []))
  · rw [u₁₃.mem, u₁₂.mem, u₁₁.mem, m₁₀.mem, mem₉, Nat.add_zero, val32_store hn (by omega_using [hx, hj]), V, value,
      val32_succ, pow32_succ, Nat.mul_comm (2 ^ 32), shift_top (Nat.two_pow_pos _) (val32_lt _ _ _ _)]
  · rw [u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.gpr, m₁₀.gpr, u₉.other _ (by decide),
      u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr,
      u₃.gpr, u₂.gpr, shr28_toNat, val32_top_bits, Nat.add_zero]
    exact congrArg (· / 2 ^ 28) word
  · rw [z₁₃, u₁₂.other _ (by decide), u₁₁.other _ (by decide), m₁₀.gpr, k₉.1 _ (by decide), c₂]

section
variable {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}

theorem nextWindow_ok (h : In base bytes len args s) (c : Ctx) :
    WP isa (nextWindow c) s fun u =>
      Frame (frameR base (s.gpr .esp) [(winOff, 4), (lo len (.slot c 8), bc len c)]) s.mem u.mem ∧
      w32 u.mem base winOff = sv s.mem base len c 8 * 16 / 2 ^ (32 * cwc len c) ∧
      sv u.mem base len c 8 = sv s.mem base len c 8 * 16 % 2 ^ (32 * cwc len c) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s u := by
  have nw' := h.crt.scratch.nowrap
  have f8 := h.slot_fit c (j := 8) (by decide)
  have g := bc_ge h.lower' c
  have hb := bc_le h.upper' c
  have bw := bc_eq_cwc len c
  have est : st len c = 2 * bc len c + 32 := rfl
  have lo8 : numBase ≤ lo len (.slot c 8) := by simp [lo]
  have nb : numBase = 3336 := rfl
  have cb1 : cb len (one c) = bc len c := by simp [cb, one]
  have cw1 : cw len (one c) = cwc len c := by simp [cw, cwc, cb, one]
  obtain ⟨k, ek⟩ : ∃ k, cwc len c = k + 1 := ⟨cwc len c - 1, by omega⟩
  unfold nextWindow
  simp only [List.append_assoc]
  -- The window word.
  refine WP.seq (ptrTo_ok (r := .eax) (t := .edx) (x := .slot c 8) (by decide) (by decide) h.edi h.width
    h.upper' (by omega) fun u₁ K₁ m₁ p₁ => ?_)
  have h₁ := h.regs K₁ m₁
  refine widthC_ok (k := 0) (c := c) (r := .edx) h₁.width h.upper' fun u₂ K₂ m₂ e₂ => ?_
  refine wp_addS rfl fun u₃ a₃ _ => wp_subS rfl fun u₄ a₄ _ => ?_
  have K₄ : Keeps [.eax, .edx] s u₄ :=
    (((K₁.mono (by decide)).trans (K₂.mono (by decide))).trans (a₃.keeps.mono (by decide))).trans
      (a₄.keeps.mono (by decide))
  have ws₄ := h.ws.of_keeps K₄
  have p₄ : PtrAt u₄ base .eax (lo len (.slot c 8) + 4 * k) := by
    rw [PtrAt, a₄.gpr, a₃.gpr, K₂.1 _ (by decide), e₂]
    rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, BitVec.sub_eq_add_neg, BitVec.add_assoc,
      ← BitVec.sub_eq_add_neg, BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega), ptr_add p₁,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := bc len c - 4) (by omega)]
    congr 2; omega
  refine wp_movS (readSrc_ptr ws₄ p₄ (d := 0) (by omega)) fun u₅ a₅ _ => ?_
  refine VG.Proof.Bignum.X86.PublicRt.wp_shr (by decide) fun u₆ a₆ => ?_
  have K₆ : Keeps [.eax, .edx] s u₆ := (K₄.trans (a₅.keeps.mono (by decide))).trans (a₆.keeps.mono (by decide))
  have h₆ := h.regs K₆ (by rw [a₆.mem, a₅.mem, a₄.mem, a₃.mem, m₂, m₁])
  refine wp_storeS (h₆.crt.scratch.ea (d := winOff) (by simp only [winOff]; omega))
    (h₆.crt.scratch.write (d := winOff) (by simp only [winOff]; omega)) fun u₇ m₇ => WP.block_nil ?_
  have mem₆ : u₆.mem = s.mem := by rw [a₆.mem, a₅.mem, a₄.mem, a₃.mem, m₂, m₁]
  have W₇ : Outside base winOff 4 s.mem u₇.mem := by
    rw [m₇.mem, ← mem₆]; exact writeW32_outside _ _ _ (by simp only [winOff]; omega)
  have win₇ : w32 u₇.mem base winOff = sv s.mem base len c 8 * 16 / 2 ^ (32 * cwc len c) := by
    rw [m₇.mem, w32_write_self, a₆.gpr, a₅.gpr, shr28_toNat, a₄.mem, a₃.mem, m₂, m₁, Nat.add_zero]
    simp only [sv]
    rw [ek, val32_top_bits]
  have K₇ : Keeps [.eax, .edx] s u₇ := K₆.trans (m₇.keeps _)
  have h₇ := h.keep K₇ (by decide) (by decide) (W₇.mono (Nat.zero_le _) (by simp only [winOff]; omega))
  -- The exponent shifted.
  refine WP.seq (ptrTo_ok (r := .ebp) (t := .edx) (x := .slot c 8) (by decide) (by decide) h₇.edi h₇.width
    h.upper' (by omega) fun u₈ K₈ m₈ p₈ => ?_)
  have h₈ := h₇.regs K₈ m₈
  refine cntTo_ok (r := .edx) (n := one c) h₈.width h.upper' (one_ok c).extra fun u₉ K₉ m₉ c₉ => ?_
  refine wp_movS rfl fun u₁₀ a₁₀ _ => WP.block_nil ?_
  have K₁₀ : Keeps [.ecx, .edx, .ebp] u₇ u₁₀ :=
    ((K₈.mono (by decide)).trans (K₉.mono (by decide))).trans (a₁₀.keeps.mono (by decide))
  refine WP.mono (shiftLoop_ok (h₇.ws.of_keeps K₁₀) (x := lo len (.slot c 8)) (N := cwc len c) (by omega)
    (by omega) (by rw [PtrAt, a₁₀.other _ (by decide), K₉.1 _ (by decide)]; exact p₈)
    (by rw [a₁₀.other _ (by decide), cnt_toNat h.upper' (one_ok c) c₉, cw1])
    a₁₀.gpr) fun u ⟨O, V, K⟩ => ?_
  have m₁₀ : u₁₀.mem = u₇.mem := by rw [a₁₀.mem, m₉, m₈]
  refine ⟨?_, ?_, ?_, ((K₇.mono (by decide)).trans (K₁₀.mono (by decide))).trans K⟩
  · rw [← m₁₀] at W₇
    have O' : Outside base (lo len (.slot c 8)) (bc len c) u₁₀.mem u.mem := by rw [bw]; exact O
    exact (frameR_of_outside W₇ (by simp only [winOff]; omega) (by simp)).trans
      (frameR_of_outside O' (by omega) (by simp))
  · rw [O.w32 (d := winOff) (by simp only [winOff]; omega) (by simp only [winOff]; omega), m₁₀, win₇]
  · simp only [sv]
    rw [V, m₁₀, W₇.val32 (by simp only [winOff]; omega) (by omega)]

end

end VG.Proof.Bignum.X86.CrtRt
