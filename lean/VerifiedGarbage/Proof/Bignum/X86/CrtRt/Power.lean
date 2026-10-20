module

public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Frame
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Num2
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Power
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.In
public import VerifiedGarbage.Proof.Mont.X86.WordOps
import VerifiedGarbage.Proof.Bignum.X86.CrtInputs
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.MulOk
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Loops

/-! # `R² mod M` in a context of private CRT at a run-time width

A doubling modulo `M` of slot 4 (`doubleStep_ok`): the sum into slot 1 with
its carry in the word after it, the sum less `M` into slot 4, and the sum
back where it is below `M`. One, doubled `16 Bc` times, is `R² mod M` for
`R = 2^(8 Bc)` (`powerTwo_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.CrtRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86
open VG.Proof.Bignum.X86.PublicRt (select_mod' count1_zf countLoop wp_carry)
open VG.Impl.Bignum.X86.PublicRt (argAt)

/-- The offset of slot `j` of the context. -/
abbrev sl (len : Nat) (c : Ctx) (j : Nat) : Nat := lo len (.slot c j)

/-- The value of slot `j` of the context. -/
abbrev sv (m : Mem) (base : Addr) (len : Nat) (c : Ctx) (j : Nat) : Nat :=
  val32 m base (lo len (.slot c j)) (cwc len c)

theorem sl_zero (len : Nat) (c : Ctx) : sl len c 0 = numBase := by simp [lo]

theorem sl_le {len : Nat} (c : Ctx) {i j : Nat} (hij : i < j) : sl len c i + st len c ≤ sl len c j := by
  have := Nat.mul_le_mul_right (st len c) hij
  simp only [lo, Nat.succ_mul] at *; omega

theorem zero_sub_cmask (c : Bool) : (0 : BitVec 32) - cmask c = BitVec.ofNat 32 c.toNat := by
  cases c <;> rfl

section
variable {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}

theorem doubleStep_ok (h : In base bytes len args s) (c : Ctx)
    (hT : sv s.mem base len c 4 < sv s.mem base len c 0) :
    WP isa (doubleStep c) s fun u =>
      Frame (frameR base (s.gpr .esp) [(lo len (.slot c 1), bc len c + 4), (lo len (.slot c 4), bc len c)]) s.mem u.mem ∧
      sv u.mem base len c 4 = (sv s.mem base len c 4 + sv s.mem base len c 4) % sv s.mem base len c 0 ∧
      u.gpr .esi = s.gpr .esi - 1 ∧ u.zf = some (s.gpr .esi - 1 == 0) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u := by
  have nw' := h.crt.scratch.nowrap
  have bl := h.bytes_lt
  have f8 := h.slot_fit c (j := 8) (by decide)
  have g := bc_ge h.lower' c
  have bw := bc_eq_cwc len c
  have s01 : lo len (.slot c 0) + st len c ≤ lo len (.slot c 1) := sl_le (len := len) c (by decide)
  have s14 : lo len (.slot c 1) + st len c ≤ lo len (.slot c 4) := sl_le (len := len) c (by decide)
  have s48 : lo len (.slot c 4) + st len c ≤ lo len (.slot c 8) := sl_le (len := len) c (by decide)
  have z0 : lo len (.slot c 0) = numBase := sl_zero len c
  have est : st len c = 2 * bc len c + 32 := rfl
  have N1 := one_ok c
  have cb1 : cb len (one c) = bc len c := by simp [cb, one]
  have cw1 : cw len (one c) = cwc len c := by simp [cw, cwc, cb, one]
  unfold doubleStep
  -- The sum into slot 1.
  refine WP.seq (WP.mono (chainAdd_ok (o := .slot c 1) (a := .slot c 4) (b := .slot c 4) h N1
    (by simp only [cb1]; omega) (by simp only [cb1]; omega) (by simp only [cb1]; omega)
    (by simp only [cb1]; omega) (by simp only [cb1]; omega)) fun u₁ ⟨O₁, _, ⟨c₁, ec₁, V₁⟩, K₁⟩ => ?_)
  simp only [cb1, cw1] at O₁ V₁
  have h₁ := h.keep K₁ (by decide) (by decide) (O₁.mono (Nat.zero_le _) (by omega))
  -- Its carry in the word after it.
  simp only [List.append_assoc]
  refine WP.seq (ptrTo_ok (r := .eax) (t := .edx) (x := .slot c 1) (by decide) (by decide) h₁.edi h₁.width
    h.upper' (by omega) fun u₂ K₂ m₂ p₂ => ?_)
  have h₂ := h₁.regs K₂ m₂
  refine cntTo_ok (r := .edx) (n := one c) h₂.width h.upper' N1.extra fun u₃ K₃ m₃ c₃ => ?_
  refine wp_addS rfl fun u₄ a₄ _ => wp_movS rfl fun u₅ a₅ _ => wp_subS rfl fun u₆ a₆ _ => ?_
  have K₆ : Keeps [.eax, .edx] u₂ u₆ := ((K₃.mono (by decide)).trans (a₄.keeps.mono (by decide))).trans
    ((a₅.keeps.mono (by decide)).trans (a₆.keeps.mono (by decide)))
  have ws₆ := h.ws.of_keeps ((K₁.mono (by decide) : Keeps [.eax, .ebx, .ecx, .edx, .ebp] s u₁).trans
    ((K₂.mono (by decide)).trans (K₆.mono (by decide))))
  have p₆ : PtrAt u₆ base .eax (lo len (.slot c 1) + bc len c) := by
    rw [PtrAt, a₆.other _ (by decide), a₅.other _ (by decide), a₄.gpr, K₃.1 _ (by decide), c₃, cb1,
      ptr_add p₂, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := bc len c) (by omega)]
  refine wp_storeS (ea_ptr ws₆ p₆ (d := 0) (by omega))
    (ws_write ws₆ (y := lo len (.slot c 1) + bc len c + 0) (n := 4) (by omega)) fun u₇ m₇ => WP.block_nil ?_
  have edx₆ : u₆.gpr .edx = BitVec.ofNat 32 c₁.toNat := by
    rw [a₆.gpr, a₅.gpr, a₅.other _ (by decide), a₄.other _ (by decide), K₃.1 _ (by decide), K₂.1 _ (by decide),
      ec₁, zero_sub_cmask]
  have m₇' : u₇.mem = u₁.mem.writeW (off base (lo len (.slot c 1) + bc len c)) (BitVec.ofNat 32 c₁.toNat) := by
    rw [m₇.mem, edx₆, a₆.mem, a₅.mem, a₄.mem, m₃, m₂, Nat.add_zero]
  have K₇ : Keeps [.eax, .ebx, .ecx, .edx, .ebp] s u₇ :=
    (((K₁.mono (by decide)).trans (K₂.mono (by decide))).trans (K₆.mono (by decide))).trans (m₇.keeps _)
  have W₇ : Outside base (lo len (.slot c 1) + bc len c) 4 u₁.mem u₇.mem := by
    rw [m₇']; exact writeW32_outside _ _ _ (by omega)
  have h₇ := h.keep K₇ (by decide) (by decide)
    ((O₁.mono (Nat.zero_le _) (by omega)).trans (W₇.mono (Nat.zero_le _) (by omega)))
  have S₇ : val32 u₇.mem base (lo len (.slot c 1)) (cwc len c) = val32 u₁.mem base (lo len (.slot c 1)) (cwc len c) :=
    W₇.val32 (by omega) (by omega)
  have T₇ : w32 u₇.mem base (lo len (.slot c 1) + bc len c) = c₁.toNat := by
    rw [m₇', w32_write_self, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by cases c₁ <;> decide)]
  have M₇ : val32 u₇.mem base numBase (cwc len c) = val32 s.mem base numBase (cwc len c) := by
    rw [W₇.val32 (by omega) (by omega), O₁.val32 (by omega) (by omega)]
  -- The sum less `M` into slot 4.
  refine WP.seq (WP.mono (chainSub_ok (o := .slot c 4) (a := .slot c 1) (b := .slot c 0) h₇ N1
    (by simp only [cb1]; omega) (by simp only [cb1]; omega) (by simp only [cb1, lo]; omega)
    (by simp only [cb1]; omega) (by simp only [cb1, lo]; omega)) fun u₈ ⟨O₈, P₈, ⟨b₁, eb₁, V₈⟩, K₈⟩ => ?_)
  simp only [cb1, cw1] at O₈ V₈ P₈
  have K₈' := K₇.trans K₈
  have ws₈ := h.ws.of_keeps K₈'
  have T₈ : w32 u₈.mem base (lo len (.slot c 1) + bc len c) = c₁.toNat := by
    rw [O₈.w32 (by omega) (by omega), T₇]
  -- The mask: the carry less the borrow.
  refine WP.seq (wp_movS (readSrc_ptr ws₈ P₈ (d := 0) (by omega)) fun t₁ u₁' _ => ?_)
  refine wp_carry (by rw [u₁'.other _ (by decide), eb₁]) fun t₂ u₂' c₂ => wp_sbbS rfl c₂ fun t₃ u₃' c₃ => ?_
  refine wp_sbb_self c₃ fun t₄ u₄' => wp_movS rfl fun t₅ u₅' _ => WP.block_nil ?_
  have K₅ : Keeps [.eax, .ecx] u₈ t₅ :=
    ((((u₁'.keeps.mono (by decide)).widen u₂'.keeps).widen u₃'.keeps).widen u₄'.keeps).widen u₅'.keeps
  have m₅ : t₅.mem = u₈.mem := by rw [u₅'.mem, u₄'.mem, u₃'.mem, u₂'.mem, u₁'.mem]
  have ecx₅ : t₅.gpr .ecx = cmask (decide (c₁.toNat < b₁.toNat)) := by
    rw [u₅'.gpr, u₄'.gpr]
    have eax₂ : (t₂.gpr .eax).toNat = c₁.toNat := by
      rw [u₂'.other _ (by decide), u₁'.gpr, Nat.add_zero, ← T₈]
    rw [eax₂, show (0 : BitVec 32).toNat = 0 from rfl, Nat.zero_add]
  have K₅' : Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t₅ := K₈'.trans (K₅.mono (by decide))
  have h₅ := h.keep K₅' (by decide) (by decide) (by
    rw [m₅]; exact ((O₁.mono (Nat.zero_le _) (by omega)).trans (W₇.mono (Nat.zero_le _) (by omega))).trans
      (O₈.mono (Nat.zero_le _) (by omega)))
  -- The sum back where it is below `M`.
  refine WP.seq (WP.mono (select_ok (x := .slot c 1) (d := .slot c 4) h₅ N1 (by simp only [cb1]; omega)
    (by simp only [cb1]; omega) (by simp only [cb1]; omega) ecx₅) fun u₉ ⟨O₉, V₉, K₉⟩ => ?_)
  simp only [cb1, cw1] at O₉ V₉
  refine wp_subZ rfl fun u₁₀ e₁₀ z₁₀ => WP.block_nil ?_
  have esi₉ : u₉.gpr .esi = s.gpr .esi := by rw [K₉.1 _ (by decide), K₅'.1 _ (by decide)]
  have M₈ : val32 u₈.mem base numBase (cwc len c) = val32 s.mem base numBase (cwc len c) := by
    rw [O₈.val32 (by omega) (by omega), M₇]
  refine ⟨?_, ?_, by rw [e₁₀.gpr, esi₉], by rw [z₁₀, esi₉], ?_⟩
  · rw [e₁₀.mem]
    have F₁ := frameR_of_outside (sp := s.gpr .esp) (ws := [(lo len (.slot c 1), bc len c + 4), (lo len (.slot c 4), bc len c)])
      (O₁.mono (Nat.le_refl _) (by omega) : Outside base (lo len (.slot c 1)) (bc len c + 4) s.mem u₁.mem) (by omega)
      (by simp)
    have F₇ := frameR_of_outside (sp := s.gpr .esp) (ws := [(lo len (.slot c 1), bc len c + 4), (lo len (.slot c 4), bc len c)])
      (W₇.mono (by omega) (by omega) : Outside base (lo len (.slot c 1)) (bc len c + 4) u₁.mem u₇.mem) (by omega)
      (by simp)
    have F₈ := frameR_of_outside (sp := s.gpr .esp) (ws := [(lo len (.slot c 1), bc len c + 4), (lo len (.slot c 4), bc len c)])
      O₈ (by omega) (by simp)
    have F₉ := frameR_of_outside (sp := s.gpr .esp) (ws := [(lo len (.slot c 1), bc len c + 4), (lo len (.slot c 4), bc len c)])
      O₉ (by omega) (by simp)
    rw [m₅] at F₉
    exact ((F₁.trans F₇).trans F₈).trans F₉
  · have key := select_mod' (X := 2 ^ (32 * cwc len c)) (Tl := val32 u₁.mem base (lo len (.slot c 1)) (cwc len c))
      (D := val32 u₈.mem base (lo len (.slot c 4)) (cwc len c)) (top := c₁.toNat) (c := b₁)
      (M := val32 s.mem base numBase (cwc len c)) (val32_lt _ _ _ _) (val32_lt _ _ _ _)
      (by rw [V₁]; simp only [sv, sl_zero] at hT; omega) (by have V := V₈; rw [S₇, z0, M₇] at V; exact V)
    simp only [sv, sl_zero]
    rw [e₁₀.mem, V₉, m₅]
    rw [show val32 u₈.mem base (lo len (.slot c 1)) (cwc len c) =
        val32 u₁.mem base (lo len (.slot c 1)) (cwc len c) by rw [O₈.val32 (by omega) (by omega), S₇]]
    rw [key, V₁]
  · exact (K₅'.mono (by decide)).trans ((K₉.mono (by decide)).trans (e₁₀.keeps.mono (by decide)))

end

end VG.Proof.Bignum.X86.CrtRt
