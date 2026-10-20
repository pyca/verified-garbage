module

public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Power
import VerifiedGarbage.Proof.Mont.X86.Inverse
import VerifiedGarbage.Proof.Mont.X86.ExponentShift
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Bignum.X86.CrtInputs
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.MulOk
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Num2
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Loops

/-! # A context of private CRT at a run-time width

One doubled `16 Bc` times is `R² mod M` (`powerTwo_ok`). `prepare` replaces
the modulus by three unless it is an odd number above one, and sets one, the
inverse and `R² mod M` (`prepare_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.CrtRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86
open VG.Proof.Bignum.X86.PublicRt (count1_zf countLoop)
open VG.Impl.Bignum.X86.PublicRt (argAt)

/-- The ranges `R² mod M` changes. -/
abbrev powR (len : Nat) (c : Ctx) : List (Nat × Nat) :=
  [(lo len (.slot c 1), bc len c + 4), (lo len (.slot c 4), bc len c)]

section
variable {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}

theorem powerTwo_ok (h : In base bytes len args s) (c : Ctx) (hM : 1 < sv s.mem base len c 0) :
    WP isa (powerTwo c) s fun u =>
      Frame (frameR base (s.gpr .esp) (powR len c)) s.mem u.mem ∧
      sv u.mem base len c 4 = 2 ^ (16 * bc len c) % sv s.mem base len c 0 ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u := by
  have nw' := h.crt.scratch.nowrap
  have f8 := h.slot_fit c (j := 8) (by decide)
  have g := bc_ge h.lower' c
  have hb := bc_le h.upper' c
  have bw := bc_eq_cwc len c
  have s01 : lo len (.slot c 0) + st len c ≤ lo len (.slot c 1) := sl_le (len := len) c (by decide)
  have s14 : lo len (.slot c 1) + st len c ≤ lo len (.slot c 4) := sl_le (len := len) c (by decide)
  have s48 : lo len (.slot c 4) + st len c ≤ lo len (.slot c 8) := sl_le (len := len) c (by decide)
  have z0 : lo len (.slot c 0) = numBase := sl_zero len c
  have est : st len c = 2 * bc len c + 32 := rfl
  have cb1 : cb len (one c) = bc len c := by simp [cb, one]
  have cw1 : cw len (one c) = cwc len c := by simp [cw, cwc, cb, one]
  have fit : ∀ p ∈ powR len c, p.1 + p.2 ≤ bytes := by
    intro p hp
    simp only [powR, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> dsimp only <;> omega
  unfold powerTwo
  refine WP.seq (WP.mono (setSmall_ok (x := .slot c 4) h (one_ok c) (by rw [cb1]; omega) (v := 1) (by decide))
    fun u₀ ⟨O₀, V₀, K₀⟩ => ?_)
  simp only [cb1, cw1] at O₀ V₀
  have h₀ := h.keep K₀ (by decide) (by decide) (O₀.mono (Nat.zero_le _) (by omega))
  have M₀ : sv u₀.mem base len c 0 = sv s.mem base len c 0 := O₀.val32 (by omega) (by omega)
  refine WP.seq (widthC_ok (k := 0) (c := c) (r := .esi) h₀.width h.upper' fun u₁ K₁ m₁ e₁ => ?_)
  refine wp_addS rfl fun u₂ a₂ _ => wp_addS rfl fun u₃ a₃ _ => wp_addS rfl fun u₄ a₄ _ => ?_
  refine wp_addS rfl fun u₅ a₅ _ => WP.block_nil ?_
  have K₅ : Keeps [.esi] u₀ u₅ := (((K₁.trans a₂.keeps).trans a₃.keeps).trans a₄.keeps).trans a₅.keeps
  have m₅ : u₅.mem = u₀.mem := by rw [a₅.mem, a₄.mem, a₃.mem, a₂.mem, m₁]
  have esi₅ : (u₅.gpr .esi).toNat = 16 * bc len c := by
    rw [a₅.gpr, a₄.gpr, a₃.gpr, a₂.gpr, e₁]
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have h₅ := h₀.regs (K₅.mono (by decide) : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] u₀ u₅) m₅
  have sp₅ : u₅.gpr .esp = s.gpr .esp := by rw [K₅.1 _ (by decide), K₀.1 _ (by decide)]
  let M := sv s.mem base len c 0
  let I : Nat → State → Prop := fun j t =>
    Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] u₅ t ∧
      Frame (frameR base (s.gpr .esp) (powR len c)) u₅.mem t.mem ∧
      sv t.mem base len c 4 = 2 ^ j % M ∧ (t.gpr .esi).toNat = 16 * bc len c - j
  have I₀ : I 0 u₅ := ⟨Keeps.refl _ _, Frame.refl _ _,
    by rw [m₅]; simp only [sv] at V₀ ⊢; rw [V₀, Nat.pow_zero, Nat.mod_eq_of_lt hM], by rw [esi₅]; rfl⟩
  refine WP.mono (countLoop (N := 16 * bc len c) (by omega) I ?_ I₀) fun t ⟨Kt, Ft, Vt, _⟩ => ?_
  · rintro j t hj ⟨Kt, Ft, Vt, esit⟩
    have ht := h₅.keepF Kt (by decide) (by decide) (by rw [sp₅]; exact Ft) fit
    have Mt : sv t.mem base len c 0 = M := by
      have := frameR_val32 (d := lo len (.slot c 0)) (k := cwc len c) Ft h.crt.room nw' (by omega) (by
        intro p hp
        simp only [powR, List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl <;> dsimp only <;> omega) fit
      simp only [sv]; rw [this, m₅]; exact M₀
    have hM' : 0 < M := by omega
    refine WP.mono (doubleStep_ok ht c (by rw [Vt, Mt]; exact Nat.mod_lt _ hM'))
      fun u ⟨Fu, Vu, esiu, zu, Ku⟩ => ?_
    obtain ⟨c₁, c₂⟩ := count1_zf esit hj
    have spt : t.gpr .esp = s.gpr .esp := by rw [Kt.1 _ (by decide), sp₅]
    refine ⟨⟨Kt.trans Ku, Ft.trans (by rw [← spt]; exact Fu), ?_, by rw [esiu]; exact c₁⟩, by rw [zu, c₂]⟩
    rw [Vu, Vt, Mt, ← Nat.add_mod, ← Nat.two_mul, Nat.mul_comm, ← Nat.pow_succ]
  · have K₅s : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u₅ := (K₀.mono (by decide)).trans (K₅.mono (by decide))
    refine ⟨?_, Vt, K₅s.trans Kt⟩
    rw [← m₅] at O₀
    exact (frameR_of_outside O₀ (by omega) (by simp [powR])).trans Ft

/-- The modulus a context runs with: the factor itself if it is an odd number above one, else three. -/
def safeM (m : Nat) : Nat := if 1 < m ∧ m % 2 = 1 then m else 3

theorem safeM_gt (m : Nat) : 1 < safeM m := by unfold safeM; split <;> omega

theorem safeM_odd (m : Nat) : safeM m % 2 = 1 := by unfold safeM; split <;> omega

theorem safeM_of {m : Nat} (gt : 1 < m) (odd : m % 2 = 1) : safeM m = m := by
  unfold safeM; simp [gt, odd]

/-- The ranges `prepare` changes. -/
abbrev prepR (len : Nat) (c : Ctx) : List (Nat × Nat) :=
  [(invOff, 4), (lo len (.slot c 0), bc len c), (lo len (.slot c 1), bc len c + 4), (lo len (.slot c 3), bc len c),
    (lo len (.slot c 4), bc len c), (lo len (.slot c 7), bc len c)]

theorem w32_val32_one (m : Mem) (base : Addr) (d : Nat) : val32 m base d 1 = w32 m base d := by
  simp [val32]

theorem cmask_and (a b : Bool) : cmask a &&& cmask b = cmask (a && b) := by cases a <;> cases b <;> rfl

theorem cmask_not (a : Bool) : cmask a ^^^ BitVec.allOnes 32 = cmask (!a) := by cases a <;> rfl

theorem zero_sub_and_one (w : BitVec 32) : (0 : BitVec 32) - (w &&& 1) = cmask (decide (w.toNat % 2 = 1)) := by
  have e : w &&& 1 = BitVec.ofNat 32 (w.toNat % 2) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, show (1 : BitVec 32).toNat = 1 from rfl, Nat.and_one_is_mod]
    omega
  rw [e]
  rcases Nat.mod_two_eq_zero_or_one w.toNat with h | h <;> rw [h] <;> rfl

theorem prepare_ok (h : In base bytes len args s) (c : Ctx) :
    WP isa (prepare c) s fun u =>
      Frame (frameR base (s.gpr .esp) (prepR len c)) s.mem u.mem ∧
      sv u.mem base len c 0 = safeM (sv s.mem base len c 0) ∧ sv u.mem base len c 3 = 1 ∧
      sv u.mem base len c 4 = 2 ^ (16 * bc len c) % safeM (sv s.mem base len c 0) ∧
      (safeM (sv s.mem base len c 0) * w32 u.mem base invOff + 1) % 2 ^ 32 = 0 ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u := by
  have nw' := h.crt.scratch.nowrap
  have f8 := h.slot_fit c (j := 8) (by decide)
  have g := bc_ge h.lower' c
  have bw := bc_eq_cwc len c
  have s01 : lo len (.slot c 0) + st len c ≤ lo len (.slot c 1) := sl_le (len := len) c (by decide)
  have s13 : lo len (.slot c 1) + st len c ≤ lo len (.slot c 3) := sl_le (len := len) c (by decide)
  have s34 : lo len (.slot c 3) + st len c ≤ lo len (.slot c 4) := sl_le (len := len) c (by decide)
  have s47 : lo len (.slot c 4) + st len c ≤ lo len (.slot c 7) := sl_le (len := len) c (by decide)
  have s78 : lo len (.slot c 7) + st len c ≤ lo len (.slot c 8) := sl_le (len := len) c (by decide)
  have z0 : lo len (.slot c 0) = numBase := sl_zero len c
  have est : st len c = 2 * bc len c + 32 := rfl
  have nb : numBase = 3336 := rfl
  have cb1 : cb len (one c) = bc len c := by simp [cb, one]
  have cw1 : cw len (one c) = cwc len c := by simp [cw, cwc, cb, one]
  have hk : ∃ k, cwc len c = k + 1 := ⟨cwc len c - 1, by omega⟩
  obtain ⟨k, ek⟩ := hk
  have fitP : ∀ p ∈ prepR len c, p.1 + p.2 ≤ bytes := by
    intro p hp
    simp only [prepR, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> (try simp only [invOff]) <;> omega
  let M₀ := sv s.mem base len c 0
  unfold prepare
  -- One in slot 3, three in slot 7.
  refine WP.seq (WP.mono (setSmall_ok (x := .slot c 3) h (one_ok c) (by rw [cb1]; omega) (v := 1) (by decide))
    fun u₁ ⟨O₁, V₁, K₁⟩ => ?_)
  simp only [cb1, cw1] at O₁ V₁
  have h₁ := h.keep K₁ (by decide) (by decide) (O₁.mono (Nat.zero_le _) (by omega))
  refine WP.seq (WP.mono (setSmall_ok (x := .slot c 7) h₁ (one_ok c) (by rw [cb1]; omega) (v := 3) (by decide))
    fun u₂ ⟨O₂, V₂, K₂⟩ => ?_)
  simp only [cb1, cw1] at O₂ V₂
  have h₂ := h₁.keep K₂ (by decide) (by decide) (O₂.mono (Nat.zero_le _) (by omega))
  have M₂ : val32 u₂.mem base numBase (cwc len c) = M₀ := by
    rw [O₂.val32 (by omega) (by omega), O₁.val32 (by omega) (by omega), ← z0]
  have one₂ : val32 u₂.mem base (lo len (.slot c 3)) (cwc len c) = 1 := by
    rw [O₂.val32 (by omega) (by omega), V₁]
  -- `ecx`: whether the modulus is above one.
  refine WP.seq (WP.mono (lessThan_ok (a := .slot c 3) (b := .slot c 0) h₂ (one_ok c) (by rw [cb1]; omega)
    (by rw [cb1]; omega)) fun u₃ ⟨m₃, e₃, K₃⟩ => ?_)
  simp only [cw1, one₂, z0, M₂] at e₃
  have h₃ := h₂.regs (K₃.mono (by decide) : Keeps [.eax, .ecx, .edx, .ebp, .esi] u₂ u₃) m₃
  -- `ecx`: whether it is to be replaced.
  refine WP.seq (wp_movS (readSrc_sc h₃.crt.scratch (d := numBase) (by omega)) fun v₁ a₁ _ => ?_)
  refine wp_logicS (.inl rfl) rfl fun v₂ a₂ => wp_movS rfl fun v₃ a₃ _ => wp_subS rfl fun v₄ a₄ _ => ?_
  refine wp_logicS (.inl rfl) rfl fun v₅ a₅ => wp_logicS (.inr rfl) rfl fun v₆ a₆ => WP.block_nil ?_
  have mem₆ : v₆.mem = u₂.mem := by rw [a₆.mem, a₅.mem, a₄.mem, a₃.mem, a₂.mem, a₁.mem, m₃]
  have par : (u₂.mem.readW (off base numBase) 32).toNat % 2 = M₀ % 2 := by
    rw [← M₂, ek, VG.Proof.Mont.X86.Dynamic.val32_parity]
  have edx₂ : v₂.gpr .edx = u₂.mem.readW (off base numBase) 32 &&& 1 := by
    rw [a₂.gpr]; show v₁.gpr .edx &&& 1 = _; rw [a₁.gpr, m₃]
  have eax₄ : v₄.gpr .eax = (0 : BitVec 32) - (u₂.mem.readW (off base numBase) 32 &&& 1) := by
    rw [a₄.gpr, a₃.gpr, a₃.other _ (by decide), edx₂]
  have ecx₄ : v₄.gpr .ecx = cmask (decide (1 < M₀)) := by
    rw [a₄.other _ (by decide), a₃.other _ (by decide), a₂.other _ (by decide), a₁.other _ (by decide), e₃]
  have ecx₅ : v₅.gpr .ecx = v₄.gpr .ecx &&& v₄.gpr .eax := by rw [a₅.gpr]; rfl
  have ecx₆ : v₆.gpr .ecx = cmask (!(decide (1 < M₀) && decide (M₀ % 2 = 1))) := by
    rw [a₆.gpr]
    show v₅.gpr .ecx ^^^ BitVec.allOnes 32 = _
    rw [ecx₅, ecx₄, eax₄, zero_sub_and_one, par, cmask_and, cmask_not]
  have K₆ : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s v₆ :=
    (((K₁.mono (by decide)).trans (K₂.mono (by decide))).trans (K₃.mono (by decide))).trans
      ((((((a₁.keeps.mono (by decide)).trans (a₂.keeps.mono (by decide))).trans (a₃.keeps.mono (by decide))).trans
        (a₄.keeps.mono (by decide))).trans (a₅.keeps.mono (by decide))).trans (a₆.keeps.mono (by decide)))
  have h₆ := h₂.regs ((K₃.mono (by decide) : Keeps [.eax, .ecx, .edx, .ebp, .esi] u₂ u₃).trans
    ((((((a₁.keeps.mono (by decide)).trans (a₂.keeps.mono (by decide))).trans (a₃.keeps.mono (by decide))).trans
        (a₄.keeps.mono (by decide))).trans (a₅.keeps.mono (by decide))).trans (a₆.keeps.mono (by decide))) :
      Keeps [.eax, .ecx, .edx, .ebp, .esi] u₂ v₆) mem₆
  -- The modulus replaced by three where it is to be.
  refine WP.seq (WP.mono (select_ok (x := .slot c 7) (d := .slot c 0) h₆ (one_ok c) (by rw [cb1]; omega)
    (by rw [cb1]; omega) (by rw [cb1]; simp only [Apart]; omega) ecx₆) fun u₇ ⟨O₇, V₇, K₇⟩ => ?_)
  simp only [cb1, cw1] at O₇ V₇
  have safe₇ : val32 u₇.mem base numBase (cwc len c) = safeM M₀ := by
    rw [← z0, V₇, mem₆]
    have three : val32 u₂.mem base (lo len (.slot c 7)) (cwc len c) = 3 := V₂
    rw [three, z0, M₂]
    unfold safeM
    by_cases hp : 1 < M₀ ∧ M₀ % 2 = 1
    · have e : (!(decide (1 < M₀) && decide (M₀ % 2 = 1))) = false := by simp [hp.1, hp.2]
      rw [e]; simp [hp]
    · have e : (!(decide (1 < M₀) && decide (M₀ % 2 = 1))) = true := by
        simp only [Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega
      rw [e]; simp [hp]
  have h₇ := h₆.keep K₇ (by decide) (by decide) (O₇.mono (Nat.zero_le _) (by omega))
  -- The inverse.
  have odd₇ : w32 u₇.mem base numBase % 2 = 1 := by
    rw [← VG.Proof.Mont.X86.Dynamic.val32_parity u₇.mem base numBase k, ← ek, safe₇]; exact safeM_odd _
  refine WP.seq (WP.mono (VG.Proof.Mont.X86.Dynamic.setupInverse_ok h₇.crt.scratch (mo := numBase) (inv := invOff) (by omega)
    (by simp only [invOff]; omega) odd₇) fun u₈ ⟨I₈, O₈, K₈⟩ => ?_)
  have h₈ := h₇.keep K₈ (by decide) (by decide) (O₈.mono (Nat.zero_le _) (by simp only [invOff]; omega))
  have M₈ : val32 u₈.mem base numBase (cwc len c) = safeM M₀ := by
    rw [O₈.val32 (by simp only [invOff]; omega) (by omega), safe₇]
  -- `R² mod M`.
  refine WP.mono (powerTwo_ok h₈ c (by simp only [sv, z0]; rw [M₈]; exact safeM_gt _)) fun u ⟨F₉, V₉, K₉⟩ => ?_
  have sp₈ : u₈.gpr .esp = s.gpr .esp := by
    rw [K₈.1 _ (by decide), K₇.1 _ (by decide), K₆.1 _ (by decide)]
  rw [sp₈] at F₉
  have fitW : ∀ p ∈ powR len c, p.1 + p.2 ≤ bytes := by
    intro p hp
    simp only [powR, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> dsimp only <;> omega
  have keepVal : ∀ d, d + 4 * cwc len c ≤ bytes → (d + 4 * cwc len c ≤ lo len (.slot c 1) ∨
      lo len (.slot c 1) + (bc len c + 4) ≤ d) → (d + 4 * cwc len c ≤ lo len (.slot c 4) ∨ lo len (.slot c 4) + bc len c ≤ d) →
      val32 u.mem base d (cwc len c) = val32 u₈.mem base d (cwc len c) := fun d hd h1 h2 =>
    frameR_val32 F₉ h.crt.room nw' hd (by
      intro p hp
      simp only [powR, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> dsimp only <;> omega) fitW
  refine ⟨?_, ?_, ?_, ?_, ?_, (K₆.trans ((K₇.mono (by decide)).trans (K₈.mono (by decide)))).trans K₉⟩
  · have F₁ := frameR_of_outside (sp := s.gpr .esp) (ws := prepR len c) O₁ (by omega) (by simp)
    have F₂ := frameR_of_outside (sp := s.gpr .esp) (ws := prepR len c) O₂ (by omega) (by simp)
    have F₇ := frameR_of_outside (sp := s.gpr .esp) (ws := prepR len c) O₇ (by omega) (by simp)
    have F₈ := frameR_of_outside (sp := s.gpr .esp) (ws := prepR len c) O₈ (by simp only [invOff]; omega) (by simp)
    rw [mem₆] at F₇
    exact (((F₁.trans F₂).trans F₇).trans F₈).trans (frameR_mono F₉ (by simp))
  · simp only [sv, z0]; rw [keepVal _ (by omega) (by omega) (by omega), M₈]; simp only [M₀, sv, z0]
  · simp only [sv]
    rw [keepVal _ (by omega) (by omega) (by omega), O₈.val32 (by simp only [invOff]; omega) (by omega),
      O₇.val32 (by omega) (by omega), mem₆, one₂]
  · simp only [sv] at V₉ ⊢; rw [V₉]; simp only [z0]; rw [M₈]; simp only [M₀, sv, z0]
  · have W : w32 u.mem base invOff = w32 u₈.mem base invOff := by
      rw [← w32_val32_one, ← w32_val32_one]
      exact frameR_val32 F₉ h.crt.room nw' (by simp only [invOff]; omega) (by
        intro p hp
        simp only [powR, List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl <;> dsimp only <;> simp only [invOff] <;> omega) fitW
    rw [W]
    rw [← safe₇, ek, val32, Nat.add_mul, Nat.mul_assoc, Nat.add_right_comm, Nat.add_mul_mod_self_left]
    exact I₈

end

end VG.Proof.Bignum.X86.CrtRt
