module

public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Window
import VerifiedGarbage.Proof.Mont.X86.WindowWords
import VerifiedGarbage.Proof.Framework.Omega

/-! # A run-time-width exponentiation by fixed windows

`windowPower_ok`: slot 6 set to slot 5 to the power of slot 8, modulo the
context's modulus, from one in slot 3 and `R² mod M` in slot 4.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.CrtRt

variable {Ex : List Region → List Region → Prop}

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86

/-- The ranges an exponentiation changes. -/
abbrev pwR (len : Nat) (c : Ctx) : List (Nat × Nat) :=
  [(winOff, 4), (lo len (.slot c 1), 3 * bc len c + 56), (lo len (.slot c 5), bc len c),
    (lo len (.slot c 6), bc len c), (lo len (.slot c 7), bc len c), (lo len (.slot c 8), bc len c),
    (te len c 0, 16 * bc len c)]

section
variable {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {c : Ctx} {M : Nat}

/-- Slot `j` lies apart from the other slots from 3 to 8 and past slot 1's range. -/
theorem slot_apart (len : Nat) (c : Ctx) {o j : Nat} (hne : j ≠ o) :
    lo len (.slot c j) + bc len c ≤ lo len (.slot c o) ∨ lo len (.slot c o) + bc len c ≤ lo len (.slot c j) := by
  have est : st len c = 2 * bc len c + 32 := rfl
  have ej : lo len (.slot c j) = numBase + j * st len c := rfl
  have eo : lo len (.slot c o) = numBase + o * st len c := rfl
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have := Nat.mul_le_mul_right (st len c) (show j + 1 ≤ o by omega)
    rw [Nat.succ_mul] at this; omega
  · have := Nat.mul_le_mul_right (st len c) (show o + 1 ≤ j by omega)
    rw [Nat.succ_mul] at this; omega

theorem slot_past1 (len : Nat) (c : Ctx) {j : Nat} (hj3 : 3 ≤ j) :
    lo len (.slot c 1) + (3 * bc len c + 56) ≤ lo len (.slot c j) := by
  have est : st len c = 2 * bc len c + 32 := rfl
  have ej : lo len (.slot c j) = numBase + j * st len c := rfl
  have e1 : lo len (.slot c 1) = numBase + st len c := by simp [lo]
  have := Nat.mul_le_mul_right (st len c) hj3
  omega

/-- A product into slot `o` keeps the other slots from 3 to 8. -/
theorem mulR_sv (h : In Ex base bytes len args s) {sp : BitVec 32} {m m' : Mem} {o j : Nat}
    (F : Frame (frameR base sp (mulR len c o)) m m') (R : CallRoom sp base bytes) (ho3 : 3 ≤ o) (ho : o ≤ 8)
    (hj3 : 3 ≤ j) (hj : j ≤ 8) (hne : j ≠ o) : sv m' base len c j = sv m base len c j := by
  have nw := h.scratch.nowrap
  have f8 := h.slot_fit c (j := 8) (by decide)
  have bw := bc_eq_cwc len c
  have est : st len c = 2 * bc len c + 32 := rfl
  have j8 : lo len (.slot c j) ≤ lo len (.slot c 8) := by
    have := Nat.mul_le_mul_right (st len c) hj; simp only [lo]; omega
  have o8 : lo len (.slot c o) ≤ lo len (.slot c 8) := by
    have := Nat.mul_le_mul_right (st len c) ho; simp only [lo]; omega
  have a := slot_apart len c hne
  have p1 := slot_past1 len c hj3
  have p1o := slot_past1 len c ho3
  refine frameR_val32 F R nw (by omega) ?_ ?_ <;>
    intro p hp <;> simp only [mulR, List.mem_cons, List.not_mem_nil, or_false] at hp <;>
    rcases hp with rfl | rfl <;> dsimp only <;> omega

/-- The table keeps slots 3 to 8 but 7. -/
theorem tabR_sv (h : In Ex base bytes len args s) {sp : BitVec 32} {m m' : Mem} {j : Nat}
    (F : Frame (frameR base sp (tabR len c)) m m') (R : CallRoom sp base bytes)
    (hj3 : 3 ≤ j) (hj : j ≤ 8) (h7 : j ≠ 7) : sv m' base len c j = sv m base len c j := by
  have nw := h.scratch.nowrap
  have T := h.table_fit c
  have f8 := h.slot_fit c (j := 8) (by decide)
  have bw := bc_eq_cwc len c
  have est : st len c = 2 * bc len c + 32 := rfl
  have j8 : lo len (.slot c j) ≤ lo len (.slot c 8) := by
    have := Nat.mul_le_mul_right (st len c) hj; simp only [lo]; omega
  have a := slot_apart len c (o := 7) h7
  have p1 := slot_past1 len c hj3
  have t0 : te len c 0 = lo len (.slot .wide 20) := by simp [te]
  refine frameR_val32 F R nw (by omega) ?_ (tabR_fit h c)
  intro p hp; simp only [tabR, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> dsimp only <;> omega

theorem pwR_fit (h : In Ex base bytes len args s) (c : Ctx) : ∀ p ∈ pwR len c, p.1 + p.2 ≤ bytes := by
  have fw := wR_fit h c
  have ft := tabR_fit h c
  have f8 := h.slot_fit c (j := 8) (by decide)
  have est : st len c = 2 * bc len c + 32 := rfl
  have e5 : lo len (.slot c 5) + st len c ≤ lo len (.slot c 8) := sl_le c (by decide)
  intro p hp
  simp only [pwR, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fw _ (by simp)
  · exact fw _ (by simp)
  · dsimp only; omega
  · exact fw _ (by simp)
  · exact fw _ (by simp)
  · exact fw _ (by simp)
  · exact ft _ (by simp)

/-- An exponentiation over the `N` windows `count` sets: slot 6 set to slot 5 to the power of the top
`4 N` bits of slot 8, modulo `M`. -/
theorem windowPowerWith_ok (C : CtxOk Ex base bytes len args c M s) (h3 : sv s.mem base len c 3 = 1)
    (h4 : sv s.mem base len c 4 = 2 ^ (16 * bc len c) % M) {count : List Instr} {N : Nat} (hN0 : 0 < N)
    (hN : N ≤ 2 * bc len c)
    (hc : ∀ t, CtxOk Ex base bytes len args c M t → WP isa (.block count) t fun u =>
      Keeps [.esi] t u ∧ u.mem = t.mem ∧ u.gpr .esi = BitVec.ofNat 32 N) :
    WP isa (windowPowerWith c count) s fun u =>
      CtxOk Ex base bytes len args c M u ∧ Frame (frameR base (s.gpr .esp) (pwR len c)) s.mem u.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u ∧
      sv u.mem base len c 6 = sv s.mem base len c 5 ^ (sv s.mem base len c 8 * 16 ^ N / 2 ^ (32 * cwc len c)) % M := by
  have h := C.inp
  have hM := C.gt
  have bw := bc_eq_cwc len c
  have g := bc_ge h.lower' c
  have hb := bc_le h.upper' c
  have RR : 2 ^ (16 * bc len c) = 2 ^ (8 * bc len c) * 2 ^ (8 * bc len c) := by
    rw [← Nat.pow_add]; congr 1; omega
  unfold windowPowerWith
  -- One in Montgomery form into slot 6.
  refine WP.seq (WP.mono (cmul_ok C (o := 6) (a := 4) (b := 3) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [h3]; exact hM)) fun s₁ ⟨C₁, K₁, F₁, L₁, V₁⟩ => ?_)
  have Y₁ : sv s₁.mem base len c 6 = 2 ^ (8 * bc len c) % M := by
    have v := VG.Proof.Bignum.mont_cancel C.coprime (o := sv s₁.mem base len c 6) (c := 2 ^ (8 * bc len c))
      (by rw [V₁, h4, h3, Nat.mul_one, Nat.mod_mod, RR])
    rwa [Nat.mod_eq_of_lt L₁] at v
  have m3₁ := mulR_sv h F₁ h.room (o := 6) (j := 3) (by decide) (by decide) (by decide) (by decide) (by decide)
  have m4₁ := mulR_sv h F₁ h.room (o := 6) (j := 4) (by decide) (by decide) (by decide) (by decide) (by decide)
  have m5₁ := mulR_sv h F₁ h.room (o := 6) (j := 5) (by decide) (by decide) (by decide) (by decide) (by decide)
  have m8₁ := mulR_sv h F₁ h.room (o := 6) (j := 8) (by decide) (by decide) (by decide) (by decide) (by decide)
  -- The base in Montgomery form.
  refine WP.seq (WP.mono (cmul_ok C₁ (o := 5) (a := 5) (b := 4) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [m4₁, h4]; exact Nat.mod_lt _ (by omega))) fun s₂ ⟨C₂, K₂, F₂, L₂, V₂⟩ => ?_)
  have B₂ : sv s₂.mem base len c 5 = sv s.mem base len c 5 * 2 ^ (8 * bc len c) % M := by
    have v := VG.Proof.Dsa.mont_scale C.coprime (out := sv s₂.mem base len c 5) (input := sv s.mem base len c 5)
      (c := 2 ^ (8 * bc len c)) (by rw [V₂, m5₁, m4₁, h4, RR])
    rwa [Nat.mod_eq_of_lt L₂] at v
  have h₁ := C₁.inp
  have m3₂ := mulR_sv h₁ F₂ h₁.room (o := 5) (j := 3) (by decide) (by decide) (by decide) (by decide) (by decide)
  have m6₂ := mulR_sv h₁ F₂ h₁.room (o := 5) (j := 6) (by decide) (by decide) (by decide) (by decide) (by decide)
  have m8₂ := mulR_sv h₁ F₂ h₁.room (o := 5) (j := 8) (by decide) (by decide) (by decide) (by decide) (by decide)
  -- The table.
  refine WP.seq (WP.mono (buildTable_ok C₂ (b := sv s.mem base len c 5) (by rw [m6₂, Y₁]) B₂) fun s₃ I₃ => ?_)
  have h₂ := C₂.inp
  have m3₃ := tabR_sv h₂ I₃.frame h₂.room (j := 3) (by decide) (by decide) (by decide)
  have m6₃ := tabR_sv h₂ I₃.frame h₂.room (j := 6) (by decide) (by decide) (by decide)
  have m8₃ := tabR_sv h₂ I₃.frame h₂.room (j := 8) (by decide) (by decide) (by decide)
  -- The count of windows.
  have C₃ := I₃.ctx
  refine WP.seq (WP.mono (hc s₃ C₃) fun s₅ ⟨K₅, mem₅, esi₅⟩ => ?_)
  have C₅ : CtxOk Ex base bytes len args c M s₅ := C₃.regs K₅ mem₅
  let P := 2 ^ (32 * cwc len c)
  let E := sv s.mem base len c 8
  let b := sv s.mem base len c 5
  have E₅ : sv s₅.mem base len c 8 = E := by rw [sv, mem₅]; simp only [sv] at m8₃ m8₂ m8₁ ⊢; rw [m8₃, m8₂, m8₁]
  have Y₅ : sv s₅.mem base len c 6 = 2 ^ (8 * bc len c) % M := by
    rw [sv, mem₅]; simp only [sv] at m6₃ m6₂ Y₁ ⊢; rw [m6₃, m6₂, Y₁]
  have T₅ : ∀ j < 16, val32 s₅.mem base (te len c j) (cwc len c) = b ^ j * 2 ^ (8 * bc len c) % M := by
    intro j hj; rw [mem₅]; exact I₃.table j hj
  have one₅ : sv s₅.mem base len c 3 = 1 := by
    rw [sv, mem₅]; simp only [sv] at m3₃ m3₂ m3₁ h3 ⊢; rw [m3₃, m3₂, m3₁, h3]
  have hE : E < P := val32_lt _ _ _ _
  -- The windows.
  refine WP.seq (WP.mono (PublicRt.countLoop (N := N) (by omega) (fun j t =>
      CtxOk Ex base bytes len args c M t ∧ Frame (frameR base (s₅.gpr .esp) (wR len c)) s₅.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s₅ t ∧ t.gpr .esi = BitVec.ofNat 32 (N - j) ∧
      (∀ j' < 16, val32 t.mem base (te len c j') (cwc len c) = b ^ j' * 2 ^ (8 * bc len c) % M) ∧
      sv t.mem base len c 8 = E * 16 ^ j % P ∧
      sv t.mem base len c 6 = b ^ (E * 16 ^ j / P) * 2 ^ (8 * bc len c) % M)
    (fun j t hj ⟨Ct, Ft, Kt, et, Tt, Et, Yt⟩ => WP.mono (windowStep_ok Ct Tt Yt (by omega) (by omega) et)
      fun u ⟨Cu, Fu, Ku, eu, zu, Yu, Eu⟩ => ?_)
    ⟨C₅, Frame.refl _ _, Keeps.refl _ _, by rw [esi₅, Nat.sub_zero], T₅,
      by rw [E₅, Nat.pow_zero, Nat.mul_one, Nat.mod_eq_of_lt hE],
      by rw [Y₅, Nat.pow_zero, Nat.mul_one, Nat.div_eq_of_lt hE, Nat.pow_zero, Nat.one_mul]⟩)
    fun s₆ I₆ => ?_)
  · have sp : t.gpr .esp = s₅.gpr .esp := Kt.1 _ (by decide)
    rw [sp] at Fu
    obtain ⟨_, Tu⟩ := wR_keep Ct.inp Fu (sp ▸ Ct.inp.room)
    refine ⟨⟨Cu, Ft.trans Fu, Kt.trans Ku, by rw [eu, Nat.sub_sub], fun j' hj' => by rw [Tu j' hj', Tt j' hj'], ?_, ?_⟩,
      by rw [zu]; congr 1; exact decide_eq_decide.mpr (by omega)⟩
    · rw [Eu, Et, Nat.pow_succ, ← Nat.mul_assoc, Nat.mod_mul_mod]
    · rw [Yu, Et, VG.Proof.Mont.X86.Dynamic.window_power, Nat.pow_succ, ← Nat.mul_assoc,
        VG.Proof.Mont.X86.Dynamic.window_exponent (E * 16 ^ j) _ (Nat.two_pow_pos _)]
  obtain ⟨C₆, F₆, K₆, _, _, E₆, Y₆⟩ := I₆
  -- Out of Montgomery form.
  have sp₆ : s₆.gpr .esp = s₅.gpr .esp := K₆.1 _ (by decide)
  obtain ⟨one₆, _⟩ := wR_keep C₅.inp F₆ C₅.inp.room
  refine WP.mono (cmul_ok C₆ (o := 6) (a := 6) (b := 3) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [one₆, one₅]; exact hM)) fun u ⟨Cu, Ku, Fu, Lu, Vu⟩ => ⟨Cu, ?_, ?_, ?_⟩
  · have sp₁ : s₁.gpr .esp = s.gpr .esp := K₁.1 _ (by decide)
    have sp₂ : s₂.gpr .esp = s.gpr .esp := (K₂.1 _ (by decide)).trans sp₁
    have sp₃ : s₃.gpr .esp = s.gpr .esp := (I₃.keeps.1 _ (by decide)).trans sp₂
    have sp₅ : s₅.gpr .esp = s.gpr .esp := by rw [K₅.1 _ (by decide), sp₃]
    rw [sp₁] at F₂
    have F₃ := I₃.frame
    rw [sp₂] at F₃
    rw [sp₆, sp₅] at Fu
    rw [sp₅] at F₆
    have sub : ∀ {ws : List (Nat × Nat)}, (∀ p ∈ ws, p ∈ pwR len c) → ∀ {m m' : Mem},
        Frame (frameR base (s.gpr .esp) ws) m m' → Frame (frameR base (s.gpr .esp) (pwR len c)) m m' :=
      fun hs _ _ F => frameR_mono F hs
    have m6 : ∀ p ∈ mulR len c 6, p ∈ pwR len c := by
      intro p hp; simp only [mulR, List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> simp
    have m5 : ∀ p ∈ mulR len c 5, p ∈ pwR len c := by
      intro p hp; simp only [mulR, List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> simp
    have mt : ∀ p ∈ tabR len c, p ∈ pwR len c := by
      intro p hp; simp only [tabR, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl <;> simp
    have mw : ∀ p ∈ wR len c, p ∈ pwR len c := by
      intro p hp; simp only [wR, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl <;> simp
    exact ((((sub m6 F₁).trans (sub m5 F₂)).trans (sub mt F₃)).trans
      (by rw [← mem₅]; exact sub mw F₆)).trans (sub m6 Fu)
  · exact (((((K₁.mono (by decide)).trans (K₂.mono (by decide))).trans I₃.keeps).trans
      (K₅.mono (by decide))).trans K₆).trans (Ku.mono (by decide))
  · have fin := Y₆
    have v := VG.Proof.Dsa.mont_decode (A := sv s₆.mem base len c 6) (out := sv u.mem base len c 6) C.coprime
      (by rw [fin, Nat.mod_mod]) (by rw [Vu, one₆, one₅])
    rw [Nat.mod_eq_of_lt Lu] at v
    exact v

/-- An exponentiation: slot 6 set to slot 5 to the power of slot 8, modulo `M`. -/
theorem windowPower_ok (C : CtxOk Ex base bytes len args c M s) (h3 : sv s.mem base len c 3 = 1)
    (h4 : sv s.mem base len c 4 = 2 ^ (16 * bc len c) % M) :
    WP isa (windowPower c) s fun u =>
      CtxOk Ex base bytes len args c M u ∧ Frame (frameR base (s.gpr .esp) (pwR len c)) s.mem u.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u ∧
      sv u.mem base len c 6 = sv s.mem base len c 5 ^ sv s.mem base len c 8 % M := by
  have h := C.inp
  have bw := bc_eq_cwc len c
  have g := bc_ge h.lower' c
  have hb := bc_le h.upper' c
  refine WP.mono (windowPowerWith_ok C h3 h4 (N := 2 * bc len c) (by omega) (Nat.le_refl _) fun t Ct =>
    widthC_ok (k := 0) (c := c) (r := .esi) (is := [_]) Ct.inp.width h.upper' fun s₄ K₄ M₄ e₄ =>
      wp_addS rfl fun s₅ a₅ _ => WP.block_nil ⟨K₄.trans (a₅.keeps.mono (by decide)), by rw [a₅.mem, M₄], by
        rw [a₅.gpr, e₄, BitVec.ofNat_add_ofNat]; congr 1; omega⟩) fun u ⟨Cu, Fu, Ku, Vu⟩ => ⟨Cu, Fu, Ku, ?_⟩
  rw [Vu, show 2 * bc len c = 8 * cwc len c by omega, VG.Proof.Mont.X86.Dynamic.window_all]

end

end VG.Proof.Bignum.X86.CrtRt
