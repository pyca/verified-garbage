module

import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Select
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Ctx
import VerifiedGarbage.Proof.Mont.X86.WindowWords
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Mont.X86.PowerInit
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Table
import VerifiedGarbage.Proof.Bignum.X86.CrtInputs
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.MulOk
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Power
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Shift
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Table
import VerifiedGarbage.Proof.Dsa.Arithmetic

/-! # A window of a run-time-width exponentiation

Four squares of slot 6, the window's entry into slot 7, and their product
(`windowStep_ok`), keeping the context, slot 3 and the table.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.CrtRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86

/-- The ranges a window changes. -/
abbrev wR (len : Nat) (c : Ctx) : List (Nat × Nat) :=
  [(winOff, 4), (lo len (.slot c 1), 3 * bc len c + 56), (lo len (.slot c 6), bc len c),
    (lo len (.slot c 7), bc len c), (lo len (.slot c 8), bc len c)]

/-- The ranges of `nextWindow`. -/
abbrev nwR (len : Nat) (c : Ctx) : List (Nat × Nat) := [(winOff, 4), (lo len (.slot c 8), bc len c)]

section
variable {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {c : Ctx} {M : Nat}

theorem wR_fit (h : In base bytes len args s) (c : Ctx) : ∀ p ∈ wR len c, p.1 + p.2 ≤ bytes := by
  have f8 := h.slot_fit c (j := 8) (by decide)
  have est : st len c = 2 * bc len c + 32 := rfl
  have e1 : lo len (.slot c 1) = numBase + st len c := by simp [lo]
  have e8 : lo len (.slot c 8) = numBase + 8 * st len c := rfl
  have e6 : lo len (.slot c 6) = numBase + 6 * st len c := rfl
  have e7 : lo len (.slot c 7) = numBase + 7 * st len c := rfl
  have nb : numBase = 3336 := rfl
  have wo : winOff = 4 := rfl
  intro p hp
  simp only [wR, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> omega

theorem wR_hdr (len : Nat) (c : Ctx) :
    ∀ p ∈ wR len c, numBase + bc len c ≤ p.1 ∨ (4 ≤ p.1 ∧ p.1 + p.2 ≤ numBase) := by
  have est : st len c = 2 * bc len c + 32 := rfl
  have e1 : lo len (.slot c 1) = numBase + st len c := by simp [lo]
  have e8 : lo len (.slot c 8) = numBase + 8 * st len c := rfl
  have e6 : lo len (.slot c 6) = numBase + 6 * st len c := rfl
  have e7 : lo len (.slot c 7) = numBase + 7 * st len c := rfl
  have nb : numBase = 3336 := rfl
  have wo : winOff = 4 := rfl
  intro p hp
  simp only [wR, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> omega

theorem wR_sub_nw (len : Nat) (c : Ctx) : ∀ p ∈ nwR len c, p ∈ wR len c := by
  intro p hp; simp only [nwR, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl <;> simp

theorem wR_sub_mul (len : Nat) (c : Ctx) : ∀ p ∈ mulR len c 6, p ∈ wR len c := by
  intro p hp; simp only [mulR, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl <;> simp

/-- A window keeps slot 3 and the table. -/
theorem wR_keep (h : In base bytes len args s) {sp : BitVec 32} {m m' : Mem}
    (F : Frame (frameR base sp (wR len c)) m m') (R : CallRoom sp base bytes) :
    sv m' base len c 3 = sv m base len c 3 ∧
      ∀ j < 16, val32 m' base (te len c j) (cwc len c) = val32 m base (te len c j) (cwc len c) := by
  have nw := h.crt.scratch.nowrap
  have f8 := h.slot_fit c (j := 8) (by decide)
  have T := h.table_fit c
  have bw := bc_eq_cwc len c
  have est : st len c = 2 * bc len c + 32 := rfl
  have e1 : lo len (.slot c 1) = numBase + st len c := by simp [lo]
  have e3 : lo len (.slot c 3) = numBase + 3 * st len c := rfl
  have e8 : lo len (.slot c 8) = numBase + 8 * st len c := rfl
  have e6 : lo len (.slot c 6) = numBase + 6 * st len c := rfl
  have e7 : lo len (.slot c 7) = numBase + 7 * st len c := rfl
  have nb : numBase = 3336 := rfl
  have wo : winOff = 4 := rfl
  have t0 : te len c 0 = lo len (.slot .wide 20) := by simp [te]
  have fit := wR_fit h c
  refine ⟨frameR_val32 F R nw (by omega) ?_ fit, fun j hj => ?_⟩
  · intro p hp; simp only [wR, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> omega
  · obtain ⟨tj0, tj⟩ := te_le (len := len) (c := c) hj
    refine frameR_val32 F R nw (by omega) ?_ fit
    intro p hp; simp only [wR, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> omega

/-- A product into slot 6 keeps slot 8 and the table. -/
theorem mulR6_keep (h : In base bytes len args s) {sp : BitVec 32} {m m' : Mem}
    (F : Frame (frameR base sp (mulR len c 6)) m m') (R : CallRoom sp base bytes) :
    sv m' base len c 8 = sv m base len c 8 ∧
      ∀ j < 16, val32 m' base (te len c j) (cwc len c) = val32 m base (te len c j) (cwc len c) := by
  have nw := h.crt.scratch.nowrap
  have f8 := h.slot_fit c (j := 8) (by decide)
  have T := h.table_fit c
  have bw := bc_eq_cwc len c
  have est : st len c = 2 * bc len c + 32 := rfl
  have e1 : lo len (.slot c 1) = numBase + st len c := by simp [lo]
  have e8 : lo len (.slot c 8) = numBase + 8 * st len c := rfl
  have e6 : lo len (.slot c 6) = numBase + 6 * st len c := rfl
  have t0 : te len c 0 = lo len (.slot .wide 20) := by simp [te]
  have fit : ∀ p ∈ mulR len c 6, p.1 + p.2 ≤ bytes := fun p hp => wR_fit h c p (wR_sub_mul len c p hp)
  refine ⟨frameR_val32 F R nw (by omega) ?_ fit, fun j hj => ?_⟩
  · intro p hp; simp only [mulR, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> dsimp only <;> omega
  · obtain ⟨tj0, tj⟩ := te_le (len := len) (c := c) hj
    refine frameR_val32 F R nw (by omega) ?_ fit
    intro p hp; simp only [mulR, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> dsimp only <;> omega

/-- The window's shift keeps slot 6 and the table. -/
theorem nwR_keep (h : In base bytes len args s) {sp : BitVec 32} {m m' : Mem}
    (F : Frame (frameR base sp (nwR len c)) m m') (R : CallRoom sp base bytes) :
    sv m' base len c 6 = sv m base len c 6 ∧
      ∀ j < 16, val32 m' base (te len c j) (cwc len c) = val32 m base (te len c j) (cwc len c) := by
  have nw := h.crt.scratch.nowrap
  have f8 := h.slot_fit c (j := 8) (by decide)
  have T := h.table_fit c
  have bw := bc_eq_cwc len c
  have est : st len c = 2 * bc len c + 32 := rfl
  have e8 : lo len (.slot c 8) = numBase + 8 * st len c := rfl
  have e6 : lo len (.slot c 6) = numBase + 6 * st len c := rfl
  have nb : numBase = 3336 := rfl
  have wo : winOff = 4 := rfl
  have t0 : te len c 0 = lo len (.slot .wide 20) := by simp [te]
  have fit : ∀ p ∈ nwR len c, p.1 + p.2 ≤ bytes := fun p hp => wR_fit h c p (wR_sub_nw len c p hp)
  refine ⟨frameR_val32 F R nw (by omega) ?_ fit, fun j hj => ?_⟩
  · intro p hp; simp only [nwR, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> dsimp only <;> omega
  · obtain ⟨tj0, tj⟩ := te_le (len := len) (c := c) hj
    refine frameR_val32 F R nw (by omega) ?_ fit
    intro p hp; simp only [nwR, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> dsimp only <;> omega

/-- A square of slot 6. -/
theorem square_ok (C : CtxOk base bytes len args c M s) {y : Nat}
    (hy : sv s.mem base len c 6 = y * 2 ^ (8 * bc len c) % M) :
    WP isa (square c) s fun t => CtxOk base bytes len args c M t ∧ Keeps [.eax, .ecx, .edx] s t ∧
      Frame (frameR base (s.gpr .esp) (mulR len c 6)) s.mem t.mem ∧
      sv t.mem base len c 6 = y ^ 2 * 2 ^ (8 * bc len c) % M := by
  have hM := C.gt
  unfold square
  refine WP.mono (cmul_ok C (o := 6) (a := 6) (b := 6) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [hy]; exact Nat.mod_lt _ (by omega))) fun t ⟨C', K, F, L, V⟩ => ⟨C', K, F, ?_⟩
  have v := VG.Proof.Dsa.mont_product C.coprime (a := y) (b := y) (by rw [hy, Nat.mod_mod])
    (by rw [hy, Nat.mod_mod]) V
  rw [Nat.mod_eq_of_lt L] at v
  rw [v, Nat.pow_two]

/-- Four squares of slot 6, then `P`. -/
theorem squares_ok (C : CtxOk base bytes len args c M s) {y : Nat}
    (hy : sv s.mem base len c 6 = y * 2 ^ (8 * bc len c) % M) {P : Prog isa} {Q : State → Prop}
    (k : ∀ t, CtxOk base bytes len args c M t → Keeps [.eax, .ecx, .edx] s t →
      Frame (frameR base (s.gpr .esp) (mulR len c 6)) s.mem t.mem →
      sv t.mem base len c 6 = y ^ 16 * 2 ^ (8 * bc len c) % M → WP isa P t Q) :
    WP isa (.seq (square c) (.seq (square c) (.seq (square c) (.seq (square c) P)))) s Q := by
  refine WP.seq (WP.mono (square_ok C hy) fun t₁ ⟨C₁, K₁, F₁, V₁⟩ => ?_)
  refine WP.seq (WP.mono (square_ok C₁ V₁) fun t₂ ⟨C₂, K₂, F₂, V₂⟩ => ?_)
  refine WP.seq (WP.mono (square_ok C₂ V₂) fun t₃ ⟨C₃, K₃, F₃, V₃⟩ => ?_)
  refine WP.seq (WP.mono (square_ok C₃ V₃) fun t₄ ⟨C₄, K₄, F₄, V₄⟩ => ?_)
  have sp₁ : t₁.gpr .esp = s.gpr .esp := K₁.1 _ (by decide)
  have sp₂ : t₂.gpr .esp = s.gpr .esp := (K₂.1 _ (by decide)).trans sp₁
  have sp₃ : t₃.gpr .esp = s.gpr .esp := (K₃.1 _ (by decide)).trans sp₂
  rw [sp₁] at F₂
  rw [sp₂] at F₃
  rw [sp₃] at F₄
  refine k t₄ C₄ (((K₁.trans K₂).trans K₃).trans K₄) (((F₁.trans F₂).trans F₃).trans F₄) ?_
  rw [V₄, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul]

/-- A window: slot 6 to `y^16 b^w` (in Montgomery form) for the top four bits `w` of slot 8, slot 8
shifted up past them, and `esi` down one. -/
theorem windowStep_ok (C : CtxOk base bytes len args c M s) {b y n : Nat}
    (hT : ∀ j < 16, val32 s.mem base (te len c j) (cwc len c) = b ^ j * 2 ^ (8 * bc len c) % M)
    (hy : sv s.mem base len c 6 = y * 2 ^ (8 * bc len c) % M) (hn0 : 0 < n) (hn : n < 2 ^ 32)
    (he : s.gpr .esi = BitVec.ofNat 32 n) :
    WP isa (windowStep c) s fun u =>
      CtxOk base bytes len args c M u ∧ Frame (frameR base (s.gpr .esp) (wR len c)) s.mem u.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u ∧
      u.gpr .esi = BitVec.ofNat 32 (n - 1) ∧ u.zf = some (decide (n = 1)) ∧
      sv u.mem base len c 6 =
        y ^ 16 * b ^ (sv s.mem base len c 8 * 16 / 2 ^ (32 * cwc len c)) * 2 ^ (8 * bc len c) % M ∧
      sv u.mem base len c 8 = sv s.mem base len c 8 * 16 % 2 ^ (32 * cwc len c) := by
  have h := C.inp
  have hM := C.gt
  have f8 := h.slot_fit c (j := 8) (by decide)
  have T := h.table_fit c
  have bw := bc_eq_cwc len c
  have est : st len c = 2 * bc len c + 32 := rfl
  have e6 : lo len (.slot c 6) = numBase + 6 * st len c := rfl
  have e7 : lo len (.slot c 7) = numBase + 7 * st len c := rfl
  have e8 : lo len (.slot c 8) = numBase + 8 * st len c := rfl
  have nw := h.crt.scratch.nowrap
  have fitW := wR_fit h c
  have hdrW := wR_hdr len c
  unfold windowStep
  refine squares_ok C hy fun t₁ C₁ K₁ F₁ V₁ => ?_
  obtain ⟨E₁, T₁⟩ := mulR6_keep h F₁ h.crt.room
  have sp₁ : t₁.gpr .esp = s.gpr .esp := K₁.1 _ (by decide)
  -- The window.
  refine WP.seq (WP.mono (nextWindow_ok C₁.inp c) fun t₂ ⟨F₂, W₂, E₂, K₂⟩ => ?_)
  obtain ⟨Y₂, T₂⟩ := nwR_keep C₁.inp F₂ C₁.inp.crt.room
  have C₂ := C₁.keepF2 K₂ (by decide) (by decide) F₂ (fun p hp => fitW p (wR_sub_nw len c p hp))
    (fun p hp => hdrW p (wR_sub_nw len c p hp))
  have sp₂ : t₂.gpr .esp = s.gpr .esp := (K₂.1 _ (by decide)).trans sp₁
  have hw : w32 t₂.mem base winOff < 16 := by
    rw [W₂, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
    have := val32_lt t₁.mem base (lo len (.slot c 8)) (cwc len c)
    simp only [sv]; omega
  -- Its entry.
  refine WP.seq (WP.mono (selectWindow_ok C₂.inp hw) fun t₃ ⟨O₃, S₃, K₃⟩ => ?_)
  have F₃ : Frame (frameR base (t₂.gpr .esp) (wR len c)) t₂.mem t₃.mem :=
    frameR_of_outside O₃ (by omega) (by simp)
  have C₃ := C₂.keepF2 K₃ (by decide) (by decide) F₃ fitW hdrW
  have sp₃ : t₃.gpr .esp = s.gpr .esp := (K₃.1 _ (by decide)).trans sp₂
  have S₃' : sv t₃.mem base len c 7 = b ^ w32 t₂.mem base winOff * 2 ^ (8 * bc len c) % M := by
    simp only [sv]; rw [S₃, T₂ _ hw, T₁ _ hw, hT _ hw]
  have Y₃ : sv t₃.mem base len c 6 = y ^ 16 * 2 ^ (8 * bc len c) % M := by
    simp only [sv]; rw [O₃.val32 (.inl (by omega)) (by omega)]; simp only [sv] at Y₂ V₁; rw [Y₂, V₁]
  have E₃ : sv t₃.mem base len c 8 = sv t₂.mem base len c 8 := by
    simp only [sv]; rw [O₃.val32 (.inr (by omega)) (by omega)]
  -- The product.
  refine WP.seq (WP.mono (cmul_ok C₃ (o := 6) (a := 6) (b := 7) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [S₃']; exact Nat.mod_lt _ (by omega))) fun t₄ ⟨C₄, K₄, F₄, L₄, V₄⟩ => ?_)
  obtain ⟨E₄, _⟩ := mulR6_keep C₃.inp F₄ C₃.inp.crt.room
  have sp₄ : t₄.gpr .esp = s.gpr .esp := (K₄.1 _ (by decide)).trans sp₃
  -- The count.
  have Kt : Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t₄ :=
    (((K₁.mono (by decide)).trans K₂).trans K₃).trans (K₄.mono (by decide))
  have esi₄ : t₄.gpr .esi = BitVec.ofNat 32 n := (Kt.1 _ (by decide)).trans he
  refine wp_subZ rfl fun u a₅ z₅ => WP.block_nil ?_
  have sub : BitVec.ofNat 32 n - 1 = BitVec.ofNat 32 (n - 1) :=
    VG.Proof.Mont.X86.Dynamic.counter_sub hn hn0
  refine ⟨C₄.regs a₅.keeps a₅.mem, ?_, (Kt.mono (by decide)).trans (a₅.keeps.mono (by decide)), ?_, ?_, ?_, ?_⟩
  · rw [a₅.mem]
    rw [sp₁] at F₂
    rw [sp₂] at F₃
    rw [sp₃] at F₄
    exact (((frameR_mono F₁ (wR_sub_mul len c)).trans (frameR_mono F₂ (wR_sub_nw len c))).trans F₃).trans
      (frameR_mono F₄ (wR_sub_mul len c))
  · rw [a₅.gpr, esi₄, sub]
  · rw [z₅, esi₄, sub]
    have z := VG.Proof.Mont.X86.Dynamic.counter_zero hn hn0
    rw [show ∀ x : BitVec 32, x - 0 = x from BitVec.sub_zero] at z
    rw [z]
  · rw [sv, a₅.mem]
    have v := VG.Proof.Dsa.mont_product C₃.coprime (a := y ^ 16) (b := b ^ w32 t₂.mem base winOff)
      (by rw [Y₃, Nat.mod_mod]) (by rw [S₃', Nat.mod_mod]) V₄
    rw [Nat.mod_eq_of_lt L₄, W₂, E₁] at v
    exact v
  · rw [sv, a₅.mem]; simp only [sv] at E₄ E₃ E₂ E₁ ⊢; rw [E₄, E₃, E₂, E₁]

end

end VG.Proof.Bignum.X86.CrtRt
