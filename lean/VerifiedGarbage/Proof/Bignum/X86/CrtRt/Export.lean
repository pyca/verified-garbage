module

import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Double
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Powers

/-! ### `Bignum.X86.CrtRt.Coefficient`, which this module and modules that import it used -/

section

/-! # The CRT coefficient

`subMod_ok`: slot 7 set to `(a + M - b) mod M` for the numbers `a` (slot 6)
and `b` (slot 5) below `M`. `coefficient_ok`: `h = (m_p - m_q mod p) qInv mod p`
into the wide slot 7, in the context of `p` (the modulus `safeM p`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.CrtRt

variable {Ex : List Region → List Region → Prop}

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86

/-- The ranges a subtraction modulo `M` changes. -/
abbrev subR (len : Nat) (c : Ctx) : List (Nat × Nat) :=
  [(maskOff, 4), (lo len (.slot c 1), bc len c), (lo len (.slot c 7), bc len c)]

/-- The result of a subtraction modulo `M`, from the borrow `c₁` of `a - b` and the carry `c₂` of
the difference plus `M`. -/
theorem subMod_value {a b M W D T : Nat} {c₁ c₂ : Bool} (ha : a < M) (hb : b < M)
    (hD : D < W) (hT : T < W) (h₁ : D + b = a + W * c₁.toNat) (h₂ : T + W * c₂.toNat = D + M) :
    (if c₁ then T else D) = (a + M - b) % M ∧ (if c₁ then T else D) < M := by
  cases c₁
  · simp only [Bool.toNat_false, Nat.mul_zero, Nat.add_zero, Bool.false_eq_true, ↓reduceIte] at h₁ ⊢
    exact ⟨by rw [show a + M - b = (a - b) + M by omega_using [h₁], Nat.add_mod_right, Nat.mod_eq_of_lt (by omega_using [ha])]; omega_using [h₁],
      by omega_using [ha, h₁]⟩
  · cases c₂ <;> simp only [Bool.toNat_true, Bool.toNat_false, Nat.mul_one, Nat.mul_zero, Nat.add_zero,
      ↓reduceIte] at h₁ h₂ ⊢
    · omega_using [hb, hT, h₂, h₁]
    · exact ⟨by rw [Nat.mod_eq_of_lt (by omega_using [ha, hD, h₁])]; omega_using [h₁, h₂], by omega_using [hD, h₂]⟩

section
variable {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {c : Ctx} {M : Nat}

theorem subMod_raw (C : CtxOk Ex base bytes len args c M s) :
    WP isa (subMod c 7 6 5) s fun u =>
      CtxOk Ex base bytes len args c M u ∧ Frame (frameR base (s.gpr .esp) (subR len c)) s.mem u.mem ∧
      (sv s.mem base len c 6 < M → sv s.mem base len c 5 < M →
        sv u.mem base len c 7 = (sv s.mem base len c 6 + M - sv s.mem base len c 5) % M) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s u := by
  have h := C.inp
  obtain f8 := h.slot_fit c (j := 8) (by decide)
  obtain bw := bc_eq_cwc len c
  obtain g := bc_ge h.lower' c
  have bl := h.bytes_lt
  have nw := h.scratch.nowrap
  have est : st len c = 2 * bc len c + 32 := rfl
  obtain z0 : lo len (.slot c 0) = numBase := sl_zero len c
  obtain e1 : lo len (.slot c 1) = numBase + st len c := by simp [lo]
  have e5 : lo len (.slot c 5) = numBase + 5 * st len c := rfl
  have e6 : lo len (.slot c 6) = numBase + 6 * st len c := rfl
  have e7 : lo len (.slot c 7) = numBase + 7 * st len c := rfl
  have e8 : lo len (.slot c 8) = numBase + 8 * st len c := rfl
  have nb : numBase = 3336 := rfl
  have mo : maskOff = 12 := rfl
  obtain cb1 : cb len (one c) = bc len c := by simp [cb, one]
  obtain cw1 : cw len (one c) = cwc len c := by simp [cw, cwc, cb, one]
  unfold subMod
  -- `a - b`, its borrow saved.
  refine WP.seq (WP.mono (chainSub_ok h (o := .slot c 7) (a := .slot c 6) (b := .slot c 5) (one_ok c)
    (by rw [cb1]; omega_arith) (by rw [cb1]; omega_arith) (by rw [cb1]; omega_arith) (by rw [cb1]; exact .inr (by omega_arith))
    (by rw [cb1]; exact .inr (by omega_arith))) fun u₁ ⟨O₁, _, ⟨c₁, k₁, V₁⟩, K₁⟩ => ?_)
  rw [cb1] at O₁
  rw [cw1] at V₁
  obtain h₁ := h.keep K₁ (by decide) (by decide) (O₁.mono (Nat.zero_le _) (by omega_arith))
  refine WP.seq (wp_storeS (h₁.scratch.ea (d := maskOff) (by omega_arith))
    (h₁.scratch.write (d := maskOff) (n := 4) (by omega_arith)) fun u₂ m₂ => WP.block_nil ?_)
  obtain O₂ : Outside base maskOff 4 u₁.mem u₂.mem := by rw [m₂.mem]; exact writeW32_outside _ _ _ (by omega_arith)
  obtain A₂ : u₂.mem.readW (off base maskOff) 32 = cmask c₁ := by rw [m₂.mem, Mem.readW_writeW_self32, k₁]
  obtain h₂ := h₁.keep (m₂.keeps []) (by decide) (by decide) (O₂.mono (Nat.zero_le _) (by omega_arith))
  -- The difference plus `M`.
  refine WP.seq (WP.mono (chainAdd_ok h₂ (o := .slot c 1) (a := .slot c 7) (b := .slot c 0) (one_ok c)
    (by rw [cb1]; omega_arith) (by rw [cb1]; omega_arith) (by rw [cb1]; omega_arith) (by rw [cb1]; exact .inl (by omega_arith))
    (by rw [cb1]; exact .inr (by omega_arith))) fun u₃ ⟨O₃, _, ⟨c₂, _, V₃⟩, K₃⟩ => ?_)
  rw [cb1] at O₃
  rw [cw1] at V₃
  obtain h₃ := h₂.keep K₃ (by decide) (by decide) (O₃.mono (Nat.zero_le _) (by omega_arith))
  -- The borrow back, and the selection.
  refine WP.seq (wp_movS (readSrc_sc h₃.scratch (d := maskOff) (by omega_arith)) fun u₄ a₄ _ => WP.block_nil ?_)
  obtain h₄ := h₃.regs a₄.keeps a₄.mem
  obtain ecx₄ : u₄.gpr .ecx = cmask c₁ := by
    rw [a₄.gpr, ← A₂]
    exact BitVec.eq_of_toNat_eq (O₃.w32 (d := maskOff) (.inl (by omega_arith)) (by omega_arith))
  refine WP.mono (select_ok h₄ (x := .slot c 1) (d := .slot c 7) (one_ok c) (by rw [cb1]; omega_arith)
    (by rw [cb1]; omega_arith) (by rw [cb1]; exact .inr (by omega_arith)) ecx₄) fun u ⟨O₅, V₅, K₅⟩ => ?_
  rw [cb1] at O₅
  rw [cw1, a₄.mem] at V₅
  -- The values.
  obtain A : val32 u₂.mem base (lo len (.slot c 7)) (cwc len c) = val32 u₁.mem base (lo len (.slot c 7)) (cwc len c) :=
    O₂.val32 (.inr (by omega_arith)) (by omega_arith)
  obtain M₂ : val32 u₂.mem base (lo len (.slot c 0)) (cwc len c) = M := by
    rw [O₂.val32 (.inr (by omega_arith)) (by omega_arith), O₁.val32 (.inl (by omega_arith)) (by omega_arith)]
    obtain hm := C.mod; simp only [sv] at hm; exact hm
  obtain D₃ : val32 u₃.mem base (lo len (.slot c 7)) (cwc len c) = val32 u₁.mem base (lo len (.slot c 7)) (cwc len c) := by
    rw [O₃.val32 (.inr (by omega_arith)) (by omega_arith), A]
  rw [A, M₂] at V₃
  rw [D₃] at V₅
  refine ⟨?_, ?_, fun ha hb => ?_, ?_⟩
  · refine C.keepF2 (regs := [.eax, .ebx, .ecx, .edx, .ebp]) ?_ (by decide) (by decide) (ws := subR len c) ?_ ?_ ?_
    · exact ((((K₁.mono (by decide)).trans ((m₂.keeps []).mono (by decide))).trans (K₃.mono (by decide))).trans
        (a₄.keeps.mono (by decide))).trans (K₅.mono (by decide))
    · exact ((((frameR_of_outside O₁ (by omega_arith) (by simp)).trans (frameR_of_outside O₂ (by omega_arith) (by simp))).trans
        (frameR_of_outside O₃ (by omega_arith) (by simp))).trans (by rw [← a₄.mem]; exact frameR_of_outside O₅ (by omega_arith) (by simp)))
    · intro p hp; simp only [subR, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl <;> dsimp only <;> omega_arith
    · intro p hp; simp only [subR, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl <;> dsimp only <;> omega_arith
  · exact (((frameR_of_outside O₁ (by omega_arith) (by simp)).trans (frameR_of_outside O₂ (by omega_arith) (by simp))).trans
      (frameR_of_outside O₃ (by omega_arith) (by simp))).trans (by rw [← a₄.mem]; exact frameR_of_outside O₅ (by omega_arith) (by simp))
  · have R := subMod_value (W := 2 ^ (32 * cwc len c)) ha hb (val32_lt _ _ _ _) (val32_lt _ _ _ _)
      (by simp only [sv] at *; omega_arith) V₃
    simp only [sv]; rw [V₅]; exact R.1
  · exact ((((K₁.mono (by decide)).trans ((m₂.keeps []).mono (by decide))).trans (K₃.mono (by decide))).trans
      (a₄.keeps.mono (by decide))).trans (K₅.mono (by decide))

theorem subMod_ok (C : CtxOk Ex base bytes len args c M s) (ha : sv s.mem base len c 6 < M)
    (hb : sv s.mem base len c 5 < M) :
    WP isa (subMod c 7 6 5) s fun u =>
      CtxOk Ex base bytes len args c M u ∧ Frame (frameR base (s.gpr .esp) (subR len c)) s.mem u.mem ∧
      sv u.mem base len c 7 = (sv s.mem base len c 6 + M - sv s.mem base len c 5) % M ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s u :=
  WP.mono (subMod_raw C) fun _ ⟨C', F, V, K⟩ => ⟨C', F, V ha hb, K⟩

/-- The ranges the coefficient changes: the inverse's and the saved mask's header words, and the
first nine wide slots. -/
abbrev coR (len : Nat) : List (Nat × Nat) := [(invOff, 4), (maskOff, 4), (numBase, 9 * st len .wide)]

/-- A range the coefficient changes. -/
abbrev InCo (len : Nat) (p : Nat × Nat) : Prop :=
  p = (invOff, 4) ∨ p = (maskOff, 4) ∨ Within p (numBase, 9 * st len .wide)

/-- The coefficient's ranges lie apart from the header words naming the factor. -/
theorem coR_hdr (len : Nat) : ∀ q ∈ coR len, 28 ≤ q.1 ∨ q.1 + q.2 ≤ 16 := by
  intro q hq
  simp only [coR, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact .inr (by decide)
  · exact .inr (by decide)
  · exact .inl (show 28 ≤ 3336 by decide)

theorem coR_fit (h : In Ex base bytes len args s) : ∀ q ∈ coR len, q.1 + q.2 ≤ bytes := by
  obtain f8 := h.slot_fit .wide (j := 8) (by decide)
  have e8 : lo len (.slot .wide 8) = numBase + 8 * st len .wide := rfl
  have nb : numBase = 3336 := rfl
  intro q hq
  simp only [coR, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl <;> simp only [invOff, maskOff] <;> omega_arith

theorem co_widen {sp : BitVec 32} {ws : List (Nat × Nat)} {m m' : Mem}
    (F : Frame (frameR base sp ws) m m')
    (hw : ∀ p ∈ ws, InCo len p) : Frame (frameR base sp (coR len)) m m' :=
  frameR_widen F fun p hp => by
    rcases hw p hp with rfl | rfl | w
    · exact ⟨_, by simp, Nat.le_refl _, Nat.le_refl _⟩
    · exact ⟨_, by simp, Nat.le_refl _, Nat.le_refl _⟩
    · exact ⟨_, by simp, w⟩

theorem co_of_outside (h : In Ex base bytes len args s) {sp : BitVec 32} {a n : Nat} {m m' : Mem}
    (O : Outside base a n m m') (w : Within (a, n) (numBase, 9 * st len .wide)) :
    Frame (frameR base sp (coR len)) m m' := by
  obtain fit := coR_fit h
  have := fit _ (by simp : (numBase, 9 * st len .wide) ∈ coR len)
  obtain ⟨_, w2⟩ := w
  simp only at w2
  refine co_widen (ws := [(a, n)]) (frameR_of_outside O (by omega_using [w2, this, h.bytes_lt]) (by simp)) ?_
  intro p hp
  obtain rfl := List.mem_singleton.mp hp
  exact .inr (.inr ⟨by assumption, w2⟩)

theorem prepR_co (h : In Ex base bytes len args s) (c : Ctx) : ∀ p ∈ prepR len c, InCo len p := by
  intro p hp
  obtain g := bc_ge h.lower' c
  simp only [prepR, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · exact .inl rfl
  · exact .inr (.inr (slot_in h c (by decide)))
  · exact .inr (.inr ⟨(slot1_in h c).1, by have := (slot1_in h c).2; dsimp only at *; omega_using [this]⟩)
  · exact .inr (.inr (slot_in h c (by decide)))
  · exact .inr (.inr (slot_in h c (by decide)))
  · exact .inr (.inr (slot_in h c (by decide)))

theorem mulR_co (h : In Ex base bytes len args s) (c : Ctx) {j : Nat} (hj : j ≤ 8) :
    ∀ p ∈ mulR len c j, InCo len p := by
  intro p hp
  simp only [mulR, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact .inr (.inr (slot_in h c hj))
  · exact .inr (.inr (slot1_in h c))

theorem subR_co (h : In Ex base bytes len args s) (c : Ctx) : ∀ p ∈ subR len c, InCo len p := by
  intro p hp
  simp only [subR, List.mem_cons, List.not_mem_nil, or_false] at hp
  obtain g := bc_ge h.lower' c
  rcases hp with rfl | rfl | rfl
  · exact .inr (.inl rfl)
  · exact .inr (.inr ⟨(slot1_in h c).1, by have := (slot1_in h c).2; dsimp only at *; omega_using [this]⟩)
  · exact .inr (.inr (slot_in h c (by decide)))

/-- A subtraction modulo `M` keeps slots 3, 4 and 8. -/
theorem subR_sv (h : In Ex base bytes len args s) (c : Ctx) {sp : BitVec 32} {m m' : Mem}
    (F : Frame (frameR base sp (subR len c)) m m') (R : CallRoom sp base bytes) {j : Nat}
    (hj3 : 3 ≤ j) (hj : j ≤ 8) (h7 : j ≠ 7) : sv m' base len c j = sv m base len c j := by
  have nw := h.scratch.nowrap
  obtain f8 := h.slot_fit c (j := 8) (by decide)
  obtain bw := bc_eq_cwc len c
  have est : st len c = 2 * bc len c + 32 := rfl
  obtain j8 : lo len (.slot c j) ≤ lo len (.slot c 8) := by
    have := Nat.mul_le_mul_right (st len c) hj; simp only [lo]; omega_using [this]
  obtain a7 := slot_apart len c (o := 7) (j := j) h7
  obtain p1 := slot_past1 len c (j := j) hj3
  obtain z0 : lo len (.slot c 0) = numBase := sl_zero len c
  obtain e1 : lo len (.slot c 1) = numBase + st len c := by simp [lo]
  have nb : numBase = 3336 := rfl
  obtain fit : ∀ p ∈ subR len c, p.1 + p.2 ≤ bytes := by
    obtain e7 : lo len (.slot c 7) + st len c ≤ lo len (.slot c 8) := sl_le c (by decide)
    intro p hp; simp only [subR, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> simp only [maskOff] <;> omega_arith
  refine frameR_val32 F R nw (by omega_using [f8, bw, est, j8]) ?_ fit
  intro p hp
  simp only [subR, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> simp only [maskOff] <;> omega_arith

/-- The coefficient from the context of `p`: `m_q` (slot 5) reduced by Montgomery multiplications,
subtracted from `m_p` (slot 6) modulo `M`, and multiplied by `qInv` (slot 8). -/
theorem coArith_ok (C : CtxOk Ex base bytes len args .wide M s) {mp mq qi : Nat}
    (h3 : sv s.mem base len .wide 3 = 1) (h4 : sv s.mem base len .wide 4 = 2 ^ (16 * bc len .wide) % M)
    (h6 : sv s.mem base len .wide 6 = mp) (hmp : mp < M) (h5 : sv s.mem base len .wide 5 = mq)
    (h8 : sv s.mem base len .wide 8 = qi) :
    WP isa (.seq (mul .wide 5 5 4) <| .seq (mul .wide 5 5 3) <| .seq (subMod .wide 7 6 5) <|
      .seq (mul .wide 8 8 4) (mul .wide 7 7 8)) s fun u =>
      CtxOk Ex base bytes len args .wide M u ∧ Frame (frameR base (s.gpr .esp) (coR len)) s.mem u.mem ∧
      sv u.mem base len .wide 7 = ((mp + M - mq % M) % M * qi) % M ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u := by
  have h := C.inp
  have hM := C.gt
  obtain g := bc_ge h.lower' .wide
  obtain RR : 2 ^ (16 * bc len .wide) = 2 ^ (8 * bc len .wide) * 2 ^ (8 * bc len .wide) := by
    rw [← Nat.pow_add]; congr 1; omega_using []
  -- `m_q R mod M`, then `m_q mod M`.
  refine WP.seq (WP.mono (cmul_ok C (o := 5) (a := 5) (b := 4) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [h4]; exact Nat.mod_lt _ (by omega_using [hmp]))) fun u₁ ⟨C₁, K₁, F₁, L₁, V₁⟩ => ?_)
  obtain B₁ : sv u₁.mem base len .wide 5 = mq * 2 ^ (8 * bc len .wide) % M := by
    obtain v := VG.Proof.Dsa.mont_scale C.coprime (out := sv u₁.mem base len .wide 5) (input := mq)
      (c := 2 ^ (8 * bc len .wide)) (by rw [V₁, h5, h4, RR])
    rwa [Nat.mod_eq_of_lt L₁] at v
  obtain o₁ := mulR_sv C.inp F₁ C.inp.room (j := 3) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain f₁ := mulR_sv C.inp F₁ C.inp.room (j := 4) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain m₁ := mulR_sv C.inp F₁ C.inp.room (j := 6) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain q₁ := mulR_sv C.inp F₁ C.inp.room (j := 8) (by decide) (by decide) (by decide) (by decide) (by decide)
  refine WP.seq (WP.mono (cmul_ok C₁ (o := 5) (a := 5) (b := 3) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [o₁, h3]; exact hM)) fun u₂ ⟨C₂, K₂, F₂, L₂, V₂⟩ => ?_)
  obtain D₂ : sv u₂.mem base len .wide 5 = mq % M := by
    obtain v := VG.Proof.Dsa.mont_decode (A := sv u₁.mem base len .wide 5) (out := sv u₂.mem base len .wide 5)
      C.coprime (by rw [B₁, Nat.mod_mod]) (by rw [V₂, o₁, h3])
    rwa [Nat.mod_eq_of_lt L₂] at v
  obtain f₂ := mulR_sv C₁.inp F₂ C₁.inp.room (j := 4) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain m₂ := mulR_sv C₁.inp F₂ C₁.inp.room (j := 6) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain q₂ := mulR_sv C₁.inp F₂ C₁.inp.room (j := 8) (by decide) (by decide) (by decide) (by decide) (by decide)
  -- The difference modulo `M`.
  refine WP.seq (WP.mono (subMod_ok C₂ (by rw [m₂, m₁, h6]; exact hmp) (by rw [D₂]; exact Nat.mod_lt _ (by omega_using [hmp])))
    fun u₃ ⟨C₃, F₃, S₃, K₃⟩ => ?_)
  rw [m₂, m₁, h6, D₂] at S₃
  obtain f₃ : sv u₃.mem base len .wide 4 = sv u₂.mem base len .wide 4 :=
    subR_sv C₂.inp .wide F₃ C₂.inp.room (by decide) (by decide) (by decide)
  obtain q₃ : sv u₃.mem base len .wide 8 = sv u₂.mem base len .wide 8 :=
    subR_sv C₂.inp .wide F₃ C₂.inp.room (by decide) (by decide) (by decide)
  -- `qInv R mod M`, and the product.
  refine WP.seq (WP.mono (cmul_ok C₃ (o := 8) (a := 8) (b := 4) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [f₃, f₂, f₁, h4]; exact Nat.mod_lt _ (by omega_using [hmp]))) fun u₄ ⟨C₄, K₄, F₄, L₄, V₄⟩ => ?_)
  obtain Q₄ : sv u₄.mem base len .wide 8 = qi * 2 ^ (8 * bc len .wide) % M := by
    obtain v := VG.Proof.Dsa.mont_scale C.coprime (out := sv u₄.mem base len .wide 8) (input := qi)
      (c := 2 ^ (8 * bc len .wide)) (by rw [V₄, q₃, q₂, q₁, h8, f₃, f₂, f₁, h4, RR])
    rwa [Nat.mod_eq_of_lt L₄] at v
  obtain s₄ := mulR_sv C₃.inp F₄ C₃.inp.room (j := 7) (by decide) (by decide) (by decide) (by decide) (by decide)
  refine WP.mono (cmul_ok C₄ (o := 7) (a := 7) (b := 8) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [Q₄]; exact Nat.mod_lt _ (by omega_using [hmp]))) fun u ⟨C₅, K₅, F₅, L₅, V₅⟩ =>
      ⟨C₅, ?_, ?_, ?_⟩
  · have sp₁ : u₁.gpr .esp = s.gpr .esp := K₁.1 _ (by decide)
    obtain sp₂ : u₂.gpr .esp = s.gpr .esp := (K₂.1 _ (by decide)).trans sp₁
    obtain sp₃ : u₃.gpr .esp = s.gpr .esp := (K₃.1 _ (by decide)).trans sp₂
    obtain sp₄ : u₄.gpr .esp = s.gpr .esp := (K₄.1 _ (by decide)).trans sp₃
    rw [sp₁] at F₂
    rw [sp₂] at F₃
    rw [sp₃] at F₄
    rw [sp₄] at F₅
    exact (((((co_widen F₁ (mulR_co h .wide (by decide))).trans (co_widen F₂ (mulR_co h .wide (by decide)))).trans
      (co_widen F₃ (subR_co h .wide))).trans (co_widen F₄ (mulR_co h .wide (by decide)))).trans
      (co_widen F₅ (mulR_co h .wide (by decide))))
  · have v := VG.Proof.Dsa.mont_scale C.coprime (out := sv u.mem base len .wide 7)
      (input := (mp + M - mq % M) % M) (c := qi) (by rw [V₅, s₄, S₃, Q₄])
    rwa [Nat.mod_eq_of_lt L₅] at v
  · exact ((((K₁.trans K₂).mono (by decide)).trans K₃).mono (by decide) |>.trans
      ((K₄.trans K₅).mono (by decide)))

/-- A wide slot from 9 on into the wide slot `d` below 9. -/
theorem copyDown_ok (h : In Ex base bytes len args s) {j d : Nat} (hj9 : 9 ≤ j) (hj : j ≤ 17) (hd : d ≤ 8) :
    WP isa (copy (.slot .wide j) (.slot .wide d) (one .wide)) s fun u =>
      Outside base (lo len (.slot .wide d)) (bc len .wide) s.mem u.mem ∧
      sv u.mem base len .wide d = val32 s.mem base (lo len (.slot .wide j)) (cwc len .wide) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s u := by
  obtain f18 := h.slot_fit .wide (j := 18) (by decide)
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  obtain a := Nat.mul_le_mul_right (st len .wide) hj9
  obtain b := Nat.mul_le_mul_right (st len .wide) (show j + 1 ≤ 18 by omega_using [hj])
  obtain c := Nat.mul_le_mul_right (st len .wide) (show d + 1 ≤ 9 by omega_using [hd])
  rw [Nat.succ_mul] at b c
  have ej : lo len (.slot .wide j) = numBase + j * st len .wide := rfl
  have ed : lo len (.slot .wide d) = numBase + d * st len .wide := rfl
  have e18 : lo len (.slot .wide 18) = numBase + 18 * st len .wide := rfl
  obtain cb1 : cb len (one .wide) = bc len .wide := by simp [cb, one]
  obtain cw1 : cw len (one .wide) = cwc len .wide := by simp [cw, cwc, cb, one]
  refine WP.mono (copy_ok h (x := .slot .wide j) (d := .slot .wide d) (one_ok .wide) (by rw [cb1]; omega_using [f18, est, b, ej, e18])
    (by rw [cb1]; omega_using [f18, est, c, ed, e18]) (by rw [cb1]; exact .inl (by omega_using [est, a, c, ej, ed]))) fun u ⟨O, V, K⟩ => ⟨?_, ?_, K⟩
  · rw [cb1] at O; exact O
  · rw [cw1] at V; exact V

/-- The coefficient's changes keep the wide slots from 9 on. -/
theorem coR_keep (h : In Ex base bytes len args s) {sp : BitVec 32} {m m' : Mem}
    (F : Frame (frameR base sp (coR len)) m m') (R : CallRoom sp base bytes) {d k : Nat}
    (hd : lo len (.slot .wide 9) ≤ d) (hk : d + 4 * k ≤ bytes) : val32 m' base d k = val32 m base d k := by
  have e9 : lo len (.slot .wide 9) = numBase + 9 * st len .wide := rfl
  have nb : numBase = 3336 := rfl
  refine low_keep h F R (coR_fit h) ?_ hd hk
  intro p hp; simp only [coR, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> simp only [invOff, maskOff] <;> omega_arith

/-- `h = (m_p - m_q mod p) qInv mod p` into the wide slot 7, for `p` (wide slot 10), `m_p` and `m_q`
(wide slots 16 and 17) and `qInv` (wide slot 14), in the context of `p`. -/
theorem wideCoefficient_ok (h : In Ex base bytes len args s) {p mp mq qi : Nat}
    (hp : val32 s.mem base (lo len (.slot .wide 10)) (cwc len .wide) = p)
    (hmp : val32 s.mem base (lo len (.slot .wide 16)) (cwc len .wide) = mp) (hmpl : mp < safeM p)
    (hmq : val32 s.mem base (lo len (.slot .wide 17)) (cwc len .wide) = mq)
    (hqi : val32 s.mem base (lo len (.slot .wide 14)) (cwc len .wide) = qi) {pc : Option Nat}
    (P : PreG s base bytes len args pc (safeM p)) (pfit : FitG len args pc .wide) :
    WP isa (wideCoefficient pc.isSome) s fun u =>
      Frame (frameR base (s.gpr .esp) (coR len)) s.mem u.mem ∧
      sv u.mem base len .wide 7 = ((mp + safeM p - mq % safeM p) % safeM p * qi) % safeM p ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u := by
  obtain f18 := h.slot_fit .wide (j := 18) (by decide)
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  obtain bw := bc_eq_cwc len .wide
  have e9 : lo len (.slot .wide 9) = numBase + 9 * st len .wide := rfl
  have e18 : lo len (.slot .wide 18) = numBase + 18 * st len .wide := rfl
  have e3 : lo len (.slot .wide 3) = numBase + 3 * st len .wide := rfl
  have e4 : lo len (.slot .wide 4) = numBase + 4 * st len .wide := rfl
  have e5 : lo len (.slot .wide 5) = numBase + 5 * st len .wide := rfl
  have e6 : lo len (.slot .wide 6) = numBase + 6 * st len .wide := rfl
  have e8 : lo len (.slot .wide 8) = numBase + 8 * st len .wide := rfl
  have bl := h.bytes_lt
  obtain hi : ∀ {j : Nat}, 9 ≤ j → j ≤ 17 → lo len (.slot .wide 9) ≤ lo len (.slot .wide j) ∧
      lo len (.slot .wide j) + 4 * cwc len .wide ≤ bytes := fun {j} hj9 hj => by
    obtain a := Nat.mul_le_mul_right (st len .wide) hj9
    obtain c := Nat.mul_le_mul_right (st len .wide) (show j + 1 ≤ 18 by omega_arith)
    rw [Nat.succ_mul] at c
    have ej : lo len (.slot .wide j) = numBase + j * st len .wide := rfl
    omega_arith
  have room := h.room
  -- Reading the key's components through the coefficient's frame.
  obtain rd : ∀ {u : State} {j : Nat}, Frame (frameR base (s.gpr .esp) (coR len)) s.mem u.mem → 9 ≤ j → j ≤ 17 →
      val32 u.mem base (lo len (.slot .wide j)) (cwc len .wide) =
        val32 s.mem base (lo len (.slot .wide j)) (cwc len .wide) := fun F hj9 hj =>
    coR_keep h F room (hi hj9 hj).1 (hi hj9 hj).2
  obtain cs : ∀ {j : Nat}, j ≤ 8 → Within (lo len (.slot .wide j), bc len .wide) (numBase, 9 * st len .wide) :=
    fun hj => slot_in h .wide hj
  unfold wideCoefficient
  refine WP.seq (WP.mono (copyDown_ok h (j := 10) (d := 0) (by decide) (by decide) (by decide))
    fun u₁ ⟨O₁, V₁, K₁⟩ => ?_)
  obtain F₁ : Frame (frameR base (s.gpr .esp) (coR len)) s.mem u₁.mem := co_of_outside h O₁ (cs (by decide))
  obtain h₁ := h.keepF K₁ (by decide) (by decide) F₁ (coR_fit h)
  obtain P₁ := P.keepF h K₁ (by decide) F₁ (coR_fit h) (coR_hdr len)
  refine WP.seq (WP.mono (prepareG_ok h₁ .wide (by rw [V₁, hp]; exact P₁) pfit) fun u₂ ⟨C₂, one₂, R₂, F₂, K₂⟩ => ?_)
  rw [V₁, hp] at C₂ R₂
  obtain sp₁ : u₁.gpr .esp = s.gpr .esp := K₁.1 _ (by decide)
  rw [sp₁] at F₂
  obtain F₁₂ := F₁.trans (co_widen F₂ (prepR_co h₁ .wide))
  have h₂ := C₂.inp
  refine WP.seq (WP.mono (copyDown_ok h₂ (j := 16) (d := 6) (by decide) (by decide) (by decide))
    fun u₃ ⟨O₃, V₃, K₃⟩ => ?_)
  rw [rd F₁₂ (by decide) (by decide), hmp] at V₃
  obtain F₃ := F₁₂.trans (co_of_outside h O₃ (cs (by decide)))
  obtain h₃ := h₂.keep K₃ (by decide) (by decide) (O₃.mono (Nat.zero_le _) (by omega_arith))
  refine WP.seq (WP.mono (copyDown_ok h₃ (j := 17) (d := 5) (by decide) (by decide) (by decide))
    fun u₄ ⟨O₄, V₄, K₄⟩ => ?_)
  rw [rd F₃ (by decide) (by decide), hmq] at V₄
  obtain F₄ := F₃.trans (co_of_outside h O₄ (cs (by decide)))
  obtain h₄ := h₃.keep K₄ (by decide) (by decide) (O₄.mono (Nat.zero_le _) (by omega_arith))
  refine WP.seq (WP.mono (copyDown_ok h₄ (j := 14) (d := 8) (by decide) (by decide) (by decide))
    fun u₅ ⟨O₅, V₅, K₅⟩ => ?_)
  rw [rd F₄ (by decide) (by decide), hqi] at V₅
  obtain F₅ := F₄.trans (co_of_outside h O₅ (cs (by decide)))
  -- The context, kept by the copies.
  obtain K₃₅ : Keeps [.eax, .ebx, .ecx, .edx, .ebp] u₂ u₅ := (K₃.trans K₄).trans K₅
  obtain C₅ : CtxOk Ex base bytes len args .wide (safeM p) u₅ := by
    refine C₂.keepF K₃₅ (by decide) (by decide)
      (ws := [(lo len (.slot .wide 6), bc len .wide), (lo len (.slot .wide 5), bc len .wide),
        (lo len (.slot .wide 8), bc len .wide)]) ?_ ?_ ?_
    · have sp₂ : u₂.gpr .esp = u₁.gpr .esp := K₂.1 _ (by decide)
      exact ((frameR_of_outside O₃ (by omega_arith) (by simp)).trans ((frameR_of_outside O₄ (by omega_arith) (by simp)).trans
        (frameR_of_outside O₅ (by omega_arith) (by simp))))
    · intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl <;> dsimp only <;> omega_arith
    · intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl <;> dsimp only <;> omega_arith
  obtain k35 : ∀ {j}, 3 ≤ j → j ≤ 4 → sv u₅.mem base len .wide j = sv u₂.mem base len .wide j := fun {j} hj3 hj => by
    have ej : lo len (.slot .wide j) = numBase + j * st len .wide := rfl
    have := Nat.mul_le_mul_right (st len .wide) hj
    have := Nat.mul_le_mul_right (st len .wide) hj3
    simp only [sv]
    rw [O₅.val32 (.inl (by omega_arith)) (by omega_arith), O₄.val32 (.inl (by omega_arith)) (by omega_arith),
      O₃.val32 (.inl (by omega_arith)) (by omega_arith)]
  obtain M6 : sv u₅.mem base len .wide 6 = mp := by
    simp only [sv]; rw [O₅.val32 (.inl (by omega_arith)) (by omega_arith),
      O₄.val32 (.inr (by omega_arith)) (by omega_arith)]; exact V₃
  obtain M5 : sv u₅.mem base len .wide 5 = mq := by
    simp only [sv]; rw [O₅.val32 (.inl (by omega_arith)) (by omega_arith)]; exact V₄
  refine WP.mono (coArith_ok C₅ (mp := mp) (mq := mq) (qi := qi) (by rw [k35 (by decide) (by decide), one₂])
    (by rw [k35 (by decide) (by decide), R₂]) M6 hmpl M5 V₅) fun u ⟨_, F, V, K⟩ => ⟨?_, V, ?_⟩
  · have sp₅ : u₅.gpr .esp = s.gpr .esp :=
      (K₃₅.1 _ (by decide)).trans ((K₂.1 _ (by decide)).trans sp₁)
    rw [sp₅] at F
    exact F₅.trans F
  · exact ((((K₁.mono (by decide)).trans K₂).trans (K₃₅.mono (by decide))).trans K)

/-- The coefficient at half the width, into the wide slot 7: `qInv` and `m_q` (wide slots 14 and 17,
`2 Bh` bytes) reduced modulo `p` in its half context, `m_p` (wide slot 16) copied, and their
difference times `qInv`, zero-extended. -/
theorem narrowCoefficient_ok (h : In Ex base bytes len args s) {p mp mq qi : Nat}
    (hp : val32 s.mem base (lo len (.slot .wide 10)) (cwc len .wide) = p) (hpn : p < 2 ^ (32 * cwc len .half))
    (hmp : val32 s.mem base (lo len (.slot .wide 16)) (cwc len .half) = mp) (hmpl : mp < safeM p)
    (hmq : val32 s.mem base (lo len (.slot .wide 17)) (2 * cwc len .half) = mq)
    (hqi : val32 s.mem base (lo len (.slot .wide 14)) (2 * cwc len .half) = qi) {pc : Option Nat}
    (P : PreG s base bytes len args pc (safeM p)) (pfit : FitG len args pc .half) :
    WP isa (narrowCoefficient pc.isSome) s fun u =>
      Frame (frameR base (s.gpr .esp) (coR len)) s.mem u.mem ∧
      val32 u.mem base (lo len (.slot .wide 7)) (2 * cwc len .wide) =
        ((mp + safeM p - mq % safeM p) % safeM p * qi) % safeM p ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u := by
  obtain f18 := h.slot_fit .wide (j := 18) (by decide)
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  obtain bw := bc_eq_cwc len .wide
  obtain ⟨cwle, cw8, bh, h0, h5, h8, sth, top⟩ := HalfLay.mk' h
  obtain hb2 := bc_half_le' len
  have e9 : lo len (.slot .wide 9) = numBase + 9 * st len .wide := rfl
  have e10 : lo len (.slot .wide 10) = numBase + 10 * st len .wide := rfl
  have e7 : lo len (.slot .wide 7) = numBase + 7 * st len .wide := rfl
  have e18 : lo len (.slot .wide 18) = numBase + 18 * st len .wide := rfl
  have e16 : lo len (.slot .wide 16) = numBase + 16 * st len .wide := rfl
  obtain bhw := bc_le_wide len .half
  have h6 : lo len (.slot .half 6) = numBase + 6 * st len .half := rfl
  have bl := h.bytes_lt
  obtain cb1 : cb len (one .half) = bc len .half := by simp [cb, one]
  obtain cw1 : cw len (one .half) = cwc len .half := by simp [cw, cwc, cb, one]
  obtain hM := safeM_gt p
  obtain hi : ∀ {j : Nat}, 9 ≤ j → j ≤ 17 → lo len (.slot .wide 9) ≤ lo len (.slot .wide j) ∧
      lo len (.slot .wide j) + 4 * (2 * cwc len .wide) ≤ bytes := fun {j} hj9 hj => by
    obtain a := Nat.mul_le_mul_right (st len .wide) hj9
    obtain c := Nat.mul_le_mul_right (st len .wide) (show j + 1 ≤ 18 by omega_arith)
    rw [Nat.succ_mul] at c
    have ej : lo len (.slot .wide j) = numBase + j * st len .wide := rfl
    omega_arith
  -- Reading the wide slots from 9 on through the coefficient's frame.
  obtain rd : ∀ {u : State} {j k : Nat}, Frame (frameR base (s.gpr .esp) (coR len)) s.mem u.mem → 9 ≤ j → j ≤ 17 →
      k ≤ 2 * cwc len .wide → val32 u.mem base (lo len (.slot .wide j)) k = val32 s.mem base (lo len (.slot .wide j)) k :=
    fun F hj9 hj hk => coR_keep h F h.room (hi hj9 hj).1 (by have := (hi hj9 hj).2; omega_arith)
  obtain ctxw : ∀ {sp : BitVec 32} {m m' : Mem}, Frame (frameR base sp [(numBase, 9 * st len .wide)]) m m' →
      Frame (frameR base sp (coR len)) m m' := fun F =>
    co_widen F fun q hq => by rw [List.mem_singleton.mp hq]; exact .inr (.inr ⟨Nat.le_refl _, Nat.le_refl _⟩)
  obtain split : cwc len .half + (cwc len .wide - cwc len .half) = cwc len .wide := by omega_arith
  obtain P₀ : val32 s.mem base (lo len (.slot .wide 10)) (cwc len .half) = p :=
    val32_low (b := cwc len .wide - cwc len .half) (by rw [split, hp]) hpn
  unfold narrowCoefficient
  -- `p` and its half context.
  refine WP.seq (WP.mono (copy_ok h (x := .slot .wide 10) (d := .slot .half 0) (one_ok .half)
    (by rw [cb1]; omega_arith) (by rw [cb1, h0]; omega_arith) (by rw [cb1, h0]; exact .inl (by omega_arith)))
    fun u₁ ⟨O₁, V₁, K₁⟩ => ?_)
  rw [cb1] at O₁
  rw [cw1, P₀] at V₁
  obtain F₁ : Frame (frameR base (s.gpr .esp) (coR len)) s.mem u₁.mem := co_of_outside h O₁ (slot_in h .half (by decide))
  obtain h₁ := h.keepF K₁ (by decide) (by decide) F₁ (coR_fit h)
  obtain P₁ := P.keepF h K₁ (by decide) F₁ (coR_fit h) (coR_hdr len)
  refine WP.seq (WP.mono (prepareG_ok h₁ .half (by rw [show sv u₁.mem base len .half 0 = p from V₁]; exact P₁) pfit)
    fun u₂ ⟨C₂, one₂, R₂, F₂, K₂⟩ => ?_)
  rw [show sv u₁.mem base len .half 0 = p from V₁] at C₂ R₂
  obtain sp₁ : u₁.gpr .esp = s.gpr .esp := K₁.1 _ (by decide)
  rw [sp₁] at F₂
  obtain F₁₂ := F₁.trans (co_widen F₂ (prepR_co h₁ .half))
  -- `qInv mod p`, in Montgomery form in slot 8.
  refine WP.seq (WP.mono (reduceHalf_ok C₂ one₂ R₂ (j := 14) (X := qi) (by decide) (by decide)
    (by rw [rd F₁₂ (by decide) (by decide) (by omega_arith), hqi]))
    fun u₃ ⟨C₃, one₃, R₃, B₃, _, F₃, K₃⟩ => ?_)
  obtain sp₂ : u₂.gpr .esp = s.gpr .esp := (K₂.1 _ (by decide)).trans sp₁
  rw [sp₂] at F₃
  obtain F₁₃ := F₁₂.trans (ctxw F₃)
  refine WP.seq (WP.mono (cmul_ok C₃ (o := 8) (a := 5) (b := 4) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [R₃]; exact Nat.mod_lt _ (by omega_arith))) fun u₄ ⟨C₄, K₄, F₄, L₄, V₄⟩ => ?_)
  obtain Q₄ : sv u₄.mem base len .half 8 % safeM p = qi % safeM p * 2 ^ (8 * bc len .half) % safeM p := by
    obtain RR : 2 ^ (16 * bc len .half) = 2 ^ (8 * bc len .half) * 2 ^ (8 * bc len .half) := by
      rw [← Nat.pow_add]; congr 1; omega_arith
    exact VG.Proof.Dsa.mont_scale C₃.coprime (by rw [V₄, B₃, R₃, RR])
  obtain o₄ := mulR_sv C₃.inp F₄ C₃.inp.room (j := 3) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain f₄ := mulR_sv C₃.inp F₄ C₃.inp.room (j := 4) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain sp₃ : u₃.gpr .esp = s.gpr .esp := (K₃.1 _ (by decide)).trans sp₂
  rw [sp₃] at F₄
  obtain F₁₄ := F₁₃.trans (co_widen F₄ (mulR_co h .half (by decide)))
  -- `m_q mod p`.
  refine WP.seq (WP.mono (reduceHalf_ok C₄ (by rw [o₄, one₃]) (by rw [f₄, R₃]) (j := 17) (X := mq) (by decide) (by decide)
    (by rw [rd F₁₄ (by decide) (by decide) (by omega_arith), hmq]))
    fun u₅ ⟨C₅, _, _, B₅, E₅, F₅, K₅⟩ => ?_)
  obtain sp₄ : u₄.gpr .esp = s.gpr .esp := (K₄.1 _ (by decide)).trans sp₃
  rw [sp₄] at F₅
  obtain F₁₅ := F₁₄.trans (ctxw F₅)
  -- `m_p` into slot 6.
  refine WP.seq (WP.mono (copy_ok C₅.inp (x := .slot .wide 16) (d := .slot .half 6) (one_ok .half)
    (by rw [cb1]; omega_arith) (by rw [cb1, h6]; omega_arith) (by rw [cb1, h6]; exact .inl (by omega_arith)))
    fun u₆ ⟨O₆, V₆, K₆⟩ => ?_)
  rw [cb1] at O₆
  rw [cw1, rd F₁₅ (by decide) (by decide) (by omega_arith), hmp] at V₆
  obtain sp₅ : u₅.gpr .esp = s.gpr .esp := (K₅.1 _ (by decide)).trans sp₄
  obtain C₆ := C₅.keepF K₆ (by decide) (by decide)
    (frameR_of_outside (ws := [(lo len (.slot .half 6), bc len .half)]) O₆ (by omega_arith) (by simp))
    (by simp; omega_arith) (by simp; omega_arith)
  obtain F₁₆ := F₁₅.trans (by rw [← sp₅]; exact co_of_outside h O₆ (slot_in h .half (by decide)))
  obtain m₆ : sv u₆.mem base len .half 5 = sv u₅.mem base len .half 5 := by
    simp only [sv]; rw [O₆.val32 (.inl (by omega_arith)) (by omega_arith)]
  obtain q₆ : sv u₆.mem base len .half 8 = sv u₅.mem base len .half 8 := by
    simp only [sv]; rw [O₆.val32 (.inr (by omega_arith)) (by omega_arith)]
  -- The difference, and its product with `qInv`.
  refine WP.seq (WP.mono (subMod_ok C₆ (by simp only [sv]; rw [V₆]; exact hmpl)
    (by rw [m₆, B₅]; exact Nat.mod_lt _ (by omega_arith))) fun u₇ ⟨C₇, F₇, S₇, K₇⟩ => ?_)
  obtain q₇ : sv u₇.mem base len .half 8 = sv u₆.mem base len .half 8 :=
    subR_sv C₆.inp .half F₇ C₆.inp.room (by decide) (by decide) (by decide)
  obtain sp₆ : u₆.gpr .esp = s.gpr .esp := (K₆.1 _ (by decide)).trans sp₅
  rw [sp₆] at F₇
  obtain F₁₇ := F₁₆.trans (co_widen F₇ (subR_co h .half))
  obtain Q₇ : sv u₇.mem base len .half 8 = sv u₄.mem base len .half 8 := by rw [q₇, q₆, E₅]
  refine WP.seq (WP.mono (cmul_ok C₇ (o := 6) (a := 7) (b := 8) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [Q₇]; exact L₄)) fun u₈ ⟨C₈, K₈, F₈, L₈, V₈⟩ => ?_)
  obtain H₈ : sv u₈.mem base len .half 6 = ((mp + safeM p - mq % safeM p) % safeM p * qi) % safeM p := by
    obtain v := VG.Proof.Dsa.mont_scale C₇.coprime (out := sv u₈.mem base len .half 6)
      (input := sv u₇.mem base len .half 7) (c := qi % safeM p)
      (by rw [V₈, Q₇, ← Nat.mod_eq_of_lt L₄, Q₄])
    rw [Nat.mod_eq_of_lt L₈, S₇, m₆, B₅] at v
    rw [v, show sv u₆.mem base len .half 6 = mp from V₆, Nat.mul_mod_mod]
  obtain sp₇ : u₇.gpr .esp = s.gpr .esp := (K₇.1 _ (by decide)).trans sp₆
  rw [sp₇] at F₈
  obtain F₁₈ := F₁₇.trans (co_widen F₈ (mulR_co h .half (by decide)))
  -- Into the wide slot 7.
  refine WP.mono (saveResultAt_ok C₈.inp .half (o := 7) (by decide) (by omega_arith)) fun u ⟨O₉, V₉, K₉⟩ =>
    ⟨?_, ?_, ?_⟩
  · exact F₁₈.trans (co_of_outside h O₉ ⟨by omega_arith, by dsimp only; omega_arith⟩)
  · rw [V₉, H₈]
  · exact ((((((K₁.mono (by decide)).trans K₂).trans (K₃.mono (by decide))).trans (K₄.mono (by decide))).trans
      (K₅.mono (by decide))).trans ((K₆.trans K₇).mono (by decide))).trans ((K₈.mono (by decide)).trans
      (K₉.mono (by decide)))

/-- The coefficient, at half the width if `p`'s length (the header word at `lenOff`) fits it. -/
theorem coefficient_ok (h : In Ex base bytes len args s) {p mp mq qi : Nat}
    (hp : val32 s.mem base (lo len (.slot .wide 10)) (cwc len .wide) = p)
    (hmp : val32 s.mem base (lo len (.slot .wide 16)) (2 * cwc len .wide) = mp) (hmpl : mp < safeM p)
    (hmq : val32 s.mem base (lo len (.slot .wide 17)) (2 * cwc len .wide) = mq) (hmqb : mq < 2 ^ (32 * cwc len .wide))
    (hqi : val32 s.mem base (lo len (.slot .wide 14)) (2 * cwc len .wide) = qi) (hqib : qi < 2 ^ (32 * cwc len .wide))
    (hpw : p < 2 ^ (32 * cwc len .wide))
    (fits : w32 s.mem base lenOff ≤ bc len .half → p < 2 ^ (32 * cwc len .half))
    {pc : Option Nat} (P : PreG s base bytes len args pc (safeM p))
    (pfit : FitG len args pc .wide ∧ (w32 s.mem base lenOff ≤ bc len .half → FitG len args pc .half)) :
    WP isa (coefficient pc.isSome) s fun u =>
      Frame (frameR base (s.gpr .esp) (coR len)) s.mem u.mem ∧
      sv u.mem base len .wide 7 = ((mp + safeM p - mq % safeM p) % safeM p * qi) % safeM p ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u := by
  obtain hb := bc_le h.upper' .half
  obtain f0 := h.slot_fit .half (j := 0) (by decide)
  obtain lo0 : numBase ≤ lo len (.slot .half 0) := by simp [lo]
  obtain bw2 : bc len .wide ≤ 2 * bc len .half := by simp only [bc]; omega_arith
  obtain bhw := bc_le_wide len .half
  obtain cwh := bc_eq_cwc len .half
  obtain cww := bc_eq_cwc len .wide
  obtain g := bc_ge h.lower' .half
  obtain hM := safeM_gt p
  obtain spw := safeM_lt hpw (by omega_arith)
  obtain two : ∀ {d v : Nat} {m : Mem}, val32 m base d (2 * cwc len .wide) = v → v < 2 ^ (32 * cwc len .wide) →
      val32 m base d (cwc len .wide) = v ∧ val32 m base d (2 * cwc len .half) = v := fun e b =>
    ⟨val32_low (b := cwc len .wide) (by rw [← Nat.two_mul, e]) b,
      val32_low (b := 2 * cwc len .wide - 2 * cwc len .half)
        (by rw [show 2 * cwc len .half + (2 * cwc len .wide - 2 * cwc len .half) = 2 * cwc len .wide by omega_arith, e])
        (Nat.lt_of_lt_of_le b (Nat.pow_le_pow_right (by decide) (by omega_arith)))⟩
  unfold coefficient
  simp only [List.cons_append]
  refine WP.seq (wp_movS (readSrc_sc h.scratch (d := lenOff) (by simp only [lenOff, numBase] at *; omega_arith))
    fun u₁ a₁ _ => ?_)
  obtain h₁ := h.regs a₁.keeps a₁.mem
  refine widthC_ok (k := 0) (c := .half) (r := .edx) h₁.width h.upper' fun u₂ K₂ m₂ e₂ => ?_
  refine wp_addS rfl fun u₃ a₃ _ => wp_cmpC rfl fun u₄ f₄ c₄ => WP.block_nil ?_
  obtain K₄ : Keeps [.eax, .edx] s u₄ :=
    (((a₁.keeps.mono (by decide)).trans (K₂.mono (by decide))).trans (a₃.keeps.mono (by decide))).trans
      (f₄.keeps _)
  obtain m₄ : u₄.mem = s.mem := by rw [f₄.mem, a₃.mem, m₂, a₁.mem]
  obtain h₄ := h.regs K₄ m₄
  obtain eax : (u₃.gpr .eax).toNat = w32 s.mem base lenOff := by
    rw [a₃.other _ (by decide), K₂.1 _ (by decide), a₁.gpr]
  obtain edx : (u₃.gpr .edx).toNat = bc len .half + 1 := by
    rw [a₃.gpr, e₂, BitVec.toNat_add, BitVec.toNat_ofNat, show (1 : BitVec 32).toNat = 1 from rfl]
    omega_arith
  rw [eax, edx] at c₄
  obtain sp : u₄.gpr .esp = s.gpr .esp := K₄.1 _ (by decide)
  rw [← m₄] at hp hmp hmq hqi
  obtain ⟨Q1, Q2⟩ := two hqi hqib
  obtain ⟨N1, N2⟩ := two hmq hmqb
  obtain P₄ := P.keepF h K₄ (by decide) (ws := []) (by rw [m₄]; exact Frame.refl _ _) (by simp) (by simp)
  refine WP.ite _ c₄ (fun nar => ?_) (fun _ => ?_)
  · have nar' : w32 s.mem base lenOff ≤ bc len .half := by have := of_decide_eq_true nar; omega_arith
    obtain hpn := fits nar'
    obtain sph := safeM_lt hpn (by omega_arith)
    obtain mpn : mp < 2 ^ (32 * cwc len .half) := by omega_arith
    obtain P1 : val32 u₄.mem base (lo len (.slot .wide 16)) (cwc len .half) = mp :=
      val32_low (b := 2 * cwc len .wide - cwc len .half)
        (by rw [show cwc len .half + (2 * cwc len .wide - cwc len .half) = 2 * cwc len .wide by omega_arith, hmp]) mpn
    refine WP.mono (narrowCoefficient_ok h₄ hp hpn P1 hmpl N2 Q2 P₄ (pfit.2 nar')) fun u ⟨Fu, Vu, Ku⟩ =>
      ⟨by rw [sp, m₄] at Fu; exact Fu, ?_, (K₄.mono (by decide)).trans Ku⟩
    simp only [sv]
    exact val32_low (b := cwc len .wide) (by rw [← Nat.two_mul, Vu])
      (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by omega_arith)) (by omega_arith))
  · have P1 : val32 u₄.mem base (lo len (.slot .wide 16)) (cwc len .wide) = mp :=
      val32_low (b := cwc len .wide) (by rw [← Nat.two_mul, hmp]) (by omega_arith)
    refine WP.mono (wideCoefficient_ok h₄ hp P1 hmpl N1 Q1 P₄ pfit.1) fun u ⟨Fu, Vu, Ku⟩ =>
      ⟨by rw [sp, m₄] at Fu; exact Fu, Vu, (K₄.mono (by decide)).trans Ku⟩

end

end VG.Proof.Bignum.X86.CrtRt

end

end

/-! ### `Bignum.X86.CrtRt.Recombine`, which only this module used -/

section

/-! # The recombination

`recombine_ok`: `m = m_q + q h` into the wide slot 19 (`2 B` bytes), from
`q` (wide slot 11), `h` (wide slot 7) and `m_q` (wide slot 17, `2 B` bytes),
when it fits.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.CrtRt

variable {Ex : List Region → List Region → Prop}

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86

/-- The ranges the recombination changes. -/
abbrev reR (len : Nat) : List (Nat × Nat) :=
  [(multOff, 4), (prodOff, 2 * bc len .wide + 4), (mulAOff, bc len .wide),
    (lo len (.slot .wide 19), 2 * bc len .wide)]

section
variable {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}

theorem recombine_ok (h : In Ex base bytes len args s) {q hc mq : Nat}
    (hq : val32 s.mem base (lo len (.slot .wide 11)) (cwc len .wide) = q)
    (hh : val32 s.mem base (lo len (.slot .wide 7)) (cwc len .wide) = hc)
    (hmq : val32 s.mem base (lo len (.slot .wide 17)) (2 * cwc len .wide) = mq) :
    WP isa recombine s fun u =>
      Frame (frameR base (s.gpr .esp) (reR len)) s.mem u.mem ∧
      (mq + q * hc < 2 ^ (32 * (2 * cwc len .wide)) →
        val32 u.mem base (lo len (.slot .wide 19)) (2 * cwc len .wide) = mq + q * hc) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u := by
  have pf := h.prod_fit
  obtain bw := bc_eq_cwc len .wide
  obtain g := bc_ge h.lower' .wide
  have bl := h.bytes_lt
  have nw := h.scratch.nowrap
  obtain f19 := h.slot_fit .wide (j := 19) (by decide)
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  have e7 : lo len (.slot .wide 7) = numBase + 7 * st len .wide := rfl
  have e11 : lo len (.slot .wide 11) = numBase + 11 * st len .wide := rfl
  have e17 : lo len (.slot .wide 17) = numBase + 17 * st len .wide := rfl
  have e19 : lo len (.slot .wide 19) = numBase + 19 * st len .wide := rfl
  have nb : numBase = 3336 := rfl
  have ma : mulAOff = 2312 := rfl
  have po : prodOff = 256 := rfl
  have mo : multOff = 48 := rfl
  obtain cb1 : cb len (one .wide) = bc len .wide := by simp [cb, one]
  obtain cw1 : cw len (one .wide) = cwc len .wide := by simp [cw, cwc, cb, one]
  obtain cb2 : cb len (two .wide) = 2 * bc len .wide := by simp [cb, two]
  obtain cw2 : cw len (two .wide) = 2 * cwc len .wide := by
    have := bc_dvd len .wide; simp [cw, cb, two, cwc]; omega_arith
  obtain fitR : ∀ p ∈ reR len, p.1 + p.2 ≤ bytes := by
    intro p hp; simp only [reR, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> dsimp only <;> omega_arith
  unfold recombine
  -- `q` into the multiplicand, and `q h`.
  refine WP.seq (WP.mono (copy_ok h (x := .slot .wide 11) (d := mulA) (one_ok .wide) (by rw [cb1]; omega_arith)
    (by rw [cb1]; simp only [mulA, lo]; omega_arith) (by rw [cb1]; simp only [mulA, lo]; exact .inl (by omega_arith)))
    fun u₁ ⟨O₁, V₁, K₁⟩ => ?_)
  simp only [mulA, lo, cb1, cw1] at O₁ V₁
  rw [show numBase + 11 * st len .wide = lo len (.slot .wide 11) from rfl, hq] at V₁
  obtain h₁ := h.keep K₁ (by decide) (by decide) (O₁.mono (Nat.zero_le _) (by omega_arith))
  refine WP.seq (WP.mono (wideProduct_ok h₁ (b := .slot .wide 7) (by omega_arith) (by simp only [lo]; omega_arith))
    fun u₂ ⟨F₂, V₂, K₂⟩ => ?_)
  rw [V₁, O₁.val32 (d := lo len (.slot .wide 7)) (k := cwc len .wide) (.inr (by omega_arith)) (by omega_arith), hh] at V₂
  obtain h₂ := h₁.keepF K₂ (by decide) (by decide) F₂ (prodR_fit h₁)
  obtain sp₁ : u₁.gpr .esp = s.gpr .esp := K₁.1 _ (by decide)
  rw [sp₁] at F₂
  obtain M₂ : val32 u₂.mem base (lo len (.slot .wide 17)) (2 * cwc len .wide) = mq := by
    rw [prodR_keep h₁ F₂ (sp₁ ▸ h₁.room) (by omega_arith) (by omega_arith),
      O₁.val32 (.inr (by omega_arith)) (by omega_arith), hmq]
  -- `m_q + q h`.
  refine WP.mono (chainAdd_ok h₂ (o := .slot .wide 19) (a := prod) (b := .slot .wide 17) (two_ok .wide)
    (by rw [cb2]; omega_arith) (by rw [cb2]; simp only [prod, lo]; omega_arith) (by rw [cb2]; omega_arith)
    (by rw [cb2]; simp only [prod, lo]; exact .inr (by omega_arith)) (by rw [cb2]; exact .inr (by omega_arith)))
    fun u ⟨O₃, _, ⟨c, _, V₃⟩, K₃⟩ => ⟨?_, fun fits => ?_, ?_⟩
  · rw [cb2] at O₃
    obtain F₁ : Frame (frameR base (s.gpr .esp) (reR len)) s.mem u₁.mem := frameR_of_outside O₁ (by omega_arith) (by simp)
    obtain F₂' : Frame (frameR base (s.gpr .esp) (reR len)) u₁.mem u₂.mem :=
      frameR_mono F₂ fun p hp => by
        simp only [prodR, List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> simp
    exact (F₁.trans F₂').trans (frameR_of_outside O₃ (by omega_arith) (by simp))
  · rw [cw2, show lo len prod = prodOff from rfl] at V₃
    rw [M₂] at V₃
    obtain pq : val32 u₂.mem base prodOff (2 * cwc len .wide) = q * hc :=
      val32_low (b := 1) V₂ (by omega_arith)
    rw [pq] at V₃
    cases c
    · simp only [Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at V₃; omega_arith
    · have := val32_lt u.mem base (lo len (.slot .wide 19)) (2 * cwc len .wide)
      simp only [Bool.toNat_true, Nat.mul_one] at V₃; omega_arith
  · exact (((K₁.mono (by decide)).trans K₂).trans (K₃.mono (by decide)))

end

end VG.Proof.Bignum.X86.CrtRt

end

end


/-! # The result written out

`maskResult_ok`: the result (wide slot 19, `B` bytes) cleared unless the mask
at `accOff` is set. `writeResult_ok`: its `n_len` bytes to `out`,
big-endian, and the acceptance in `eax`.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.CrtRt

variable {Ex : List Region → List Region → Prop}

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86

section
variable {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}

theorem maskResult_ok (h : In Ex base bytes len args s) {c : Bool}
    (hm : s.mem.readW (off base accOff) 32 = cmask c) {P : Prog isa} {Q : State → Prop}
    (k : ∀ u, Outside base (lo len (.slot .wide 19)) (bc len .wide) s.mem u.mem →
      val32 u.mem base (lo len (.slot .wide 19)) (cwc len .wide) =
        (if c then val32 s.mem base (lo len (.slot .wide 19)) (cwc len .wide) else 0) →
      Keeps [.eax, .ecx, .edx, .ebp] s u → WP isa P u Q) :
    WP isa (.seq (.block (ptrTo (.slot .wide 19) .ebp .edx ++ cntTo (one .wide) .edx ++
      ([.mov .ecx (.mem (sc accOff))] : List Instr))) (.seq maskLoop P)) s Q := by
  obtain f19 := h.slot_fit .wide (j := 19) (by decide)
  obtain bw := bc_eq_cwc len .wide
  obtain g := bc_ge h.lower' .wide
  have bl := h.bytes_lt
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  have e19 : lo len (.slot .wide 19) = numBase + 19 * st len .wide := rfl
  have nb : numBase = 3336 := rfl
  obtain cw1 : cw len (one .wide) = cwc len .wide := by simp [cw, cwc, cb, one]
  simp only [List.append_assoc]
  refine WP.seq (ptrTo_ok (r := .ebp) (t := .edx) (x := .slot .wide 19) (by decide) (by decide) h.edi h.width
    h.upper' (by omega_using [f19, bl]) fun u K m p => ?_)
  obtain hu := h.regs K m
  refine cntTo_ok (r := .edx) (n := one .wide) hu.width h.upper' (one_ok .wide).extra fun v Kv mv cv => ?_
  obtain hv := hu.regs Kv mv
  refine wp_movS (readSrc_sc hv.scratch (d := accOff) (by simp only [accOff]; omega_using [f19, est])) fun w uw _ =>
    WP.block_nil ?_
  obtain Kw : Keeps [.ecx, .edx, .ebp] s w :=
    ((K.mono (by decide)).trans (Kv.mono (by decide))).trans (uw.keeps.mono (by decide))
  obtain mw : w.mem = s.mem := by rw [uw.mem, mv, m]
  refine WP.seq (WP.mono (VG.Proof.Bignum.X86.PublicRt.maskLoop_ok (h.ws.of_keeps Kw) (x := lo len (.slot .wide 19))
    (N := cwc len .wide) (c := c) (by omega) (by omega_using [f19, bw, est])
    (by rw [PtrAt, uw.other _ (by decide), Kv.1 _ (by decide)]; exact p)
    (by rw [uw.other _ (by decide), cnt_toNat h.upper' (one_ok .wide) cv, cw1])
    (by rw [uw.gpr, mv, m, hm])) fun t ⟨O, V, Kt⟩ => k t (by rw [← mw, bw]; exact O) (by rw [V, mw])
      ((Kw.mono (by decide)).trans (Kt.mono (by decide))))

/-- The result's `n_len` bytes to the synthetic argument `p`, of `n_len` bytes (at the synthetic argument
`l`); they are its value's when it fits them. -/
theorem writeTo_ok (h : In Ex base bytes len args s) {p l : Nat} (hp : p < 18) (hl : l < 18)
    (lenArg : args l = BitVec.ofNat 32 len) (outFit : (args p).toNat + len ≤ 2 ^ 32)
    (outWrite : InRegions s.wr (byteAddr (args p)) len)
    (outApart : Region.Disjoint ⟨base, bytes⟩ ⟨byteAddr (args p), len⟩) :
    WP isa (.seq (.block (([.mov .ebx (.mem (PublicRt.argAt 0 p)), .mov .ecx (.mem (PublicRt.argAt 0 l))] : List Instr) ++
      ptrTo (.slot .wide 19) .esi .edx ++ ([.alu .add .esi (.reg .ecx), .alu .sub .esi (.imm 1)] : List Instr)))
      (.seq reverseBytes (.block [.mov .eax (.mem (sc accOff)), .alu .and .eax (.imm 1)]))) s fun t =>
      (val32 s.mem base (lo len (.slot .wide 19)) (cwc len .wide) < 2 ^ (8 * len) →
        Spec.Rsa.bytesAt t.mem (byteAddr (args p)) len =
          Spec.Rsa.i2osp (val32 s.mem base (lo len (.slot .wide 19)) (cwc len .wide)) len) ∧
      t.gpr .eax = s.mem.readW (off base accOff) 32 &&& 1 ∧
      Frame [⟨byteAddr (args p), len⟩] s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .esi] s t := by
  obtain f19 := h.slot_fit .wide (j := 19) (by decide)
  obtain bw := bc_eq_cwc len .wide
  obtain g := bc_ge h.lower' .wide
  obtain lb := len_le_bc len
  have nw' := h.scratch.nowrap
  have hlow := h.lower'
  have hup := h.upper'
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  have e19 : lo len (.slot .wide 19) = numBase + 19 * st len .wide := rfl
  have nb : numBase = 3336 := rfl
  simp only [List.cons_append, List.append_assoc]
  refine WP.seq (wp_movS (h.stack p hp).readSrc fun u₁ e₁ _ => ?_)
  obtain h₁ := h.regs e₁.keeps e₁.mem
  refine wp_movS (h₁.stack l hl).readSrc fun u₂ e₂ _ => ?_
  obtain h₂ := h₁.regs e₂.keeps e₂.mem
  refine ptrTo_ok (r := .esi) (t := .edx) (x := .slot .wide 19) (by decide) (by decide) h₂.edi h₂.width
    h.upper' (by omega_using [f19, nw', est]) fun v Kv mv pv => wp_addS rfl fun v₁ w₁ _ => wp_subS rfl fun v₂ w₂ _ => WP.block_nil ?_
  obtain K₂ : Keeps [.ebx, .ecx, .edx, .esi] s v₂ :=
    (((e₁.keeps.mono (by decide)).trans (e₂.keeps.mono (by decide))).trans (Kv.mono (by decide))).trans
      ((w₁.keeps.mono (by decide)).trans (w₂.keeps.mono (by decide)))
  obtain m₂ : v₂.mem = s.mem := by rw [w₂.mem, w₁.mem, mv, e₂.mem, e₁.mem]
  obtain srcAddr : byteAddr (v.gpr .esi) = off base (lo len (.slot .wide 19)) :=
    VG.Proof.Bignum.X86.PublicRt.byteAddr_ptr pv (by omega_using [f19, nw', est])
  obtain srcNat : (v.gpr .esi).toNat = base.toNat + lo len (.slot .wide 19) := by
    rw [pv, Nat.mod_eq_of_lt (by omega_using [f19, nw', est])]
  obtain ecx₂ : v₂.gpr .ecx = BitVec.ofNat 32 len := by
    rw [w₂.other _ (by decide), w₁.other _ (by decide), Kv.1 _ (by decide), e₂.gpr, lenArg]
  obtain ebx₂ : v₂.gpr .ebx = args p := by
    rw [w₂.other _ (by decide), w₁.other _ (by decide), Kv.1 _ (by decide), e₂.other _ (by decide), e₁.gpr]
  obtain esi₂ : v₂.gpr .esi = v.gpr .esi + BitVec.ofNat 32 (len - 1) := by
    rw [w₂.gpr, w₁.gpr, Kv.1 .ecx (by decide), e₂.gpr, lenArg]
    rw [BitVec.sub_eq_add_neg, BitVec.add_assoc, ← BitVec.sub_eq_add_neg,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega_using [hlow])]
  obtain hsub : Region.Sub ⟨off base (lo len (.slot .wide 19)), len⟩ ⟨base, bytes⟩ := by
    have := Offset.sub base (d := lo len (.slot .wide 19)) (n := len) (e := 0) (k := bytes) (Nat.zero_le _) (by omega_using [f19, lb, est])
    simpa only [off, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using this
  refine WP.seq (WP.mono (reverseBuffer_ok v₂ (src := v.gpr .esi) (dst := args p) (n := len) (by omega_using [hlow])
    (by omega_using [f19, lb, nw', est, srcNat]) outFit (by omega_using [hup]) (by rw [K₂.2.1, K₂.2.2, srcAddr]; exact h.scratch.read (by omega_using [f19, lb, est]))
    (by rw [K₂.2.2]; exact outWrite) (by rw [srcAddr]; exact outApart.sub_left hsub) ebx₂ esi₂ ecx₂)
    fun t ⟨V, F, _, T⟩ => ?_)
  obtain Kt : Keeps [.eax, .ebx, .ecx, .edx, .esi] s t := (K₂.mono (by decide)).trans (T.mono (by decide))
  obtain Ft : Frame [⟨byteAddr (args p), len⟩] s.mem t.mem := by rw [← m₂]; exact F
  obtain ht := h.ws.of_keeps Kt
  obtain st' : Scr t base bytes := ⟨by rw [← h.scratch.edi, Kt.1 _ (by decide)], ht.wr, ht.nowrap,
    by rw [Kt.1 _ (by decide)]; exact h.scratch.stk⟩
  refine wp_movS (readSrc_sc st' (d := accOff) (by simp only [accOff]; omega_using [f19, est])) fun t₁ u₁ _ => ?_
  refine wp_logicS (.inl rfl) rfl fun t₂ u₂ => WP.block_nil ?_
  obtain acc : t.mem.readW (off base accOff) 32 = s.mem.readW (off base accOff) 32 :=
    Ft.readW (r := ⟨base, bytes⟩) (Scr.contains nw' (by simp only [accOff]; omega_using [f19, est]))
      (by intro r hr; rw [List.mem_singleton.mp hr]; exact outApart) (by decide)
  refine ⟨?_, ?_, by rw [u₂.mem, u₁.mem]; exact Ft, (Kt.trans (u₁.keeps.mono (by decide))).trans (u₂.keeps.mono (by decide))⟩
  · intro fitv
    rw [u₂.mem, u₁.mem, V, srcAddr, m₂]
    obtain eq : (s.mem.read (off base (lo len (.slot .wide 19))) (4 * cwc len .wide)).toNat =
        val32 s.mem base (lo len (.slot .wide 19)) (cwc len .wide) := read_eq_val32 _ _ _ _
    rw [VG.Proof.Bignum.read_prefix_value s.mem _ (by omega_using [bw, lb] : len ≤ 4 * cwc len .wide) (by rw [eq]; exact fitv), eq]
  · rw [u₂.gpr, u₁.gpr, acc]; rfl

/-- The result's `n_len` bytes to `out`; they are its value's when it fits them. -/
theorem writeResult_ok (h : In Ex base bytes len args s) (outFit : (args 0).toNat + len ≤ 2 ^ 32)
    (outWrite : InRegions s.wr (byteAddr (args 0)) len)
    (outApart : Region.Disjoint ⟨base, bytes⟩ ⟨byteAddr (args 0), len⟩) :
    WP isa (.seq (.block (PublicFn.outputArgs ++ ptrTo (.slot .wide 19) .esi .edx ++
      ([.alu .add .esi (.reg .ecx), .alu .sub .esi (.imm 1)] : List Instr)))
      (.seq reverseBytes (.block [.mov .eax (.mem (sc accOff)), .alu .and .eax (.imm 1)]))) s fun t =>
      (val32 s.mem base (lo len (.slot .wide 19)) (cwc len .wide) < 2 ^ (8 * len) →
        Spec.Rsa.bytesAt t.mem (byteAddr (args 0)) len =
          Spec.Rsa.i2osp (val32 s.mem base (lo len (.slot .wide 19)) (cwc len .wide)) len) ∧
      t.gpr .eax = s.mem.readW (off base accOff) 32 &&& 1 ∧
      Frame [⟨byteAddr (args 0), len⟩] s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .esi] s t :=
  writeTo_ok h (p := 0) (l := 1) (by decide) (by decide) h.outLen outFit outWrite outApart

end

end VG.Proof.Bignum.X86.CrtRt
