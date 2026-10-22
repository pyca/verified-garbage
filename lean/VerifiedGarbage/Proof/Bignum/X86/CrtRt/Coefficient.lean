module

public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Powers
import VerifiedGarbage.Proof.Framework.Omega

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
    exact ⟨by rw [show a + M - b = (a - b) + M by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]; omega,
      by omega⟩
  · cases c₂ <;> simp only [Bool.toNat_true, Bool.toNat_false, Nat.mul_one, Nat.mul_zero, Nat.add_zero,
      ↓reduceIte] at h₁ h₂ ⊢
    · omega
    · exact ⟨by rw [Nat.mod_eq_of_lt (by omega)]; omega, by omega⟩

section
variable {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {c : Ctx} {M : Nat}

theorem subMod_raw (C : CtxOk Ex base bytes len args c M s) :
    WP isa (subMod c 7 6 5) s fun u =>
      CtxOk Ex base bytes len args c M u ∧ Frame (frameR base (s.gpr .esp) (subR len c)) s.mem u.mem ∧
      (sv s.mem base len c 6 < M → sv s.mem base len c 5 < M →
        sv u.mem base len c 7 = (sv s.mem base len c 6 + M - sv s.mem base len c 5) % M) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s u := by
  have h := C.inp
  have f8 := h.slot_fit c (j := 8) (by decide)
  have bw := bc_eq_cwc len c
  have g := bc_ge h.lower' c
  have bl := h.bytes_lt
  have nw := h.scratch.nowrap
  have est : st len c = 2 * bc len c + 32 := rfl
  have z0 : lo len (.slot c 0) = numBase := sl_zero len c
  have e1 : lo len (.slot c 1) = numBase + st len c := by simp [lo]
  have e5 : lo len (.slot c 5) = numBase + 5 * st len c := rfl
  have e6 : lo len (.slot c 6) = numBase + 6 * st len c := rfl
  have e7 : lo len (.slot c 7) = numBase + 7 * st len c := rfl
  have e8 : lo len (.slot c 8) = numBase + 8 * st len c := rfl
  have nb : numBase = 3336 := rfl
  have mo : maskOff = 12 := rfl
  have cb1 : cb len (one c) = bc len c := by simp [cb, one]
  have cw1 : cw len (one c) = cwc len c := by simp [cw, cwc, cb, one]
  unfold subMod
  -- `a - b`, its borrow saved.
  refine WP.seq (WP.mono (chainSub_ok h (o := .slot c 7) (a := .slot c 6) (b := .slot c 5) (one_ok c)
    (by rw [cb1]; omega) (by rw [cb1]; omega) (by rw [cb1]; omega) (by rw [cb1]; exact .inr (by omega))
    (by rw [cb1]; exact .inr (by omega))) fun u₁ ⟨O₁, _, ⟨c₁, k₁, V₁⟩, K₁⟩ => ?_)
  rw [cb1] at O₁
  rw [cw1] at V₁
  have h₁ := h.keep K₁ (by decide) (by decide) (O₁.mono (Nat.zero_le _) (by omega))
  refine WP.seq (wp_storeS (h₁.scratch.ea (d := maskOff) (by omega))
    (h₁.scratch.write (d := maskOff) (n := 4) (by omega)) fun u₂ m₂ => WP.block_nil ?_)
  have O₂ : Outside base maskOff 4 u₁.mem u₂.mem := by rw [m₂.mem]; exact writeW32_outside _ _ _ (by omega)
  have A₂ : u₂.mem.readW (off base maskOff) 32 = cmask c₁ := by rw [m₂.mem, Mem.readW_writeW_self32, k₁]
  have h₂ := h₁.keep (m₂.keeps []) (by decide) (by decide) (O₂.mono (Nat.zero_le _) (by omega))
  -- The difference plus `M`.
  refine WP.seq (WP.mono (chainAdd_ok h₂ (o := .slot c 1) (a := .slot c 7) (b := .slot c 0) (one_ok c)
    (by rw [cb1]; omega) (by rw [cb1]; omega) (by rw [cb1]; omega) (by rw [cb1]; exact .inl (by omega))
    (by rw [cb1]; exact .inr (by omega))) fun u₃ ⟨O₃, _, ⟨c₂, _, V₃⟩, K₃⟩ => ?_)
  rw [cb1] at O₃
  rw [cw1] at V₃
  have h₃ := h₂.keep K₃ (by decide) (by decide) (O₃.mono (Nat.zero_le _) (by omega))
  -- The borrow back, and the selection.
  refine WP.seq (wp_movS (readSrc_sc h₃.scratch (d := maskOff) (by omega)) fun u₄ a₄ _ => WP.block_nil ?_)
  have h₄ := h₃.regs a₄.keeps a₄.mem
  have ecx₄ : u₄.gpr .ecx = cmask c₁ := by
    rw [a₄.gpr, ← A₂]
    exact BitVec.eq_of_toNat_eq (O₃.w32 (d := maskOff) (.inl (by omega)) (by omega))
  refine WP.mono (select_ok h₄ (x := .slot c 1) (d := .slot c 7) (one_ok c) (by rw [cb1]; omega)
    (by rw [cb1]; omega) (by rw [cb1]; exact .inr (by omega)) ecx₄) fun u ⟨O₅, V₅, K₅⟩ => ?_
  rw [cb1] at O₅
  rw [cw1, a₄.mem] at V₅
  -- The values.
  have A : val32 u₂.mem base (lo len (.slot c 7)) (cwc len c) = val32 u₁.mem base (lo len (.slot c 7)) (cwc len c) :=
    O₂.val32 (.inr (by omega)) (by omega)
  have M₂ : val32 u₂.mem base (lo len (.slot c 0)) (cwc len c) = M := by
    rw [O₂.val32 (.inr (by omega)) (by omega), O₁.val32 (.inl (by omega)) (by omega)]
    have hm := C.mod; simp only [sv] at hm; exact hm
  have D₃ : val32 u₃.mem base (lo len (.slot c 7)) (cwc len c) = val32 u₁.mem base (lo len (.slot c 7)) (cwc len c) := by
    rw [O₃.val32 (.inr (by omega)) (by omega), A]
  rw [A, M₂] at V₃
  rw [D₃] at V₅
  refine ⟨?_, ?_, fun ha hb => ?_, ?_⟩
  · refine C.keepF2 (regs := [.eax, .ebx, .ecx, .edx, .ebp]) ?_ (by decide) (by decide) (ws := subR len c) ?_ ?_ ?_
    · exact ((((K₁.mono (by decide)).trans ((m₂.keeps []).mono (by decide))).trans (K₃.mono (by decide))).trans
        (a₄.keeps.mono (by decide))).trans (K₅.mono (by decide))
    · exact ((((frameR_of_outside O₁ (by omega) (by simp)).trans (frameR_of_outside O₂ (by omega) (by simp))).trans
        (frameR_of_outside O₃ (by omega) (by simp))).trans (by rw [← a₄.mem]; exact frameR_of_outside O₅ (by omega) (by simp)))
    · intro p hp; simp only [subR, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl <;> dsimp only <;> omega
    · intro p hp; simp only [subR, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl <;> dsimp only <;> omega
  · exact (((frameR_of_outside O₁ (by omega) (by simp)).trans (frameR_of_outside O₂ (by omega) (by simp))).trans
      (frameR_of_outside O₃ (by omega) (by simp))).trans (by rw [← a₄.mem]; exact frameR_of_outside O₅ (by omega) (by simp))
  · have R := subMod_value (W := 2 ^ (32 * cwc len c)) ha hb (val32_lt _ _ _ _) (val32_lt _ _ _ _)
      (by simp only [sv] at *; omega) V₃
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

theorem coR_fit (h : In Ex base bytes len args s) : ∀ q ∈ coR len, q.1 + q.2 ≤ bytes := by
  have f8 := h.slot_fit .wide (j := 8) (by decide)
  have e8 : lo len (.slot .wide 8) = numBase + 8 * st len .wide := rfl
  have nb : numBase = 3336 := rfl
  intro q hq
  simp only [coR, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl <;> simp only [invOff, maskOff] <;> omega

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
  have fit := coR_fit h
  have := fit _ (by simp : (numBase, 9 * st len .wide) ∈ coR len)
  obtain ⟨_, w2⟩ := w
  simp only at w2
  refine co_widen (ws := [(a, n)]) (frameR_of_outside O (by omega_using [w2, this, h.bytes_lt]) (by simp)) ?_
  intro p hp
  obtain rfl := List.mem_singleton.mp hp
  exact .inr (.inr ⟨by assumption, w2⟩)

theorem prepR_co (h : In Ex base bytes len args s) (c : Ctx) : ∀ p ∈ prepR len c, InCo len p := by
  intro p hp
  have g := bc_ge h.lower' c
  simp only [prepR, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · exact .inl rfl
  · exact .inr (.inr (slot_in h c (by decide)))
  · exact .inr (.inr ⟨(slot1_in h c).1, by have := (slot1_in h c).2; dsimp only at *; omega⟩)
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
  have g := bc_ge h.lower' c
  rcases hp with rfl | rfl | rfl
  · exact .inr (.inl rfl)
  · exact .inr (.inr ⟨(slot1_in h c).1, by have := (slot1_in h c).2; dsimp only at *; omega⟩)
  · exact .inr (.inr (slot_in h c (by decide)))

/-- A subtraction modulo `M` keeps slots 3, 4 and 8. -/
theorem subR_sv (h : In Ex base bytes len args s) (c : Ctx) {sp : BitVec 32} {m m' : Mem}
    (F : Frame (frameR base sp (subR len c)) m m') (R : CallRoom sp base bytes) {j : Nat}
    (hj3 : 3 ≤ j) (hj : j ≤ 8) (h7 : j ≠ 7) : sv m' base len c j = sv m base len c j := by
  have nw := h.scratch.nowrap
  have f8 := h.slot_fit c (j := 8) (by decide)
  have bw := bc_eq_cwc len c
  have est : st len c = 2 * bc len c + 32 := rfl
  have j8 : lo len (.slot c j) ≤ lo len (.slot c 8) := by
    have := Nat.mul_le_mul_right (st len c) hj; simp only [lo]; omega
  have a7 := slot_apart len c (o := 7) (j := j) h7
  have p1 := slot_past1 len c (j := j) hj3
  have z0 : lo len (.slot c 0) = numBase := sl_zero len c
  have e1 : lo len (.slot c 1) = numBase + st len c := by simp [lo]
  have nb : numBase = 3336 := rfl
  have fit : ∀ p ∈ subR len c, p.1 + p.2 ≤ bytes := by
    have e7 : lo len (.slot c 7) + st len c ≤ lo len (.slot c 8) := sl_le c (by decide)
    intro p hp; simp only [subR, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> simp only [maskOff] <;> omega
  refine frameR_val32 F R nw (by omega) ?_ fit
  intro p hp
  simp only [subR, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> simp only [maskOff] <;> omega

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
  have g := bc_ge h.lower' .wide
  have RR : 2 ^ (16 * bc len .wide) = 2 ^ (8 * bc len .wide) * 2 ^ (8 * bc len .wide) := by
    rw [← Nat.pow_add]; congr 1; omega
  -- `m_q R mod M`, then `m_q mod M`.
  refine WP.seq (WP.mono (cmul_ok C (o := 5) (a := 5) (b := 4) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [h4]; exact Nat.mod_lt _ (by omega))) fun u₁ ⟨C₁, K₁, F₁, L₁, V₁⟩ => ?_)
  have B₁ : sv u₁.mem base len .wide 5 = mq * 2 ^ (8 * bc len .wide) % M := by
    have v := VG.Proof.Dsa.mont_scale C.coprime (out := sv u₁.mem base len .wide 5) (input := mq)
      (c := 2 ^ (8 * bc len .wide)) (by rw [V₁, h5, h4, RR])
    rwa [Nat.mod_eq_of_lt L₁] at v
  have o₁ := mulR_sv C.inp F₁ C.inp.room (j := 3) (by decide) (by decide) (by decide) (by decide) (by decide)
  have f₁ := mulR_sv C.inp F₁ C.inp.room (j := 4) (by decide) (by decide) (by decide) (by decide) (by decide)
  have m₁ := mulR_sv C.inp F₁ C.inp.room (j := 6) (by decide) (by decide) (by decide) (by decide) (by decide)
  have q₁ := mulR_sv C.inp F₁ C.inp.room (j := 8) (by decide) (by decide) (by decide) (by decide) (by decide)
  refine WP.seq (WP.mono (cmul_ok C₁ (o := 5) (a := 5) (b := 3) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [o₁, h3]; exact hM)) fun u₂ ⟨C₂, K₂, F₂, L₂, V₂⟩ => ?_)
  have D₂ : sv u₂.mem base len .wide 5 = mq % M := by
    have v := VG.Proof.Dsa.mont_decode (A := sv u₁.mem base len .wide 5) (out := sv u₂.mem base len .wide 5)
      C.coprime (by rw [B₁, Nat.mod_mod]) (by rw [V₂, o₁, h3])
    rwa [Nat.mod_eq_of_lt L₂] at v
  have f₂ := mulR_sv C₁.inp F₂ C₁.inp.room (j := 4) (by decide) (by decide) (by decide) (by decide) (by decide)
  have m₂ := mulR_sv C₁.inp F₂ C₁.inp.room (j := 6) (by decide) (by decide) (by decide) (by decide) (by decide)
  have q₂ := mulR_sv C₁.inp F₂ C₁.inp.room (j := 8) (by decide) (by decide) (by decide) (by decide) (by decide)
  -- The difference modulo `M`.
  refine WP.seq (WP.mono (subMod_ok C₂ (by rw [m₂, m₁, h6]; exact hmp) (by rw [D₂]; exact Nat.mod_lt _ (by omega)))
    fun u₃ ⟨C₃, F₃, S₃, K₃⟩ => ?_)
  rw [m₂, m₁, h6, D₂] at S₃
  have f₃ : sv u₃.mem base len .wide 4 = sv u₂.mem base len .wide 4 :=
    subR_sv C₂.inp .wide F₃ C₂.inp.room (by decide) (by decide) (by decide)
  have q₃ : sv u₃.mem base len .wide 8 = sv u₂.mem base len .wide 8 :=
    subR_sv C₂.inp .wide F₃ C₂.inp.room (by decide) (by decide) (by decide)
  -- `qInv R mod M`, and the product.
  refine WP.seq (WP.mono (cmul_ok C₃ (o := 8) (a := 8) (b := 4) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [f₃, f₂, f₁, h4]; exact Nat.mod_lt _ (by omega))) fun u₄ ⟨C₄, K₄, F₄, L₄, V₄⟩ => ?_)
  have Q₄ : sv u₄.mem base len .wide 8 = qi * 2 ^ (8 * bc len .wide) % M := by
    have v := VG.Proof.Dsa.mont_scale C.coprime (out := sv u₄.mem base len .wide 8) (input := qi)
      (c := 2 ^ (8 * bc len .wide)) (by rw [V₄, q₃, q₂, q₁, h8, f₃, f₂, f₁, h4, RR])
    rwa [Nat.mod_eq_of_lt L₄] at v
  have s₄ := mulR_sv C₃.inp F₄ C₃.inp.room (j := 7) (by decide) (by decide) (by decide) (by decide) (by decide)
  refine WP.mono (cmul_ok C₄ (o := 7) (a := 7) (b := 8) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [Q₄]; exact Nat.mod_lt _ (by omega))) fun u ⟨C₅, K₅, F₅, L₅, V₅⟩ =>
      ⟨C₅, ?_, ?_, ?_⟩
  · have sp₁ : u₁.gpr .esp = s.gpr .esp := K₁.1 _ (by decide)
    have sp₂ : u₂.gpr .esp = s.gpr .esp := (K₂.1 _ (by decide)).trans sp₁
    have sp₃ : u₃.gpr .esp = s.gpr .esp := (K₃.1 _ (by decide)).trans sp₂
    have sp₄ : u₄.gpr .esp = s.gpr .esp := (K₄.1 _ (by decide)).trans sp₃
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
  have f18 := h.slot_fit .wide (j := 18) (by decide)
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  have a := Nat.mul_le_mul_right (st len .wide) hj9
  have b := Nat.mul_le_mul_right (st len .wide) (show j + 1 ≤ 18 by omega)
  have c := Nat.mul_le_mul_right (st len .wide) (show d + 1 ≤ 9 by omega)
  rw [Nat.succ_mul] at b c
  have ej : lo len (.slot .wide j) = numBase + j * st len .wide := rfl
  have ed : lo len (.slot .wide d) = numBase + d * st len .wide := rfl
  have e18 : lo len (.slot .wide 18) = numBase + 18 * st len .wide := rfl
  have cb1 : cb len (one .wide) = bc len .wide := by simp [cb, one]
  have cw1 : cw len (one .wide) = cwc len .wide := by simp [cw, cwc, cb, one]
  refine WP.mono (copy_ok h (x := .slot .wide j) (d := .slot .wide d) (one_ok .wide) (by rw [cb1]; omega)
    (by rw [cb1]; omega) (by rw [cb1]; exact .inl (by omega))) fun u ⟨O, V, K⟩ => ⟨?_, ?_, K⟩
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
  rcases hp with rfl | rfl | rfl <;> simp only [invOff, maskOff] <;> omega

/-- `h = (m_p - m_q mod p) qInv mod p` into the wide slot 7, for `p` (wide slot 10), `m_p` and `m_q`
(wide slots 16 and 17) and `qInv` (wide slot 14), in the context of `p`. -/
theorem coefficient_ok (h : In Ex base bytes len args s) {p mp mq qi : Nat}
    (hp : val32 s.mem base (lo len (.slot .wide 10)) (cwc len .wide) = p)
    (hmp : val32 s.mem base (lo len (.slot .wide 16)) (cwc len .wide) = mp) (hmpl : mp < safeM p)
    (hmq : val32 s.mem base (lo len (.slot .wide 17)) (cwc len .wide) = mq)
    (hqi : val32 s.mem base (lo len (.slot .wide 14)) (cwc len .wide) = qi) :
    WP isa coefficient s fun u =>
      Frame (frameR base (s.gpr .esp) (coR len)) s.mem u.mem ∧
      sv u.mem base len .wide 7 = ((mp + safeM p - mq % safeM p) % safeM p * qi) % safeM p ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u := by
  have f18 := h.slot_fit .wide (j := 18) (by decide)
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  have bw := bc_eq_cwc len .wide
  have e9 : lo len (.slot .wide 9) = numBase + 9 * st len .wide := rfl
  have e18 : lo len (.slot .wide 18) = numBase + 18 * st len .wide := rfl
  have e3 : lo len (.slot .wide 3) = numBase + 3 * st len .wide := rfl
  have e4 : lo len (.slot .wide 4) = numBase + 4 * st len .wide := rfl
  have e5 : lo len (.slot .wide 5) = numBase + 5 * st len .wide := rfl
  have e6 : lo len (.slot .wide 6) = numBase + 6 * st len .wide := rfl
  have e8 : lo len (.slot .wide 8) = numBase + 8 * st len .wide := rfl
  have bl := h.bytes_lt
  have hi : ∀ {j : Nat}, 9 ≤ j → j ≤ 17 → lo len (.slot .wide 9) ≤ lo len (.slot .wide j) ∧
      lo len (.slot .wide j) + 4 * cwc len .wide ≤ bytes := fun {j} hj9 hj => by
    have a := Nat.mul_le_mul_right (st len .wide) hj9
    have c := Nat.mul_le_mul_right (st len .wide) (show j + 1 ≤ 18 by omega)
    rw [Nat.succ_mul] at c
    have ej : lo len (.slot .wide j) = numBase + j * st len .wide := rfl
    omega
  have room := h.room
  -- Reading the key's components through the coefficient's frame.
  have rd : ∀ {u : State} {j : Nat}, Frame (frameR base (s.gpr .esp) (coR len)) s.mem u.mem → 9 ≤ j → j ≤ 17 →
      val32 u.mem base (lo len (.slot .wide j)) (cwc len .wide) =
        val32 s.mem base (lo len (.slot .wide j)) (cwc len .wide) := fun F hj9 hj =>
    coR_keep h F room (hi hj9 hj).1 (hi hj9 hj).2
  have cs : ∀ {j : Nat}, j ≤ 8 → Within (lo len (.slot .wide j), bc len .wide) (numBase, 9 * st len .wide) :=
    fun hj => slot_in h .wide hj
  unfold coefficient
  refine WP.seq (WP.mono (copyDown_ok h (j := 10) (d := 0) (by decide) (by decide) (by decide))
    fun u₁ ⟨O₁, V₁, K₁⟩ => ?_)
  have F₁ : Frame (frameR base (s.gpr .esp) (coR len)) s.mem u₁.mem := co_of_outside h O₁ (cs (by decide))
  have h₁ := h.keepF K₁ (by decide) (by decide) F₁ (coR_fit h)
  refine WP.seq (WP.mono (prepCtx_ok h₁ .wide) fun u₂ ⟨C₂, one₂, R₂, F₂, K₂⟩ => ?_)
  rw [V₁, hp] at C₂ R₂
  have sp₁ : u₁.gpr .esp = s.gpr .esp := K₁.1 _ (by decide)
  rw [sp₁] at F₂
  have F₁₂ := F₁.trans (co_widen F₂ (prepR_co h₁ .wide))
  have h₂ := C₂.inp
  refine WP.seq (WP.mono (copyDown_ok h₂ (j := 16) (d := 6) (by decide) (by decide) (by decide))
    fun u₃ ⟨O₃, V₃, K₃⟩ => ?_)
  rw [rd F₁₂ (by decide) (by decide), hmp] at V₃
  have F₃ := F₁₂.trans (co_of_outside h O₃ (cs (by decide)))
  have h₃ := h₂.keep K₃ (by decide) (by decide) (O₃.mono (Nat.zero_le _) (by omega))
  refine WP.seq (WP.mono (copyDown_ok h₃ (j := 17) (d := 5) (by decide) (by decide) (by decide))
    fun u₄ ⟨O₄, V₄, K₄⟩ => ?_)
  rw [rd F₃ (by decide) (by decide), hmq] at V₄
  have F₄ := F₃.trans (co_of_outside h O₄ (cs (by decide)))
  have h₄ := h₃.keep K₄ (by decide) (by decide) (O₄.mono (Nat.zero_le _) (by omega))
  refine WP.seq (WP.mono (copyDown_ok h₄ (j := 14) (d := 8) (by decide) (by decide) (by decide))
    fun u₅ ⟨O₅, V₅, K₅⟩ => ?_)
  rw [rd F₄ (by decide) (by decide), hqi] at V₅
  have F₅ := F₄.trans (co_of_outside h O₅ (cs (by decide)))
  -- The context, kept by the copies.
  have K₃₅ : Keeps [.eax, .ebx, .ecx, .edx, .ebp] u₂ u₅ := (K₃.trans K₄).trans K₅
  have C₅ : CtxOk Ex base bytes len args .wide (safeM p) u₅ := by
    refine C₂.keepF K₃₅ (by decide) (by decide)
      (ws := [(lo len (.slot .wide 6), bc len .wide), (lo len (.slot .wide 5), bc len .wide),
        (lo len (.slot .wide 8), bc len .wide)]) ?_ ?_ ?_
    · have sp₂ : u₂.gpr .esp = u₁.gpr .esp := K₂.1 _ (by decide)
      exact ((frameR_of_outside O₃ (by omega) (by simp)).trans ((frameR_of_outside O₄ (by omega) (by simp)).trans
        (frameR_of_outside O₅ (by omega) (by simp))))
    · intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl <;> dsimp only <;> omega
    · intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl <;> dsimp only <;> omega
  have k35 : ∀ {j}, 3 ≤ j → j ≤ 4 → sv u₅.mem base len .wide j = sv u₂.mem base len .wide j := fun {j} hj3 hj => by
    have ej : lo len (.slot .wide j) = numBase + j * st len .wide := rfl
    have := Nat.mul_le_mul_right (st len .wide) hj
    have := Nat.mul_le_mul_right (st len .wide) hj3
    simp only [sv]
    rw [O₅.val32 (.inl (by omega)) (by omega), O₄.val32 (.inl (by omega)) (by omega),
      O₃.val32 (.inl (by omega)) (by omega)]
  have M6 : sv u₅.mem base len .wide 6 = mp := by
    simp only [sv]; rw [O₅.val32 (.inl (by omega)) (by omega),
      O₄.val32 (.inr (by omega)) (by omega)]; exact V₃
  have M5 : sv u₅.mem base len .wide 5 = mq := by
    simp only [sv]; rw [O₅.val32 (.inl (by omega)) (by omega)]; exact V₄
  refine WP.mono (coArith_ok C₅ (mp := mp) (mq := mq) (qi := qi) (by rw [k35 (by decide) (by decide), one₂])
    (by rw [k35 (by decide) (by decide), R₂]) M6 hmpl M5 V₅) fun u ⟨_, F, V, K⟩ => ⟨?_, V, ?_⟩
  · have sp₅ : u₅.gpr .esp = s.gpr .esp :=
      (K₃₅.1 _ (by decide)).trans ((K₂.1 _ (by decide)).trans sp₁)
    rw [sp₅] at F
    exact F₅.trans F
  · exact ((((K₁.mono (by decide)).trans K₂).trans (K₃₅.mono (by decide))).trans K)

end

end VG.Proof.Bignum.X86.CrtRt
