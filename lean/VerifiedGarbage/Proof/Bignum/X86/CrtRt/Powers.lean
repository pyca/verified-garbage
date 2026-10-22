module

public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.StageR
import VerifiedGarbage.Proof.Framework.Omega

/-! # The factors' powers

`reduce_ok`: the input modulo a factor `p` (in the wide context, its
modulus `safeM p`), into the wide slot `o`. `narrowPower_ok` and
`widePower_ok`: the input to the power `d` modulo `safeM p`, zero-extended
into the wide slot `o`, at half the width or at the modulus's.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.CrtRt

variable {Ex : List Region → List Region → Prop}

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86

section
variable {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}

/-- A preparation keeps slots 5, 6 and 8. -/
theorem prepR_sv (h : In Ex base bytes len args s) (c : Ctx) {sp : BitVec 32} {m m' : Mem}
    (F : Frame (frameR base sp (prepR len c)) m m') (R : CallRoom sp base bytes) {j : Nat}
    (hj5 : 5 ≤ j) (hj : j ≤ 8) (h7 : j ≠ 7) : sv m' base len c j = sv m base len c j := by
  have nw := h.scratch.nowrap
  have f8 := h.slot_fit c (j := 8) (by decide)
  have bw := bc_eq_cwc len c
  have est : st len c = 2 * bc len c + 32 := rfl
  have j8 : lo len (.slot c j) ≤ lo len (.slot c 8) := by
    have := Nat.mul_le_mul_right (st len c) hj; simp only [lo]; omega
  have a3 := slot_apart len c (o := 3) (j := j) (by omega)
  have a4 := slot_apart len c (o := 4) (j := j) (by omega)
  have a7 := slot_apart len c (o := 7) (j := j) h7
  have p1 := slot_past1 len c (j := j) (by omega)
  have z0 : lo len (.slot c 0) = numBase := sl_zero len c
  have e1 : lo len (.slot c 1) = numBase + st len c := by simp [lo]
  have nb : numBase = 3336 := rfl
  refine frameR_val32 F R nw (by omega) ?_ (prepR_fit h c)
  intro p hp
  simp only [prepR, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [invOff] <;> omega

/-- Changes below the wide slot 9 keep the slots from 9 on. -/
theorem low_keep (h : In Ex base bytes len args s) {sp : BitVec 32} {ws : List (Nat × Nat)} {m m' : Mem}
    (F : Frame (frameR base sp ws) m m') (R : CallRoom sp base bytes) (fit : ∀ p ∈ ws, p.1 + p.2 ≤ bytes)
    (hw : ∀ p ∈ ws, p.1 + p.2 ≤ lo len (.slot .wide 9)) {d k : Nat} (hd : lo len (.slot .wide 9) ≤ d)
    (hk : d + 4 * k ≤ bytes) : val32 m' base d k = val32 m base d k :=
  frameR_val32 F R h.scratch.nowrap hk (fun p hp => .inr (by have := hw p hp; omega)) fit

/-- Where the wide slots lie, for a factor's power. -/
structure WideLay (len bytes f o : Nat) : Prop where
  est : st len .wide = 2 * bc len .wide + 32
  l0 : lo len (.slot .wide 0) = numBase
  l5 : lo len (.slot .wide 5) = numBase + 5 * st len .wide
  l8 : lo len (.slot .wide 8) = numBase + 8 * st len .wide
  l9 : lo len (.slot .wide 9) = numBase + 9 * st len .wide
  l15 : lo len (.slot .wide 15) = numBase + 15 * st len .wide
  l16 : lo len (.slot .wide 16) = numBase + 16 * st len .wide
  l18 : lo len (.slot .wide 18) = numBase + 18 * st len .wide
  f1 : lo len (.slot .wide 9) ≤ lo len (.slot .wide f)
  f2 : lo len (.slot .wide f) + st len .wide ≤ lo len (.slot .wide 16)
  o1 : lo len (.slot .wide 16) ≤ lo len (.slot .wide o)
  o2 : lo len (.slot .wide o) + st len .wide ≤ lo len (.slot .wide 18)
  fit : lo len (.slot .wide 18) + st len .wide ≤ bytes
  nb : numBase = 3336

theorem WideLay.mk' (h : In Ex base bytes len args s) {f o : Nat} (hf9 : 9 ≤ f) (hf : f ≤ 15) (ho16 : 16 ≤ o)
    (ho : o ≤ 17) : WideLay len bytes f o := by
  have a := Nat.mul_le_mul_right (st len .wide) hf9
  have b := Nat.mul_le_mul_right (st len .wide) (show f + 1 ≤ 16 by omega)
  have c := Nat.mul_le_mul_right (st len .wide) ho16
  have d := Nat.mul_le_mul_right (st len .wide) (show o + 1 ≤ 18 by omega)
  rw [Nat.succ_mul] at b d
  have ef : lo len (.slot .wide f) = numBase + f * st len .wide := rfl
  have eo : lo len (.slot .wide o) = numBase + o * st len .wide := rfl
  have e9 : lo len (.slot .wide 9) = numBase + 9 * st len .wide := rfl
  have e16 : lo len (.slot .wide 16) = numBase + 16 * st len .wide := rfl
  have e18 : lo len (.slot .wide 18) = numBase + 18 * st len .wide := rfl
  exact ⟨rfl, sl_zero len .wide, rfl, rfl, rfl, rfl, rfl, rfl, by omega, by omega, by omega, by omega,
    h.slot_fit .wide (by decide), rfl⟩

/-- The input (wide slot 15) modulo the factor in the wide slot `f`, into the wide slot `o`. -/
theorem reduce_ok (h : In Ex base bytes len args s) {f o : Nat} (hf9 : 9 ≤ f) (hf : f ≤ 15) (ho16 : 16 ≤ o)
    (ho : o ≤ 17) {p x : Nat} (hp : val32 s.mem base (lo len (.slot .wide f)) (cwc len .wide) = p)
    (hx : val32 s.mem base (lo len (.slot .wide 15)) (cwc len .wide) = x) {P : Prog isa} {Q : State → Prop}
    (k : ∀ u, In Ex base bytes len args u → Frame (frameR base (s.gpr .esp) (stR len o)) s.mem u.mem →
      val32 u.mem base (lo len (.slot .wide o)) (cwc len .wide) = x % safeM p →
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u → WP isa P u Q) :
    WP isa (.seq (copy (.slot .wide f) (.slot .wide 0) (one .wide)) <|
      .seq (copy (.slot .wide 15) (.slot .wide 5) (one .wide)) <| .seq (prepare .wide) <|
      .seq (mul .wide 5 5 4) <| .seq (mul .wide 5 5 3) <|
      .seq (copy (.slot .wide 5) (.slot .wide o) (one .wide)) P) s Q := by
  obtain ⟨est, l0, l5, l8, l9, l15, l16, l18, f1, f2, o1, o2, fit, nb⟩ := WideLay.mk' h hf9 hf ho16 ho
  have bw := bc_eq_cwc len .wide
  have g := bc_ge h.lower' .wide
  have bl := h.bytes_lt
  have cb1 : cb len (one .wide) = bc len .wide := by simp [cb, one]
  have cw1 : cw len (one .wide) = cwc len .wide := by simp [cw, cwc, cb, one]
  have ho' : o ≤ 19 := by omega
  have RR : 2 ^ (16 * bc len .wide) = 2 ^ (8 * bc len .wide) * 2 ^ (8 * bc len .wide) := by
    rw [← Nat.pow_add]; congr 1; omega
  have hM := safeM_gt p
  -- The factor and the input.
  refine WP.seq (WP.mono (copy_ok h (x := .slot .wide f) (d := .slot .wide 0) (one_ok .wide)
    (by rw [cb1]; omega) (by rw [cb1, l0]; omega)
    (by rw [cb1, l0]; exact .inl (by omega))) fun u₁ ⟨O₁, V₁, K₁⟩ => ?_)
  rw [cb1, l0] at O₁
  rw [cw1, l0, hp] at V₁
  have h₁ := h.keep K₁ (by decide) (by decide) (O₁.mono (Nat.zero_le _) (by omega))
  refine WP.seq (WP.mono (copy_ok h₁ (x := .slot .wide 15) (d := .slot .wide 5) (one_ok .wide)
    (by rw [cb1, l15]; omega) (by rw [cb1, l5]; omega)
    (by rw [cb1, l5, l15]; exact .inl (by omega))) fun u₂ ⟨O₂, V₂, K₂⟩ => ?_)
  rw [cb1, l5] at O₂
  rw [cw1, l5, O₁.val32 (.inr (by rw [l15]; omega)) (by rw [l15]; omega), hx] at V₂
  have h₂ := h₁.keep K₂ (by decide) (by decide) (O₂.mono (Nat.zero_le _) (by omega))
  have M₂ : sv u₂.mem base len .wide 0 = p := by
    simp only [sv]; rw [l0, O₂.val32 (.inl (by omega)) (by omega), V₁]
  -- The context of the factor.
  refine WP.seq (WP.mono (prepCtx_ok h₂ .wide) fun u₃ ⟨C₃, one₃, R₃, F₃, K₃⟩ => ?_)
  rw [M₂] at C₃ R₃
  have X₃ : sv u₃.mem base len .wide 5 = x := by
    rw [prepR_sv h₂ .wide F₃ h₂.room (j := 5) (by decide) (by decide) (by decide)]
    simp only [sv]; rw [l5]; exact V₂
  -- `x R mod M`, then `x mod M`.
  refine WP.seq (WP.mono (cmul_ok C₃ (o := 5) (a := 5) (b := 4) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [R₃]; exact Nat.mod_lt _ (by omega))) fun u₄ ⟨C₄, K₄, F₄, L₄, V₄⟩ => ?_)
  have B₄ : sv u₄.mem base len .wide 5 = x * 2 ^ (8 * bc len .wide) % safeM p := by
    have v := VG.Proof.Dsa.mont_scale C₃.coprime (out := sv u₄.mem base len .wide 5) (input := x)
      (c := 2 ^ (8 * bc len .wide)) (by rw [V₄, X₃, R₃, RR])
    rwa [Nat.mod_eq_of_lt L₄] at v
  have one₄ : sv u₄.mem base len .wide 3 = 1 := by
    rw [mulR_sv C₃.inp F₄ C₃.inp.room (o := 5) (j := 3) (by decide) (by decide) (by decide) (by decide)
      (by decide)]; exact one₃
  refine WP.seq (WP.mono (cmul_ok C₄ (o := 5) (a := 5) (b := 3) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [one₄]; exact hM)) fun u₅ ⟨C₅, K₅, F₅, L₅, V₅⟩ => ?_)
  have D₅ : sv u₅.mem base len .wide 5 = x % safeM p := by
    have v := VG.Proof.Dsa.mont_decode (A := sv u₄.mem base len .wide 5) (out := sv u₅.mem base len .wide 5)
      C₄.coprime (by rw [B₄, Nat.mod_mod]) (by rw [V₅, one₄])
    rwa [Nat.mod_eq_of_lt L₅] at v
  -- Into the wide slot `o`.
  have h₅ := C₅.inp
  refine WP.seq (WP.mono (copy_ok h₅ (x := .slot .wide 5) (d := .slot .wide o) (one_ok .wide)
    (by rw [cb1, l5]; omega) (by rw [cb1]; omega)
    (by rw [cb1, l5]; exact .inr (by omega))) fun u₆ ⟨O₆, V₆, K₆⟩ => ?_)
  rw [cb1] at O₆
  rw [cw1] at V₆
  have sp₁ : u₁.gpr .esp = s.gpr .esp := K₁.1 _ (by decide)
  have sp₂ : u₂.gpr .esp = s.gpr .esp := (K₂.1 _ (by decide)).trans sp₁
  have sp₃ : u₃.gpr .esp = s.gpr .esp := (K₃.1 _ (by decide)).trans sp₂
  have sp₄ : u₄.gpr .esp = s.gpr .esp := (K₄.1 _ (by decide)).trans sp₃
  rw [sp₂] at F₃
  rw [sp₃] at F₄
  rw [sp₄] at F₅
  refine k u₆ (h₅.keep K₆ (by decide) (by decide) (O₆.mono (Nat.zero_le _) (by omega)))
    ?_ (by rw [V₆]; simp only [sv] at D₅; rw [l5] at D₅ ⊢; exact D₅) ?_
  · have i0 := slot_in h .wide (j := 0) (by decide)
    have i5 := slot_in h .wide (j := 5) (by decide)
    rw [l0] at i0
    rw [l5] at i5
    exact ((((stR_of_outside h ho' O₁ ⟨_, by simp, i0⟩).trans (stR_of_outside h ho' O₂ ⟨_, by simp, i5⟩)).trans
      (stR_widen F₃ (prepR_in h₂ .wide o))).trans ((stR_widen F₄ (mulR_in C₃.inp .wide (by decide) o)).trans
      (stR_widen F₅ (mulR_in C₄.inp .wide (by decide) o)))).trans
      (stR_of_outside h ho' O₆ ⟨(lo len (.slot .wide o), 2 * bc len .wide), by simp, Nat.le_refl _,
        by dsimp only; omega⟩)
  · exact (((((K₁.mono (by decide)).trans (K₂.mono (by decide))).trans K₃).trans
      ((K₄.trans K₅).mono (by decide))).trans (K₆.mono (by decide)))

theorem safeM_lt {p k : Nat} (hp : p < 2 ^ (32 * k)) (hk : 1 ≤ k) : safeM p < 2 ^ (32 * k) := by
  have : 2 ^ 32 ≤ 2 ^ (32 * k) := Nat.pow_le_pow_right (by decide) (by omega)
  unfold safeM; split <;> omega

/-- Where the half context's slots lie. -/
structure HalfLay (len : Nat) : Prop where
  cw : cwc len .half ≤ cwc len .wide
  cw8 : 8 ≤ cwc len .half
  bh : bc len .half = 4 * cwc len .half
  h0 : lo len (.slot .half 0) = numBase
  h5 : lo len (.slot .half 5) = numBase + 5 * st len .half
  h8 : lo len (.slot .half 8) = numBase + 8 * st len .half
  sth : st len .half = 2 * bc len .half + 32
  top : lo len (.slot .half 8) + st len .half ≤ lo len (.slot .wide 9)

theorem HalfLay.mk' (h : In Ex base bytes len args s) : HalfLay len := by
  have := bc_le_wide len .half
  have a := bc_eq_cwc len .half
  have b := bc_eq_cwc len .wide
  have g := bc_ge h.lower' .half
  exact ⟨by omega, by omega, a, sl_zero len .half, rfl, rfl, rfl, half_in_wide h (by decide)⟩

/-- The factor, a number below it and the exponent into the half context's slots 0, 5 and 8. -/
theorem narrowCopies_ok (h : In Ex base bytes len args s) {f e o : Nat} (hf9 : 9 ≤ f) (hf : f ≤ 15) (he9 : 9 ≤ e)
    (he : e ≤ 15) (ho16 : 16 ≤ o) (ho : o ≤ 17) {p d y : Nat}
    (hp : val32 s.mem base (lo len (.slot .wide f)) (cwc len .half) = p)
    (hd : val32 s.mem base (lo len (.slot .wide e)) (cwc len .half) = d)
    (hy : val32 s.mem base (lo len (.slot .wide o)) (cwc len .half) = y) {P : Prog isa} {Q : State → Prop}
    (k : ∀ u, In Ex base bytes len args u → Frame (frameR base (s.gpr .esp) (stR len o)) s.mem u.mem →
      sv u.mem base len .half 0 = p → sv u.mem base len .half 5 = y → sv u.mem base len .half 8 = d →
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u → WP isa P u Q) :
    WP isa (.seq (copy (.slot .wide f) (.slot .half 0) (one .half)) <|
      .seq (copy (.slot .wide o) (.slot .half 5) (one .half)) <|
      .seq (copy (.slot .wide e) (.slot .half 8) (one .half)) P) s Q := by
  have Lf := WideLay.mk' h hf9 hf ho16 ho
  have Le := WideLay.mk' h he9 he ho16 ho
  have l9 := Lf.l9
  have f1 := Lf.f1
  have f2 := Lf.f2
  have e1 := Le.f1
  have e2 := Le.f2
  have o1 := Lf.o1
  have o2 := Lf.o2
  have fit := Lf.fit
  have l16 := Lf.l16
  have l18 := Lf.l18
  have est := Lf.est
  obtain ⟨cwle, cw8, bh, h0, h5, h8, sth, top⟩ := HalfLay.mk' h
  have bw := bc_eq_cwc len .wide
  have ho' : o ≤ 19 := by omega
  have bl := h.bytes_lt
  have cb1 : cb len (one .half) = bc len .half := by simp [cb, one]
  have cw1 : cw len (one .half) = cwc len .half := by simp [cw, cwc, cb, one]
  refine WP.seq (WP.mono (copy_ok h (x := .slot .wide f) (d := .slot .half 0) (one_ok .half)
    (by rw [cb1]; omega) (by rw [cb1, h0]; omega) (by rw [cb1, h0]; exact .inl (by omega)))
    fun u₂ ⟨O₂, V₂, K₂⟩ => ?_)
  rw [cb1, h0] at O₂
  rw [cw1, h0, hp] at V₂
  have h₂ := h.keep K₂ (by decide) (by decide) (O₂.mono (Nat.zero_le _) (by omega))
  refine WP.seq (WP.mono (copy_ok h₂ (x := .slot .wide o) (d := .slot .half 5) (one_ok .half)
    (by rw [cb1]; omega) (by rw [cb1, h5]; omega) (by rw [cb1, h5]; exact .inl (by omega)))
    fun u₃ ⟨O₃, V₃, K₃⟩ => ?_)
  rw [cb1, h5] at O₃
  rw [cw1, h5, O₂.val32 (d := lo len (.slot .wide o)) (k := cwc len .half) (.inr (by omega)) (by omega), hy] at V₃
  have h₃ := h₂.keep K₃ (by decide) (by decide) (O₃.mono (Nat.zero_le _) (by omega))
  refine WP.seq (WP.mono (copy_ok h₃ (x := .slot .wide e) (d := .slot .half 8) (one_ok .half)
    (by rw [cb1]; omega) (by rw [cb1, h8]; omega) (by rw [cb1, h8]; exact .inl (by omega)))
    fun u₄ ⟨O₄, V₄, K₄⟩ => ?_)
  rw [cb1, h8] at O₄
  rw [cw1, h8, O₃.val32 (d := lo len (.slot .wide e)) (k := cwc len .half) (.inr (by omega)) (by omega),
    O₂.val32 (d := lo len (.slot .wide e)) (k := cwc len .half) (.inr (by omega)) (by omega), hd] at V₄
  have h₄ := h₃.keep K₄ (by decide) (by decide) (O₄.mono (Nat.zero_le _) (by omega))
  have i0 := slot_in h .half (j := 0) (by decide)
  have i5 := slot_in h .half (j := 5) (by decide)
  have i8 := slot_in h .half (j := 8) (by decide)
  rw [h0] at i0
  rw [h5] at i5
  rw [h8] at i8
  have sp₂ : u₂.gpr .esp = s.gpr .esp := K₂.1 _ (by decide)
  have sp₃ : u₃.gpr .esp = s.gpr .esp := (K₃.1 _ (by decide)).trans sp₂
  refine k u₄ h₄ (((stR_of_outside h ho' O₂ ⟨_, by simp, i0⟩).trans (stR_of_outside h ho' O₃ ⟨_, by simp, i5⟩)).trans
    (stR_of_outside h ho' O₄ ⟨_, by simp, i8⟩)) ?_ ?_ (by simp only [sv]; rw [h8, V₄]) ?_
  · simp only [sv]; rw [h0, O₄.val32 (d := numBase) (k := cwc len .half) (.inl (by omega)) (by omega),
      O₃.val32 (d := numBase) (k := cwc len .half) (.inl (by omega)) (by omega), V₂]
  · simp only [sv]; rw [h5, O₄.val32 (d := numBase + 5 * st len .half) (k := cwc len .half) (.inl (by omega)) (by omega), V₃]
  · exact (((K₂.trans K₃).trans K₄).mono (by decide))

/-- A factor's context prepared at width `c`, the power, and its result zero-extended into the wide
slot `o`. -/
theorem powerTail_ok (h : In Ex base bytes len args s) (c : Ctx) {o : Nat} (ho16 : 16 ≤ o) (ho : o ≤ 17)
    {p d y : Nat} (hp : sv s.mem base len c 0 = p) (hy : sv s.mem base len c 5 = y)
    (hd : sv s.mem base len c 8 = d) :
    WP isa (.seq (prepare c) (.seq (windowPower c) (saveResult c o))) s fun u =>
      Frame (frameR base (s.gpr .esp) (stR len o)) s.mem u.mem ∧
      val32 u.mem base (lo len (.slot .wide o)) (2 * cwc len .wide) = y ^ d % safeM p ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u := by
  have ho' : o ≤ 19 := by omega
  refine WP.seq (WP.mono (prepCtx_ok h c) fun u₅ ⟨C₅, one₅, R₅, F₅, K₅⟩ => ?_)
  rw [hp] at C₅ R₅
  have B₅ : sv u₅.mem base len c 5 = y := by
    rw [prepR_sv h c F₅ h.room (j := 5) (by decide) (by decide) (by decide), hy]
  have E₅ : sv u₅.mem base len c 8 = d := by
    rw [prepR_sv h c F₅ h.room (j := 8) (by decide) (by decide) (by decide), hd]
  refine WP.seq (WP.mono (windowPower_ok C₅ one₅ R₅) fun u₆ ⟨C₆, F₆, K₆, Y₆⟩ => ?_)
  rw [B₅, E₅] at Y₆
  refine WP.mono (saveResult_ok C₆.inp c (o := o) (by omega) ho') fun u ⟨O₇, V₇, K₇⟩ => ⟨?_, by rw [V₇, Y₆], ?_⟩
  · have sp₅ : u₅.gpr .esp = s.gpr .esp := K₅.1 _ (by decide)
    rw [sp₅] at F₆
    exact ((stR_widen F₅ (prepR_in h c o)).trans (stR_widen F₆ (pwR_in C₅.inp c o))).trans
      (stR_of_outside h ho' O₇ ⟨(lo len (.slot .wide o), 2 * bc len .wide), by simp, Nat.le_refl _,
        Nat.le_refl _⟩)
  · exact (K₅.trans K₆).trans (K₇.mono (by decide))

/-- The input to the power `d` modulo the factor `p`, at half the width, zero-extended into the wide
slot `o`. -/
theorem narrowPower_ok (h : In Ex base bytes len args s) {f e o : Nat} (hf9 : 9 ≤ f) (hf : f ≤ 15) (he9 : 9 ≤ e)
    (he : e ≤ 15) (ho16 : 16 ≤ o) (ho : o ≤ 17) {p d x : Nat}
    (hp : val32 s.mem base (lo len (.slot .wide f)) (cwc len .wide) = p) (hpn : p < 2 ^ (32 * cwc len .half))
    (hd : val32 s.mem base (lo len (.slot .wide e)) (cwc len .wide) = d) (hdn : d < 2 ^ (32 * cwc len .half))
    (hx : val32 s.mem base (lo len (.slot .wide 15)) (cwc len .wide) = x) :
    WP isa (narrowPower f e o) s fun u =>
      Frame (frameR base (s.gpr .esp) (stR len o)) s.mem u.mem ∧
      val32 u.mem base (lo len (.slot .wide o)) (2 * cwc len .wide) = x ^ d % safeM p ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u := by
  have Lf := WideLay.mk' h hf9 hf ho16 ho
  have Le := WideLay.mk' h he9 he ho16 ho
  have cwle := (HalfLay.mk' h).cw
  have cw8 := (HalfLay.mk' h).cw8
  have hM := safeM_gt p
  have sml := safeM_lt hpn (by omega)
  have split : cwc len .half + (cwc len .wide - cwc len .half) = cwc len .wide := by omega
  unfold narrowPower
  refine reduce_ok h hf9 hf ho16 ho hp hx fun u₁ h₁ F₁ V₁ K₁ => ?_
  have bw := bc_eq_cwc len .wide
  have kf := stR_keep h ho16 ho F₁ h.room (k := cwc len .wide) Lf.f1
    (by have := Lf.f2; have := Lf.o1; have := Lf.l16; have := Lf.l18; have := Lf.est; omega)
    (.inl (by have := Lf.f2; have := Lf.o1; have := Lf.est; omega))
  have ke := stR_keep h ho16 ho F₁ h.room (k := cwc len .wide) Le.f1
    (by have := Le.f2; have := Le.o1; have := Le.l16; have := Le.l18; have := Le.est; omega)
    (.inl (by have := Le.f2; have := Le.o1; have := Le.est; omega))
  have P₁ : val32 u₁.mem base (lo len (.slot .wide f)) (cwc len .half) = p :=
    val32_low (b := cwc len .wide - cwc len .half) (by rw [split, kf, hp]) hpn
  have D₁ : val32 u₁.mem base (lo len (.slot .wide e)) (cwc len .half) = d :=
    val32_low (b := cwc len .wide - cwc len .half) (by rw [split, ke, hd]) hdn
  have X₁ : val32 u₁.mem base (lo len (.slot .wide o)) (cwc len .half) = x % safeM p :=
    val32_low (b := cwc len .wide - cwc len .half) (by rw [split, V₁])
      (by have := Nat.mod_lt x (by omega : 0 < safeM p); omega)
  refine narrowCopies_ok h₁ hf9 hf he9 he ho16 ho P₁ D₁ X₁ fun u₄ h₄ F₄ M₄ B₄ E₄ K₄ => ?_
  refine WP.mono (powerTail_ok h₄ .half ho16 ho M₄ B₄ E₄) fun u ⟨F, V, K⟩ => ⟨?_, ?_, ?_⟩
  · have sp₁ : u₁.gpr .esp = s.gpr .esp := K₁.1 _ (by decide)
    have sp₄ : u₄.gpr .esp = s.gpr .esp := (K₄.1 _ (by decide)).trans sp₁
    rw [sp₁] at F₄
    rw [sp₄] at F
    exact (F₁.trans F₄).trans F
  · rw [V, ← Nat.pow_mod]
  · exact (K₁.trans K₄).trans K

/-- The input to the power `d` modulo the factor `p`, at the modulus's width, zero-extended into the
wide slot `o`. -/
theorem widePower_ok (h : In Ex base bytes len args s) {f e o : Nat} (hf9 : 9 ≤ f) (hf : f ≤ 15) (he9 : 9 ≤ e)
    (he : e ≤ 15) (ho16 : 16 ≤ o) (ho : o ≤ 17) {p d x : Nat}
    (hp : val32 s.mem base (lo len (.slot .wide f)) (cwc len .wide) = p)
    (hd : val32 s.mem base (lo len (.slot .wide e)) (cwc len .wide) = d)
    (hx : val32 s.mem base (lo len (.slot .wide 15)) (cwc len .wide) = x) :
    WP isa (widePower f e o) s fun u =>
      Frame (frameR base (s.gpr .esp) (stR len o)) s.mem u.mem ∧
      val32 u.mem base (lo len (.slot .wide o)) (2 * cwc len .wide) = x ^ d % safeM p ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u := by
  have Lf := WideLay.mk' h hf9 hf ho16 ho
  have Le := WideLay.mk' h he9 he ho16 ho
  have l0 := Lf.l0
  have l5 := Lf.l5
  have l8 := Lf.l8
  have l9 := Lf.l9
  have l15 := Lf.l15
  have f1 := Lf.f1
  have f2 := Lf.f2
  have e1 := Le.f1
  have e2 := Le.f2
  have o1 := Lf.o1
  have o2 := Lf.o2
  have fit := Lf.fit
  have l16 := Lf.l16
  have l18 := Lf.l18
  have est := Lf.est
  have bw := bc_eq_cwc len .wide
  have bl := h.bytes_lt
  have ho' : o ≤ 19 := by omega
  have cb1 : cb len (one .wide) = bc len .wide := by simp [cb, one]
  have cw1 : cw len (one .wide) = cwc len .wide := by simp [cw, cwc, cb, one]
  unfold widePower
  refine WP.seq (WP.mono (copy_ok h (x := .slot .wide f) (d := .slot .wide 0) (one_ok .wide)
    (by rw [cb1]; omega) (by rw [cb1, l0]; omega) (by rw [cb1, l0]; exact .inl (by omega)))
    fun u₁ ⟨O₁, V₁, K₁⟩ => ?_)
  rw [cb1, l0] at O₁
  rw [cw1, l0, hp] at V₁
  have h₁ := h.keep K₁ (by decide) (by decide) (O₁.mono (Nat.zero_le _) (by omega))
  refine WP.seq (WP.mono (copy_ok h₁ (x := .slot .wide 15) (d := .slot .wide 5) (one_ok .wide)
    (by rw [cb1, l15]; omega) (by rw [cb1, l5]; omega) (by rw [cb1, l5, l15]; exact .inl (by omega)))
    fun u₂ ⟨O₂, V₂, K₂⟩ => ?_)
  rw [cb1, l5] at O₂
  rw [cw1, l5, O₁.val32 (d := lo len (.slot .wide 15)) (k := cwc len .wide) (.inr (by omega)) (by omega), hx] at V₂
  have h₂ := h₁.keep K₂ (by decide) (by decide) (O₂.mono (Nat.zero_le _) (by omega))
  refine WP.seq (WP.mono (copy_ok h₂ (x := .slot .wide e) (d := .slot .wide 8) (one_ok .wide)
    (by rw [cb1]; omega) (by rw [cb1, l8]; omega) (by rw [cb1, l8]; exact .inl (by omega)))
    fun u₃ ⟨O₃, V₃, K₃⟩ => ?_)
  rw [cb1, l8] at O₃
  rw [cw1, l8, O₂.val32 (d := lo len (.slot .wide e)) (k := cwc len .wide) (.inr (by omega)) (by omega),
    O₁.val32 (d := lo len (.slot .wide e)) (k := cwc len .wide) (.inr (by omega)) (by omega), hd] at V₃
  have h₃ := h₂.keep K₃ (by decide) (by decide) (O₃.mono (Nat.zero_le _) (by omega))
  have M₃ : sv u₃.mem base len .wide 0 = p := by
    simp only [sv]; rw [l0, O₃.val32 (d := numBase) (k := cwc len .wide) (.inl (by omega)) (by omega),
      O₂.val32 (d := numBase) (k := cwc len .wide) (.inl (by omega)) (by omega), V₁]
  have B₃ : sv u₃.mem base len .wide 5 = x := by
    simp only [sv]; rw [l5, O₃.val32 (d := numBase + 5 * st len .wide) (k := cwc len .wide) (.inl (by omega))
      (by omega), V₂]
  have E₃ : sv u₃.mem base len .wide 8 = d := by simp only [sv]; rw [l8, V₃]
  refine WP.mono (powerTail_ok h₃ .wide ho16 ho M₃ B₃ E₃) fun u ⟨F, V, K⟩ => ⟨?_, V, ?_⟩
  · have i0 := slot_in h .wide (j := 0) (by decide)
    have i5 := slot_in h .wide (j := 5) (by decide)
    have i8 := slot_in h .wide (j := 8) (by decide)
    rw [l0] at i0
    rw [l5] at i5
    rw [l8] at i8
    have sp₁ : u₁.gpr .esp = s.gpr .esp := K₁.1 _ (by decide)
    have sp₃ : u₃.gpr .esp = s.gpr .esp := (K₃.1 _ (by decide)).trans ((K₂.1 _ (by decide)).trans sp₁)
    rw [sp₃] at F
    exact (((stR_of_outside h ho' O₁ ⟨_, by simp, i0⟩).trans (stR_of_outside h ho' O₂ ⟨_, by simp, i5⟩)).trans
      (stR_of_outside h ho' O₃ ⟨_, by simp, i8⟩)).trans F
  · exact (((K₁.trans K₂).trans K₃).mono (by decide)).trans K

/-- `cmp d, src`, and the carry. -/
theorem wp_cmpC {is : List Instr} {s : State} {Q : State → Prop} {d : Reg} {src : Src} {v : BitVec 32}
    (h : readSrc s src = some v)
    (k : ∀ t, Fupd s t → t.cf = some (decide ((s.gpr d).toNat < v.toNat)) → WP isa (.block is) t Q) :
    WP isa (.block (.alu .cmp d src :: is)) s Q :=
  cons (s' := arithFlags s (s.gpr d - v) (decide ((s.gpr d).toNat < v.toNat)) (subOverflow (s.gpr d) v (s.gpr d - v)))
    (by simp only [exec, execAlu, h, Option.bind_some]) (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl)

/-- A factor's power, at half the width when its length (argument `l`) fits it. -/
theorem power_ok (h : In Ex base bytes len args s) {f e o l : Nat} (hf9 : 9 ≤ f) (hf : f ≤ 15) (he9 : 9 ≤ e)
    (he : e ≤ 15) (ho16 : 16 ≤ o) (ho : o ≤ 17) (hl : l < 18) {p d x : Nat}
    (hp : val32 s.mem base (lo len (.slot .wide f)) (cwc len .wide) = p)
    (hd : val32 s.mem base (lo len (.slot .wide e)) (cwc len .wide) = d)
    (hx : val32 s.mem base (lo len (.slot .wide 15)) (cwc len .wide) = x)
    (fits : (args l).toNat ≤ bc len .half → p < 2 ^ (32 * cwc len .half) ∧ d < 2 ^ (32 * cwc len .half)) :
    WP isa (power f e o l) s fun u =>
      Frame (frameR base (s.gpr .esp) (stR len o)) s.mem u.mem ∧
      val32 u.mem base (lo len (.slot .wide o)) (2 * cwc len .wide) = x ^ d % safeM p ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u := by
  have hb := bc_le h.upper' .half
  unfold power
  simp only [List.cons_append]
  refine WP.seq (wp_movS (h.arg hl) fun u₁ a₁ _ => ?_)
  have h₁ := h.regs a₁.keeps a₁.mem
  refine widthC_ok (k := 0) (c := .half) (r := .edx) h₁.width h.upper' fun u₂ K₂ m₂ e₂ => ?_
  refine wp_addS rfl fun u₃ a₃ _ => wp_cmpC rfl fun u₄ f₄ c₄ => WP.block_nil ?_
  have K₄ : Keeps [.eax, .edx] s u₄ :=
    (((a₁.keeps.mono (by decide)).trans (K₂.mono (by decide))).trans (a₃.keeps.mono (by decide))).trans
      (f₄.keeps _)
  have m₄ : u₄.mem = s.mem := by rw [f₄.mem, a₃.mem, m₂, a₁.mem]
  have h₄ := h.regs K₄ m₄
  have eax : u₃.gpr .eax = args l := by rw [a₃.other _ (by decide), K₂.1 _ (by decide), a₁.gpr]
  have edx : (u₃.gpr .edx).toNat = bc len .half + 1 := by
    rw [a₃.gpr, e₂, BitVec.toNat_add, BitVec.toNat_ofNat, show (1 : BitVec 32).toNat = 1 from rfl]
    omega
  rw [eax, edx] at c₄
  have sp : u₄.gpr .esp = s.gpr .esp := K₄.1 _ (by decide)
  have hp' : val32 u₄.mem base (lo len (.slot .wide f)) (cwc len .wide) = p := by rw [m₄, hp]
  have hd' : val32 u₄.mem base (lo len (.slot .wide e)) (cwc len .wide) = d := by rw [m₄, hd]
  have hx' : val32 u₄.mem base (lo len (.slot .wide 15)) (cwc len .wide) = x := by rw [m₄, hx]
  refine WP.ite _ c₄ (fun nar => ?_) (fun _ => ?_)
  · have F := fits (by have := of_decide_eq_true nar; omega)
    refine WP.mono (narrowPower_ok h₄ hf9 hf he9 he ho16 ho hp' F.1 hd' F.2 hx') fun u ⟨Fu, Vu, Ku⟩ =>
      ⟨by rw [sp, m₄] at Fu; exact Fu, Vu, (K₄.mono (by decide)).trans Ku⟩
  · refine WP.mono (widePower_ok h₄ hf9 hf he9 he ho16 ho hp' hd' hx') fun u ⟨Fu, Vu, Ku⟩ =>
      ⟨by rw [sp, m₄] at Fu; exact Fu, Vu, (K₄.mono (by decide)).trans Ku⟩

end

end VG.Proof.Bignum.X86.CrtRt
