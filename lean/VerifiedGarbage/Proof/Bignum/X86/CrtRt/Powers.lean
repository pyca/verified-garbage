module

public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.StageR
import VerifiedGarbage.Proof.Framework.Omega

/-! # The factors' powers

`reduceHalf_ok`: a number of `2 Bh` bytes modulo the half context's
modulus, from its two halves. `narrowPower_ok` and
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
    have := Nat.mul_le_mul_right (st len c) hj; simp only [lo]; omega_arith
  have a3 := slot_apart len c (o := 3) (j := j) (by omega_arith)
  have a4 := slot_apart len c (o := 4) (j := j) (by omega_arith)
  have a7 := slot_apart len c (o := 7) (j := j) h7
  have p1 := slot_past1 len c (j := j) (by omega_arith)
  have z0 : lo len (.slot c 0) = numBase := sl_zero len c
  have e1 : lo len (.slot c 1) = numBase + st len c := by simp [lo]
  have nb : numBase = 3336 := rfl
  refine frameR_val32 F R nw (by omega_arith) ?_ (prepR_fit h c)
  intro p hp
  simp only [prepR, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [invOff] <;> omega_arith

/-- Changes below the wide slot 9 keep the slots from 9 on. -/
theorem low_keep (h : In Ex base bytes len args s) {sp : BitVec 32} {ws : List (Nat × Nat)} {m m' : Mem}
    (F : Frame (frameR base sp ws) m m') (R : CallRoom sp base bytes) (fit : ∀ p ∈ ws, p.1 + p.2 ≤ bytes)
    (hw : ∀ p ∈ ws, p.1 + p.2 ≤ lo len (.slot .wide 9)) {d k : Nat} (hd : lo len (.slot .wide 9) ≤ d)
    (hk : d + 4 * k ≤ bytes) : val32 m' base d k = val32 m base d k :=
  frameR_val32 F R h.scratch.nowrap hk (fun p hp => .inr (by have := hw p hp; omega_arith)) fit

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
  have b := Nat.mul_le_mul_right (st len .wide) (show f + 1 ≤ 16 by omega_arith)
  have c := Nat.mul_le_mul_right (st len .wide) ho16
  have d := Nat.mul_le_mul_right (st len .wide) (show o + 1 ≤ 18 by omega_arith)
  rw [Nat.succ_mul] at b d
  have ef : lo len (.slot .wide f) = numBase + f * st len .wide := rfl
  have eo : lo len (.slot .wide o) = numBase + o * st len .wide := rfl
  have e9 : lo len (.slot .wide 9) = numBase + 9 * st len .wide := rfl
  have e16 : lo len (.slot .wide 16) = numBase + 16 * st len .wide := rfl
  have e18 : lo len (.slot .wide 18) = numBase + 18 * st len .wide := rfl
  exact ⟨rfl, sl_zero len .wide, rfl, rfl, rfl, rfl, rfl, rfl, by omega_arith, by omega_arith, by omega_arith, by omega_arith,
    h.slot_fit .wide (by decide), rfl⟩

theorem safeM_lt {p k : Nat} (hp : p < 2 ^ (32 * k)) (hk : 1 ≤ k) : safeM p < 2 ^ (32 * k) := by
  have : 2 ^ 32 ≤ 2 ^ (32 * k) := Nat.pow_le_pow_right (by decide) (by omega_arith)
  unfold safeM; split <;> omega_arith

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
  exact ⟨by omega_arith, by omega_arith, a, sl_zero len .half, rfl, rfl, rfl, half_in_wide h (by decide)⟩

/-- The number of `2 Bh` bytes in the wide slot `j` modulo the half context's modulus `M` into the
half slot 5, from its low half `l` and high half `h` (through slot 6): `l R² R⁻¹ R⁻¹` and `h R² R⁻¹`
added modulo `M`. The context, one in slot 3, `R² mod M` in slot 4 and slot 8 are kept. -/
theorem reduceHalf_ok {M : Nat} (C : CtxOk Ex base bytes len args .half M s) (h3 : sv s.mem base len .half 3 = 1)
    (h4 : sv s.mem base len .half 4 = 2 ^ (16 * bc len .half) % M) {j : Nat} (hj9 : 9 ≤ j) (hj : j ≤ 17)
    {X : Nat} (hX : val32 s.mem base (lo len (.slot .wide j)) (2 * cwc len .half) = X) :
    WP isa (reduceHalf j) s fun u =>
      CtxOk Ex base bytes len args .half M u ∧ sv u.mem base len .half 3 = 1 ∧
      sv u.mem base len .half 4 = 2 ^ (16 * bc len .half) % M ∧ sv u.mem base len .half 5 = X % M ∧
      sv u.mem base len .half 8 = sv s.mem base len .half 8 ∧
      Frame (frameR base (s.gpr .esp) [(numBase, 9 * st len .wide)]) s.mem u.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s u := by
  have h := C.inp
  have nw := h.scratch.nowrap
  have bl := h.bytes_lt
  obtain ⟨cwle, cw8, bh, h0, h5, h8, sth, top⟩ := HalfLay.mk' h
  have bw := bc_eq_cwc len .wide
  have bhw := bc_le_wide len .half
  have Wj := h.wide_fit (j := j) (by omega)
  have e9 : lo len (.slot .wide 9) = numBase + 9 * st len .wide := rfl
  have ej : lo len (.slot .wide j) = numBase + j * st len .wide := rfl
  have j9 : lo len (.slot .wide 9) ≤ lo len (.slot .wide j) := by
    have := Nat.mul_le_mul_right (st len .wide) hj9; omega
  have h6 : lo len (.slot .half 6) = numBase + 6 * st len .half := rfl
  have nb : numBase = 3336 := rfl
  have cb1 : cb len (one .half) = bc len .half := by simp [cb, one]
  have cw1 : cw len (one .half) = cwc len .half := by simp [cw, cwc, cb, one]
  have hM := C.gt
  have RR : 2 ^ (16 * bc len .half) = 2 ^ (8 * bc len .half) * 2 ^ (8 * bc len .half) := by
    rw [← Nat.pow_add]; congr 1; omega
  -- The halves.
  have split := val32_append s.mem base (lo len (.slot .wide j)) (cwc len .half) (cwc len .half)
  rw [show cwc len .half + cwc len .half = 2 * cwc len .half by omega, hX,
    show lo len (.slot .wide j) + 4 * cwc len .half = lo len (.slot .wide j) + bc len .half by omega] at split
  -- The low half into slot 5.
  refine WP.seq (WP.mono (copy_ok h (x := .slot .wide j) (d := .slot .half 5) (one_ok .half)
    (by rw [cb1]; omega) (by rw [cb1, h5]; omega) (by rw [cb1, h5]; exact .inl (by omega))) fun u₁ ⟨O₁, V₁, K₁⟩ => ?_)
  rw [cb1] at O₁
  rw [cw1] at V₁
  have sp₁ : u₁.gpr .esp = s.gpr .esp := K₁.1 _ (by decide)
  have F₁ : Frame (frameR base (s.gpr .esp) [(lo len (.slot .half 5), bc len .half)]) s.mem u₁.mem :=
    frameR_of_outside O₁ (by omega) (by simp)
  have C₁ := C.keepF K₁ (by decide) (by decide) F₁ (by simp; omega) (by simp; omega)
  -- The high half into slot 6.
  refine WP.seq (WP.mono (copyHigh_ok C₁.inp (j := j) (d := 6) (by omega) (by omega) (by omega))
    fun u₂ ⟨O₂, V₂, K₂⟩ => ?_)
  rw [cw1, O₁.val32 (.inr (by omega)) (by omega)] at V₂
  have sp₂ : u₂.gpr .esp = s.gpr .esp := (K₂.1 _ (by decide)).trans sp₁
  have F₂ : Frame (frameR base (u₁.gpr .esp) [(lo len (.slot .half 6), bc len .half)]) u₁.mem u₂.mem :=
    frameR_of_outside O₂ (by omega) (by simp)
  have C₂ := C₁.keepF K₂ (by decide) (by decide) F₂ (by simp; omega) (by simp; omega)
  have keep₂ : ∀ k, k ≠ 5 → k ≠ 6 → k ≤ 8 → sv u₂.mem base len .half k = sv s.mem base len .half k := by
    intro k k5 k6 k8
    have ek : lo len (.slot .half k) = numBase + k * st len .half := rfl
    have k8' := Nat.mul_le_mul_right (st len .half) k8
    have d6 : lo len (.slot .half k) + 4 * cwc len .half ≤ lo len (.slot .half 6) ∨
        lo len (.slot .half 6) + bc len .half ≤ lo len (.slot .half k) := by
      rcases Nat.lt_or_gt_of_ne k6 with l | l
      · have := Nat.mul_le_mul_right (st len .half) (show k + 1 ≤ 6 by omega); rw [Nat.succ_mul] at this
        exact .inl (by omega)
      · have := Nat.mul_le_mul_right (st len .half) (show 7 ≤ k by omega); exact .inr (by omega)
    have d5 : lo len (.slot .half k) + 4 * cwc len .half ≤ lo len (.slot .half 5) ∨
        lo len (.slot .half 5) + bc len .half ≤ lo len (.slot .half k) := by
      rcases Nat.lt_or_gt_of_ne k5 with l | l
      · have := Nat.mul_le_mul_right (st len .half) (show k + 1 ≤ 5 by omega); rw [Nat.succ_mul] at this
        exact .inl (by omega)
      · have := Nat.mul_le_mul_right (st len .half) (show 6 ≤ k by omega); exact .inr (by omega)
    simp only [sv]
    rw [O₂.val32 d6 (by omega), O₁.val32 d5 (by omega)]
  have L₂ : sv u₂.mem base len .half 5 = val32 s.mem base (lo len (.slot .wide j)) (cwc len .half) := by
    simp only [sv]; rw [O₂.val32 (.inl (by omega)) (by omega), V₁]
  have H₂ : sv u₂.mem base len .half 6 = val32 s.mem base (lo len (.slot .wide j) + bc len .half) (cwc len .half) := by
    simp only [sv]; rw [V₂]
  have R₂ : sv u₂.mem base len .half 4 = 2 ^ (16 * bc len .half) % M := by
    rw [keep₂ 4 (by decide) (by decide) (by decide), h4]
  have one₂ : sv u₂.mem base len .half 3 = 1 := by rw [keep₂ 3 (by decide) (by decide) (by decide), h3]
  have E₂ : sv u₂.mem base len .half 8 = sv s.mem base len .half 8 := keep₂ 8 (by decide) (by decide) (by decide)
  -- `l R mod M`, then `l mod M`.
  refine WP.seq (WP.mono (cmul_ok C₂ (o := 5) (a := 5) (b := 4) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [R₂]; exact Nat.mod_lt _ (by omega))) fun u₃ ⟨C₃, K₃, F₃, L₃, V₃⟩ => ?_)
  have B₃ : sv u₃.mem base len .half 5 % M =
      val32 s.mem base (lo len (.slot .wide j)) (cwc len .half) * 2 ^ (8 * bc len .half) % M :=
    VG.Proof.Dsa.mont_scale C₂.coprime (by rw [V₃, L₂, R₂, RR])
  have mk3 : ∀ k, 3 ≤ k → k ≤ 8 → k ≠ 5 → sv u₃.mem base len .half k = sv u₂.mem base len .half k :=
    fun k a b c => mulR_sv C₂.inp F₃ C₂.inp.room (by decide) (by decide) a b c
  refine WP.seq (WP.mono (cmul_ok C₃ (o := 5) (a := 5) (b := 3) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [mk3 3 (by decide) (by decide) (by decide), one₂]; exact hM))
    fun u₄ ⟨C₄, K₄, F₄, L₄, V₄⟩ => ?_)
  have D₄ : sv u₄.mem base len .half 5 = val32 s.mem base (lo len (.slot .wide j)) (cwc len .half) % M := by
    have v := VG.Proof.Dsa.mont_decode (A := sv u₃.mem base len .half 5) (out := sv u₄.mem base len .half 5)
      C₃.coprime B₃ (by rw [V₄, mk3 3 (by decide) (by decide) (by decide), one₂])
    rwa [Nat.mod_eq_of_lt L₄] at v
  have mk4 : ∀ k, 3 ≤ k → k ≤ 8 → k ≠ 5 → sv u₄.mem base len .half k = sv u₂.mem base len .half k :=
    fun k a b c => (mulR_sv C₃.inp F₄ C₃.inp.room (by decide) (by decide) a b c).trans (mk3 k a b c)
  -- `h R mod M`.
  refine WP.seq (WP.mono (cmul_ok C₄ (o := 6) (a := 6) (b := 4) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [mk4 4 (by decide) (by decide) (by decide), R₂]; exact Nat.mod_lt _ (by omega)))
    fun u₅ ⟨C₅, K₅, F₅, L₅, V₅⟩ => ?_)
  have B₅ : sv u₅.mem base len .half 6 =
      val32 s.mem base (lo len (.slot .wide j) + bc len .half) (cwc len .half) * 2 ^ (8 * bc len .half) % M := by
    have v : sv u₅.mem base len .half 6 % M =
        val32 s.mem base (lo len (.slot .wide j) + bc len .half) (cwc len .half) * 2 ^ (8 * bc len .half) % M :=
      VG.Proof.Dsa.mont_scale C₄.coprime
      (by rw [V₅, mk4 6 (by decide) (by decide) (by decide), mk4 4 (by decide) (by decide) (by decide), H₂, R₂, RR])
    rwa [Nat.mod_eq_of_lt L₅] at v
  have mk5 : ∀ k, 3 ≤ k → k ≤ 8 → k ≠ 6 → sv u₅.mem base len .half k = sv u₄.mem base len .half k :=
    fun k a b c => mulR_sv C₄.inp F₅ C₄.inp.room (by decide) (by decide) a b c
  have M₅ : sv u₅.mem base len .half 0 = M := C₅.mod
  -- Their sum modulo `M`.
  refine WP.mono (addMod_ok C₅.inp .half (o := 5) (a := 5) (b := 6) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [M₅, mk5 5 (by decide) (by decide) (by decide)]; exact L₄) (by rw [M₅]; exact L₅))
    fun u ⟨F₆, V₆, K₆⟩ => ?_
  have e1 : lo len (.slot .half 1) = numBase + st len .half := by simp [lo]
  have fit6 : ∀ p ∈ [(lo len (.slot .half 1), bc len .half + 4), (lo len (.slot .half 5), bc len .half)],
      p.1 + p.2 ≤ bytes := by simp; omega
  have C₆ := C₅.keepF K₆ (by decide) (by decide) F₆ fit6 (by simp; omega)
  have keep₆ : ∀ k, 3 ≤ k → k ≤ 8 → k ≠ 5 → sv u.mem base len .half k = sv u₅.mem base len .half k := by
    intro k a b c
    have ek : lo len (.slot .half k) = numBase + k * st len .half := rfl
    have k8' := Nat.mul_le_mul_right (st len .half) b
    simp only [sv]
    refine frameR_val32 F₆ C₅.inp.room nw (by omega) ?_ fit6
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · have := Nat.mul_le_mul_right (st len .half) a; exact .inr (by dsimp only; omega)
    · rcases Nat.lt_or_gt_of_ne c with l | l
      · have := Nat.mul_le_mul_right (st len .half) (show k + 1 ≤ 5 by omega); rw [Nat.succ_mul] at this
        exact .inl (by dsimp only; omega)
      · have := Nat.mul_le_mul_right (st len .half) (show 6 ≤ k by omega); exact .inr (by dsimp only; omega)
  have sp₃ : u₃.gpr .esp = s.gpr .esp := (K₃.1 _ (by decide)).trans sp₂
  have sp₄ : u₄.gpr .esp = s.gpr .esp := (K₄.1 _ (by decide)).trans sp₃
  have sp₅ : u₅.gpr .esp = s.gpr .esp := (K₅.1 _ (by decide)).trans sp₄
  refine ⟨C₆, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [keep₆ 3 (by decide) (by decide) (by decide), mk5 3 (by decide) (by decide) (by decide),
      mk4 3 (by decide) (by decide) (by decide), one₂]
  · rw [keep₆ 4 (by decide) (by decide) (by decide), mk5 4 (by decide) (by decide) (by decide),
      mk4 4 (by decide) (by decide) (by decide), R₂]
  · rw [V₆, M₅, mk5 5 (by decide) (by decide) (by decide), D₄, B₅, split,
      Nat.add_mod (val32 s.mem base (lo len (.slot .wide j)) (cwc len .half)),
      show 32 * cwc len .half = 8 * bc len .half by omega, Nat.mul_comm (2 ^ (8 * bc len .half))]
  · rw [keep₆ 8 (by decide) (by decide) (by decide), mk5 8 (by decide) (by decide) (by decide),
      mk4 8 (by decide) (by decide) (by decide), E₂]
  · have i5 := slot_in h .half (j := 5) (by decide)
    have i6 := slot_in h .half (j := 6) (by decide)
    have i1 := slot1_in h .half
    rw [sp₁] at F₂
    rw [sp₂] at F₃
    rw [sp₃] at F₄
    rw [sp₄] at F₅
    rw [sp₅] at F₆
    have mw : ∀ {k : Nat}, k ≤ 8 → ∀ p ∈ mulR len .half k, ∃ q ∈ [(numBase, 9 * st len .wide)],
        q.1 ≤ p.1 ∧ p.1 + p.2 ≤ q.1 + q.2 := fun hk p hp => by
      simp only [mulR, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact ⟨_, by simp, slot_in h .half hk⟩
      · exact ⟨_, by simp, i1⟩
    refine ((((frameR_widen F₁ ?_).trans (frameR_widen F₂ ?_)).trans (frameR_widen F₃ (mw (by decide)))).trans
      ((frameR_widen F₄ (mw (by decide))).trans (frameR_widen F₅ (mw (by decide))))).trans
      (frameR_widen F₆ ?_)
    · intro p hp; rw [List.mem_singleton.mp hp]; exact ⟨_, by simp, i5⟩
    · intro p hp; rw [List.mem_singleton.mp hp]; exact ⟨_, by simp, i6⟩
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact ⟨_, by simp, i1.1, by have := i1.2; dsimp only at *; omega⟩
      · exact ⟨_, by simp, i5⟩
  · exact ((((K₁.trans K₂).trans (K₃.mono (by decide))).trans (K₄.mono (by decide))).trans
      (K₅.mono (by decide))).trans K₆

/-- A factor's context prepared at width `c`, the power, and its result zero-extended into the wide
slot `o`. -/
theorem powerTail_ok (h : In Ex base bytes len args s) (c : Ctx) {o : Nat} (ho16 : 16 ≤ o) (ho : o ≤ 17)
    {p d y : Nat} (hp : sv s.mem base len c 0 = p) (hy : sv s.mem base len c 5 = y)
    (hd : sv s.mem base len c 8 = d) :
    WP isa (.seq (prepare c) (.seq (windowPower c) (saveResult c o))) s fun u =>
      Frame (frameR base (s.gpr .esp) (stR len o)) s.mem u.mem ∧
      val32 u.mem base (lo len (.slot .wide o)) (2 * cwc len .wide) = y ^ d % safeM p ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u := by
  have ho' : o ≤ 19 := by omega_arith
  refine WP.seq (WP.mono (prepCtx_ok h c) fun u₅ ⟨C₅, one₅, R₅, F₅, K₅⟩ => ?_)
  rw [hp] at C₅ R₅
  have B₅ : sv u₅.mem base len c 5 = y := by
    rw [prepR_sv h c F₅ h.room (j := 5) (by decide) (by decide) (by decide), hy]
  have E₅ : sv u₅.mem base len c 8 = d := by
    rw [prepR_sv h c F₅ h.room (j := 8) (by decide) (by decide) (by decide), hd]
  refine WP.seq (WP.mono (windowPower_ok C₅ one₅ R₅) fun u₆ ⟨C₆, F₆, K₆, Y₆⟩ => ?_)
  rw [B₅, E₅] at Y₆
  refine WP.mono (saveResult_ok C₆.inp c (o := o) (by omega_arith) ho') fun u ⟨O₇, V₇, K₇⟩ => ⟨?_, by rw [V₇, Y₆], ?_⟩
  · have sp₅ : u₅.gpr .esp = s.gpr .esp := K₅.1 _ (by decide)
    rw [sp₅] at F₆
    exact ((stR_widen F₅ (prepR_in h c o)).trans (stR_widen F₆ (pwR_in C₅.inp c o))).trans
      (stR_of_outside h ho' O₇ ⟨(lo len (.slot .wide o), 2 * bc len .wide), by simp, Nat.le_refl _,
        Nat.le_refl _⟩)
  · exact (K₅.trans K₆).trans (K₇.mono (by decide))

/-- The input to the power `d` modulo the factor `p`, at half the width, zero-extended into the wide
slot `o`: the input (`2 Bh` bytes) reduced modulo the factor in the half context, then raised. -/
theorem narrowPower_ok (h : In Ex base bytes len args s) {f e o : Nat} (hf9 : 9 ≤ f) (hf : f ≤ 15) (he9 : 9 ≤ e)
    (he : e ≤ 15) (ho16 : 16 ≤ o) (ho : o ≤ 17) {p d x : Nat}
    (hp : val32 s.mem base (lo len (.slot .wide f)) (cwc len .wide) = p) (hpn : p < 2 ^ (32 * cwc len .half))
    (hd : val32 s.mem base (lo len (.slot .wide e)) (cwc len .wide) = d) (hdn : d < 2 ^ (32 * cwc len .half))
    (hx : val32 s.mem base (lo len (.slot .wide 15)) (2 * cwc len .half) = x) :
    WP isa (narrowPower f e o) s fun u =>
      Frame (frameR base (s.gpr .esp) (stR len o)) s.mem u.mem ∧
      val32 u.mem base (lo len (.slot .wide o)) (2 * cwc len .wide) = x ^ d % safeM p ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u := by
  have Lf := WideLay.mk' h hf9 hf ho16 ho
  have Le := WideLay.mk' h he9 he ho16 ho
  have l9 := Lf.l9
  have f1 := Lf.f1
  have f2 := Lf.f2
  have e1 := Le.f1
  have e2 := Le.f2
  have o1 := Lf.o1
  have l15 := Lf.l15
  have l16 := Lf.l16
  have l18 := Lf.l18
  have est := Lf.est
  have fit := Lf.fit
  have o2 := Lf.o2
  obtain ⟨cwle, cw8, bh, h0, h5, h8, sth, top⟩ := HalfLay.mk' h
  have bw := bc_eq_cwc len .wide
  have hb2 := bc_half_le' len
  have ho' : o ≤ 19 := by omega_arith
  have bl := h.bytes_lt
  have hM := safeM_gt p
  have cb1 : cb len (one .half) = bc len .half := by simp [cb, one]
  have cw1 : cw len (one .half) = cwc len .half := by simp [cw, cwc, cb, one]
  have split : cwc len .half + (cwc len .wide - cwc len .half) = cwc len .wide := by omega_arith
  have P₀ : val32 s.mem base (lo len (.slot .wide f)) (cwc len .half) = p :=
    val32_low (b := cwc len .wide - cwc len .half) (by rw [split, hp]) hpn
  have D₀ : val32 s.mem base (lo len (.slot .wide e)) (cwc len .half) = d :=
    val32_low (b := cwc len .wide - cwc len .half) (by rw [split, hd]) hdn
  -- What the steps before the reduction keep of the input.
  have kx : ∀ {m m' : Mem}, Frame (frameR base (s.gpr .esp) (stR len o)) m m' →
      val32 m' base (lo len (.slot .wide 15)) (2 * cwc len .half) = val32 m base (lo len (.slot .wide 15)) (2 * cwc len .half) :=
    fun F => stR_keep h ho16 ho F h.room (by omega_arith) (by omega_arith) (.inl (by omega_arith))
  unfold narrowPower
  -- The factor and the exponent.
  refine WP.seq (WP.mono (copy_ok h (x := .slot .wide f) (d := .slot .half 0) (one_ok .half)
    (by rw [cb1]; omega_arith) (by rw [cb1, h0]; omega_arith) (by rw [cb1, h0]; exact .inl (by omega_arith)))
    fun u₁ ⟨O₁, V₁, K₁⟩ => ?_)
  rw [cb1, h0] at O₁
  rw [cw1, h0, P₀] at V₁
  have h₁ := h.keep K₁ (by decide) (by decide) (O₁.mono (Nat.zero_le _) (by omega_arith))
  refine WP.seq (WP.mono (copy_ok h₁ (x := .slot .wide e) (d := .slot .half 8) (one_ok .half)
    (by rw [cb1]; omega_arith) (by rw [cb1, h8]; omega_arith) (by rw [cb1, h8]; exact .inl (by omega_arith)))
    fun u₂ ⟨O₂, V₂, K₂⟩ => ?_)
  rw [cb1, h8] at O₂
  rw [cw1, h8, O₁.val32 (d := lo len (.slot .wide e)) (k := cwc len .half) (.inr (by omega_arith)) (by omega_arith),
    D₀] at V₂
  have h₂ := h₁.keep K₂ (by decide) (by decide) (O₂.mono (Nat.zero_le _) (by omega_arith))
  have i0 := slot_in h .half (j := 0) (by decide)
  have i8 := slot_in h .half (j := 8) (by decide)
  rw [h0] at i0
  rw [h8] at i8
  have sp₁ : u₁.gpr .esp = s.gpr .esp := K₁.1 _ (by decide)
  have sp₂ : u₂.gpr .esp = s.gpr .esp := (K₂.1 _ (by decide)).trans sp₁
  have F₂ : Frame (frameR base (s.gpr .esp) (stR len o)) s.mem u₂.mem :=
    (stR_of_outside h ho' O₁ ⟨_, by simp, i0⟩).trans (stR_of_outside h ho' O₂ ⟨_, by simp, i8⟩)
  have M₂ : sv u₂.mem base len .half 0 = p := by
    simp only [sv]; rw [h0, O₂.val32 (d := numBase) (k := cwc len .half) (.inl (by omega_arith)) (by omega_arith), V₁]
  have E₂ : sv u₂.mem base len .half 8 = d := by simp only [sv]; rw [h8, V₂]
  -- The half context of the factor.
  refine WP.seq (WP.mono (prepCtx_ok h₂ .half) fun u₃ ⟨C₃, one₃, R₃, F₃, K₃⟩ => ?_)
  rw [M₂] at C₃ R₃
  have E₃ : sv u₃.mem base len .half 8 = d := by
    rw [prepR_sv h₂ .half F₃ h₂.room (j := 8) (by decide) (by decide) (by decide), E₂]
  rw [sp₂] at F₃
  have F₃' := F₂.trans (stR_widen F₃ (prepR_in h₂ .half o))
  have X₃ : val32 u₃.mem base (lo len (.slot .wide 15)) (2 * cwc len .half) = x := by rw [kx F₃', hx]
  -- The input modulo the factor.
  refine WP.seq (WP.mono (reduceHalf_ok C₃ one₃ R₃ (j := 15) (by decide) (by decide) X₃)
    fun u₄ ⟨C₄, one₄, R₄, B₄, E₄, F₄, K₄⟩ => ?_)
  rw [E₃] at E₄
  have sp₃ : u₃.gpr .esp = s.gpr .esp := (K₃.1 _ (by decide)).trans sp₂
  rw [sp₃] at F₄
  -- The power, and its result into the wide slot `o`.
  refine WP.seq (WP.mono (windowPower_ok C₄ one₄ R₄) fun u₅ ⟨C₅, F₅, K₅, Y₅⟩ => ?_)
  rw [B₄, E₄] at Y₅
  refine WP.mono (saveResult_ok C₅.inp .half (o := o) (by omega_arith) ho') fun u ⟨O₇, V₇, K₇⟩ => ⟨?_, ?_, ?_⟩
  · have sp₄ : u₄.gpr .esp = s.gpr .esp := (K₄.1 _ (by decide)).trans sp₃
    rw [sp₄] at F₅
    exact ((F₃'.trans (stR_widen F₄ fun q hq => by rw [List.mem_singleton.mp hq]; exact ⟨_, by simp, Nat.le_refl _, Nat.le_refl _⟩)).trans (stR_widen F₅ (pwR_in C₄.inp .half o))).trans
      (stR_of_outside h ho' O₇ ⟨(lo len (.slot .wide o), 2 * bc len .wide), by simp, Nat.le_refl _,
        Nat.le_refl _⟩)
  · rw [V₇, Y₅, ← Nat.pow_mod]
  · exact ((((K₁.trans K₂).mono (by decide)).trans K₃).trans ((K₄.mono (by decide)).trans K₅)).trans
      (K₇.mono (by decide))

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
  have ho' : o ≤ 19 := by omega_arith
  have cb1 : cb len (one .wide) = bc len .wide := by simp [cb, one]
  have cw1 : cw len (one .wide) = cwc len .wide := by simp [cw, cwc, cb, one]
  unfold widePower
  refine WP.seq (WP.mono (copy_ok h (x := .slot .wide f) (d := .slot .wide 0) (one_ok .wide)
    (by rw [cb1]; omega_arith) (by rw [cb1, l0]; omega_arith) (by rw [cb1, l0]; exact .inl (by omega_arith)))
    fun u₁ ⟨O₁, V₁, K₁⟩ => ?_)
  rw [cb1, l0] at O₁
  rw [cw1, l0, hp] at V₁
  have h₁ := h.keep K₁ (by decide) (by decide) (O₁.mono (Nat.zero_le _) (by omega_arith))
  refine WP.seq (WP.mono (copy_ok h₁ (x := .slot .wide 15) (d := .slot .wide 5) (one_ok .wide)
    (by rw [cb1, l15]; omega_arith) (by rw [cb1, l5]; omega_arith) (by rw [cb1, l5, l15]; exact .inl (by omega_arith)))
    fun u₂ ⟨O₂, V₂, K₂⟩ => ?_)
  rw [cb1, l5] at O₂
  rw [cw1, l5, O₁.val32 (d := lo len (.slot .wide 15)) (k := cwc len .wide) (.inr (by omega_arith)) (by omega_arith), hx] at V₂
  have h₂ := h₁.keep K₂ (by decide) (by decide) (O₂.mono (Nat.zero_le _) (by omega_arith))
  refine WP.seq (WP.mono (copy_ok h₂ (x := .slot .wide e) (d := .slot .wide 8) (one_ok .wide)
    (by rw [cb1]; omega_arith) (by rw [cb1, l8]; omega_arith) (by rw [cb1, l8]; exact .inl (by omega_arith)))
    fun u₃ ⟨O₃, V₃, K₃⟩ => ?_)
  rw [cb1, l8] at O₃
  rw [cw1, l8, O₂.val32 (d := lo len (.slot .wide e)) (k := cwc len .wide) (.inr (by omega_arith)) (by omega_arith),
    O₁.val32 (d := lo len (.slot .wide e)) (k := cwc len .wide) (.inr (by omega_arith)) (by omega_arith), hd] at V₃
  have h₃ := h₂.keep K₃ (by decide) (by decide) (O₃.mono (Nat.zero_le _) (by omega_arith))
  have M₃ : sv u₃.mem base len .wide 0 = p := by
    simp only [sv]; rw [l0, O₃.val32 (d := numBase) (k := cwc len .wide) (.inl (by omega_arith)) (by omega_arith),
      O₂.val32 (d := numBase) (k := cwc len .wide) (.inl (by omega_arith)) (by omega_arith), V₁]
  have B₃ : sv u₃.mem base len .wide 5 = x := by
    simp only [sv]; rw [l5, O₃.val32 (d := numBase + 5 * st len .wide) (k := cwc len .wide) (.inl (by omega_arith))
      (by omega_arith), V₂]
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

/-- A factor's power, at half the width when its length (the header word at `lenOff`) fits it. -/
theorem power_ok (h : In Ex base bytes len args s) {f e o : Nat} (hf9 : 9 ≤ f) (hf : f ≤ 15) (he9 : 9 ≤ e)
    (he : e ≤ 15) (ho16 : 16 ≤ o) (ho : o ≤ 17) {p d x : Nat}
    (hp : val32 s.mem base (lo len (.slot .wide f)) (cwc len .wide) = p)
    (hd : val32 s.mem base (lo len (.slot .wide e)) (cwc len .wide) = d)
    (hx : val32 s.mem base (lo len (.slot .wide 15)) (2 * cwc len .wide) = x) (hxn : x < 2 ^ (32 * cwc len .wide))
    (fits : w32 s.mem base lenOff ≤ bc len .half → p < 2 ^ (32 * cwc len .half) ∧ d < 2 ^ (32 * cwc len .half)) :
    WP isa (power f e o) s fun u =>
      Frame (frameR base (s.gpr .esp) (stR len o)) s.mem u.mem ∧
      val32 u.mem base (lo len (.slot .wide o)) (2 * cwc len .wide) = x ^ d % safeM p ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u := by
  have hb := bc_le h.upper' .half
  have f0 := h.slot_fit .half (j := 0) (by decide)
  have lo0 : numBase ≤ lo len (.slot .half 0) := by simp [lo]
  unfold power
  simp only [List.cons_append]
  refine WP.seq (wp_movS (readSrc_sc h.scratch (d := lenOff) (by simp only [lenOff, numBase] at *; omega_arith))
    fun u₁ a₁ _ => ?_)
  have h₁ := h.regs a₁.keeps a₁.mem
  refine widthC_ok (k := 0) (c := .half) (r := .edx) h₁.width h.upper' fun u₂ K₂ m₂ e₂ => ?_
  refine wp_addS rfl fun u₃ a₃ _ => wp_cmpC rfl fun u₄ f₄ c₄ => WP.block_nil ?_
  have K₄ : Keeps [.eax, .edx] s u₄ :=
    (((a₁.keeps.mono (by decide)).trans (K₂.mono (by decide))).trans (a₃.keeps.mono (by decide))).trans
      (f₄.keeps _)
  have m₄ : u₄.mem = s.mem := by rw [f₄.mem, a₃.mem, m₂, a₁.mem]
  have h₄ := h.regs K₄ m₄
  have eax : (u₃.gpr .eax).toNat = w32 s.mem base lenOff := by
    rw [a₃.other _ (by decide), K₂.1 _ (by decide), a₁.gpr]
  have edx : (u₃.gpr .edx).toNat = bc len .half + 1 := by
    rw [a₃.gpr, e₂, BitVec.toNat_add, BitVec.toNat_ofNat, show (1 : BitVec 32).toNat = 1 from rfl]
    omega_arith
  rw [eax, edx] at c₄
  have sp : u₄.gpr .esp = s.gpr .esp := K₄.1 _ (by decide)
  have hp' : val32 u₄.mem base (lo len (.slot .wide f)) (cwc len .wide) = p := by rw [m₄, hp]
  have hd' : val32 u₄.mem base (lo len (.slot .wide e)) (cwc len .wide) = d := by rw [m₄, hd]
  have bw2 : bc len .wide ≤ 2 * bc len .half := by simp only [bc]; omega_arith
  have bhw := bc_le_wide len .half
  have cwh := bc_eq_cwc len .half
  have cww := bc_eq_cwc len .wide
  have hx' : val32 u₄.mem base (lo len (.slot .wide 15)) (cwc len .wide) = x :=
    val32_low (b := cwc len .wide) (by rw [m₄, ← Nat.two_mul, hx]) hxn
  have hxh : val32 u₄.mem base (lo len (.slot .wide 15)) (2 * cwc len .half) = x :=
    val32_low (b := 2 * cwc len .wide - 2 * cwc len .half)
      (by rw [m₄, show 2 * cwc len .half + (2 * cwc len .wide - 2 * cwc len .half) = 2 * cwc len .wide by omega_arith, hx])
      (Nat.lt_of_lt_of_le hxn (Nat.pow_le_pow_right (by decide) (by omega_arith)))
  refine WP.ite _ c₄ (fun nar => ?_) (fun _ => ?_)
  · have F := fits (by have := of_decide_eq_true nar; omega_arith)
    refine WP.mono (narrowPower_ok h₄ hf9 hf he9 he ho16 ho hp' F.1 hd' F.2 hxh) fun u ⟨Fu, Vu, Ku⟩ =>
      ⟨by rw [sp, m₄] at Fu; exact Fu, Vu, (K₄.mono (by decide)).trans Ku⟩
  · refine WP.mono (widePower_ok h₄ hf9 hf he9 he ho16 ho hp' hd' hx') fun u ⟨Fu, Vu, Ku⟩ =>
      ⟨by rw [sp, m₄] at Fu; exact Fu, Vu, (K₄.mono (by decide)).trans Ku⟩

end

end VG.Proof.Bignum.X86.CrtRt
