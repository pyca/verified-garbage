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

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86

section
variable {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}

/-- A preparation keeps slots 5, 6 and 8. -/
theorem prepR_sv (h : In base bytes len args s) (c : Ctx) {sp : BitVec 32} {m m' : Mem}
    (F : Frame (frameR base sp (prepR len c)) m m') (R : CallRoom sp base bytes) {j : Nat}
    (hj5 : 5 ≤ j) (hj : j ≤ 8) (h7 : j ≠ 7) : sv m' base len c j = sv m base len c j := by
  have nw := h.crt.scratch.nowrap
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
theorem low_keep (h : In base bytes len args s) {sp : BitVec 32} {ws : List (Nat × Nat)} {m m' : Mem}
    (F : Frame (frameR base sp ws) m m') (R : CallRoom sp base bytes) (fit : ∀ p ∈ ws, p.1 + p.2 ≤ bytes)
    (hw : ∀ p ∈ ws, p.1 + p.2 ≤ lo len (.slot .wide 9)) {d k : Nat} (hd : lo len (.slot .wide 9) ≤ d)
    (hk : d + 4 * k ≤ bytes) : val32 m' base d k = val32 m base d k :=
  frameR_val32 F R h.crt.scratch.nowrap hk (fun p hp => .inr (by have := hw p hp; omega)) fit

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

theorem WideLay.mk' (h : In base bytes len args s) {f o : Nat} (hf9 : 9 ≤ f) (hf : f ≤ 15) (ho16 : 16 ≤ o)
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
theorem reduce_ok (h : In base bytes len args s) {f o : Nat} (hf9 : 9 ≤ f) (hf : f ≤ 15) (ho16 : 16 ≤ o)
    (ho : o ≤ 17) {p x : Nat} (hp : val32 s.mem base (lo len (.slot .wide f)) (cwc len .wide) = p)
    (hx : val32 s.mem base (lo len (.slot .wide 15)) (cwc len .wide) = x) {P : Prog isa} {Q : State → Prop}
    (k : ∀ u, In base bytes len args u → Frame (frameR base (s.gpr .esp) (stR len o)) s.mem u.mem →
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
    rw [prepR_sv h₂ .wide F₃ h₂.crt.room (j := 5) (by decide) (by decide) (by decide)]
    simp only [sv]; rw [l5]; exact V₂
  -- `x R mod M`, then `x mod M`.
  refine WP.seq (WP.mono (cmul_ok C₃ (o := 5) (a := 5) (b := 4) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [R₃]; exact Nat.mod_lt _ (by omega))) fun u₄ ⟨C₄, K₄, F₄, L₄, V₄⟩ => ?_)
  have B₄ : sv u₄.mem base len .wide 5 = x * 2 ^ (8 * bc len .wide) % safeM p := by
    have v := VG.Proof.Dsa.mont_scale C₃.coprime (out := sv u₄.mem base len .wide 5) (input := x)
      (c := 2 ^ (8 * bc len .wide)) (by rw [V₄, X₃, R₃, RR])
    rwa [Nat.mod_eq_of_lt L₄] at v
  have one₄ : sv u₄.mem base len .wide 3 = 1 := by
    rw [mulR_sv C₃.inp F₄ C₃.inp.crt.room (o := 5) (j := 3) (by decide) (by decide) (by decide) (by decide)
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

end

end VG.Proof.Bignum.X86.CrtRt
