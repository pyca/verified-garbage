module

public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Exp
public import VerifiedGarbage.Proof.Mont.X86.ContextMath
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Omega

/-! # The exponentiation of public RSA at a run-time width

From `R² mod M` (number 4), one (number 3) and the input `x < M` (number
1): `R mod M`, the base `x R mod M`, a round per bit of the exponent up to
its top one (`sparseLoop_ok`), and the result out of Montgomery form,
`x^e mod M` in number 2 for the exponent `e` at 128 (`exponentiate_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.PublicRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.PublicRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86

/-- The loop's state after some rounds from `s₀`, towards `target`. -/
structure LoopInv (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) (M target : Nat)
    (s₀ t : State) : Prop where
  env : Env base bytes len args M t
  frame : Frame (Chg base len bytes (s₀.gpr .esp)) s₀.mem t.mem
  value : ∃ y b, val32 t.mem base (numAt len 2) (nw len) = y * 2 ^ (32 * nw len) % M ∧
    val32 t.mem base (numAt len 1) (nw len) = b * 2 ^ (32 * nw len) % M ∧
    (y * b ^ val32 t.mem base 128 2) % M = target
  keeps : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s₀ t
  one : val32 t.mem base (numAt len 3) (nw len) = val32 s₀.mem base (numAt len 3) (nw len)

theorem sparseLoop_ok {s₀ : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {M target : Nat}
    (hbytes : bytes = (args 9).toNat * 8) (I₀ : LoopInv base bytes len args M target s₀ s₀) :
    WP isa (.loop sparseRound .ne) s₀ fun t =>
      LoopInv base bytes len args M target s₀ t ∧ val32 t.mem base 128 2 = 0 := by
  refine WP.loop (M := isa)
    (fun k t => val32 t.mem base 128 2 = k ∧ LoopInv base bytes len args M target s₀ t) ?_
    (val32 s₀.mem base 128 2) s₀ ⟨rfl, I₀⟩
  rintro k t ⟨rfl, I⟩
  obtain ⟨y, b, Y, B, V⟩ := I.value
  refine WP.mono (sparseRound_ok I.env hbytes Y B) fun u ⟨Eu, Fu, Zu, Yu, Bu, Wu, Ku, ou⟩ => ?_
  have next : LoopInv base bytes len args M target s₀ u := by
    refine ⟨Eu, ?_, ⟨_, _, Yu, Bu, ?_⟩, I.keeps.trans Ku, ?_⟩
    · exact I.frame.trans (by rw [← I.keeps.1 _ (by decide)]; exact Fu)
    · rw [Wu, VG.Proof.Mont.X86.Dynamic.exponent_step_value]; exact V
    · rw [ou, I.one]
  by_cases done : val32 t.mem base 128 2 / 2 = 0
  · refine .inl ⟨?_, next, by rw [Wu, done]⟩
    simp only [eval, Zu, done, decide_true, Option.map_some, Bool.not_true]
  · refine .inr ⟨?_, val32 u.mem base 128 2, by rw [Wu]; omega, rfl, next⟩
    simp only [eval, Zu, decide_eq_false done, Option.map_some, Bool.not_false]

theorem exponentiate_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {M : Nat}
    (E : Env base bytes len args M s) (hbase : (args 8).toNat = base.toNat) (hbytes : bytes = (args 9).toNat * 8)
    (hM1 : 1 < M)
    (hT : val32 s.mem base (numAt len 4) (nw len) = 2 ^ (32 * nw len) * 2 ^ (32 * nw len) % M)
    (hO : val32 s.mem base (numAt len 3) (nw len) = 1) :
    WP isa exponentiate s fun t =>
      Env base bytes len args M t ∧ Frame (Chg base len bytes (s.gpr .esp)) s.mem t.mem ∧
      val32 t.mem base (numAt len 2) (nw len) =
        val32 s.mem base (numAt len 1) (nw len) ^ val32 s.mem base 128 2 % M ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have h := E.pi
  have nw' := h.scratch.nowrap
  have dims := h.dimensions
  have wbe := wb_eq len
  have f5 := (h.fits (j := 5) (by decide)).2
  have f1 := (h.fits (j := 1) (by decide)).1
  have f2 := (h.fits (j := 2) (by decide)).1
  have e1 : numAt len 1 = 256 + wb len := by simp only [numAt, numOff] <;> omega
  have e2 : numAt len 2 = 256 + 2 * wb len := by simp only [numAt, numOff] <;> omega
  have e3 : numAt len 3 = 256 + 3 * wb len := by simp only [numAt, numOff] <;> omega
  have e4 : numAt len 4 = 256 + 4 * wb len := by simp only [numAt, numOff] <;> omega
  have e5 : numAt len 5 = 256 + 5 * wb len := by simp only [numAt, numOff] <;> omega
  have n0 : numOff = 256 := rfl
  have hR := E.coprime (32 * nw len)
  generalize hRd : 2 ^ (32 * nw len) = R at hT hR
  -- `R mod M`, from `R²` and one.
  unfold exponentiate
  refine WP.seq (WP.mono (mulRaw_ok E hbytes (o := 2) (a := 4) (b := 3) (by decide) (by decide) (by decide)
    (by decide) (by rw [hO]; exact hM1)) fun u₁ ⟨E₁, C₁, cs₁, F₁, L₁, V₁⟩ => ?_)
  rw [hT, hO, hRd, Nat.mul_one, Nat.mod_mod] at V₁
  have Y₁ : val32 u₁.mem base (numAt len 2) (nw len) = 1 * R % M := by
    rw [Nat.one_mul, ← Nat.mod_eq_of_lt L₁]; exact VG.Proof.Bignum.mont_cancel hR V₁
  have pv : ∀ {d}, (d + 4 * nw len ≤ numAt len 2 ∨ numAt len 2 + wb len ≤ d) → d + 4 * nw len ≤ numAt len 5 →
      val32 u₁.mem base d (nw len) = val32 s.mem base d (nw len) := fun hd h5 =>
    mulFrame_val32 E.room nw' F₁ hd h5 (by omega) f2 f5
  have X₁ := pv (d := numAt len 1) (.inl (by omega)) (by omega)
  have T₁ := pv (d := numAt len 4) (.inr (by omega)) (by omega)
  have O₁ := pv (d := numAt len 3) (.inr (by omega)) (by omega)
  have W₁ : val32 u₁.mem base 128 2 = val32 s.mem base 128 2 := by
    rw [← read_eq_val32, ← read_eq_val32, mulFrame_hdr E.room nw' F₁ (by decide) (by omega) f2 f5]
  -- The base `x R mod M`.
  refine WP.seq (WP.mono (mulRaw_ok E₁ hbytes (o := 1) (a := 1) (b := 4) (by decide) (by decide) (by decide)
    (by decide) (by rw [T₁, hT]; exact Nat.mod_lt _ (by omega))) fun u₂ ⟨E₂, C₂, cs₂, F₂, L₂, V₂⟩ => ?_)
  rw [X₁, T₁, hT, hRd] at V₂
  have X₂ : val32 u₂.mem base (numAt len 1) (nw len) = val32 s.mem base (numAt len 1) (nw len) * R % M := by
    rw [← Nat.mod_eq_of_lt L₂]
    refine VG.Proof.Bignum.mont_cancel hR (V₂.trans ?_)
    rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, Nat.mul_assoc]
  have pv₂ : ∀ {d}, (d + 4 * nw len ≤ numAt len 1 ∨ numAt len 1 + wb len ≤ d) → d + 4 * nw len ≤ numAt len 5 →
      val32 u₂.mem base d (nw len) = val32 u₁.mem base d (nw len) := fun hd h5 =>
    mulFrame_val32 E₁.room nw' F₂ hd h5 (by omega) f1 f5
  have Y₂ := pv₂ (d := numAt len 2) (.inr (by omega)) (by omega)
  have O₂ := pv₂ (d := numAt len 3) (.inr (by omega)) (by omega)
  have W₂ : val32 u₂.mem base 128 2 = val32 s.mem base 128 2 := by
    rw [← W₁, ← read_eq_val32, ← read_eq_val32, mulFrame_hdr E₁.room nw' F₂ (by decide) (by omega) f1 f5]
  -- A round per bit of the exponent.
  have sp₁ : u₁.gpr .esp = s.gpr .esp := cs₁.1 _ (by decide)
  have sp₂ : u₂.gpr .esp = s.gpr .esp := (cs₂.1 _ (by decide)).trans sp₁
  have I₀ : LoopInv base bytes len args M (val32 s.mem base (numAt len 1) (nw len) ^ val32 s.mem base 128 2 % M)
      u₂ u₂ := by
    refine ⟨E₂, Frame.refl _ _, ⟨1, val32 s.mem base (numAt len 1) (nw len), ?_, ?_, ?_⟩, Keeps.refl _ _, rfl⟩
    · rw [Y₂, Y₁, ← hRd]
    · rw [X₂, ← hRd]
    · rw [W₂, Nat.one_mul]
  refine WP.seq (WP.mono (sparseLoop_ok hbytes I₀) fun u₄ ⟨I, z⟩ => ?_)
  obtain ⟨y, b, Y₄, -, V₄⟩ := I.value
  rw [z, Nat.pow_zero, Nat.mul_one] at V₄
  have O₄ : val32 u₄.mem base (numAt len 3) (nw len) = 1 := by rw [I.one, O₂, O₁, hO]
  -- The result out of Montgomery form.
  refine WP.mono (mulRaw_ok I.env hbytes (o := 2) (a := 2) (b := 3) (by decide) (by decide) (by decide)
    (by decide) (by rw [O₄]; exact hM1)) fun t ⟨Et, Ct, cst, _, Lt, Vt⟩ => ?_
  rw [Y₄, O₄, Nat.mul_one, Nat.mod_mod, hRd] at Vt
  have sp₄ : u₄.gpr .esp = s.gpr .esp := by rw [I.keeps.1 _ (by decide), sp₂]
  refine ⟨Et, ?_, ?_, ?_⟩
  · have G₂ : Frame (Chg base len bytes (s.gpr .esp)) u₁.mem u₂.mem := by rw [← sp₁]; exact C₂
    have G₄ : Frame (Chg base len bytes (s.gpr .esp)) u₂.mem u₄.mem := by
      have := I.frame; rwa [sp₂] at this
    have Gt : Frame (Chg base len bytes (s.gpr .esp)) u₄.mem t.mem := by rw [← sp₄]; exact Ct
    exact ((C₁.trans G₂).trans G₄).trans Gt
  · rw [← Nat.mod_eq_of_lt Lt, ← V₄]
    exact VG.Proof.Bignum.mont_cancel hR (by rw [← hRd] at Vt ⊢; exact Vt)
  · exact ((cs₁.mono (by decide)).trans (cs₂.mono (by decide))).trans (I.keeps.trans (cst.mono (by decide)))

end VG.Proof.Bignum.X86.PublicRt
