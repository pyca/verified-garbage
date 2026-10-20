module

public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Exponentiate
import Mathlib.Data.Int.GCD
import VerifiedGarbage.Proof.Framework.Omega

/-! # The exponentiation from any `R²` below the modulus

`exponentiate` from any number 4 below `M` (`exponentiate_any_ok`): it ends,
in `Env`, changing only `Chg`. Its value is `exponentiate_ok`'s when number 4
is `R² mod M`, and unspecified otherwise, as when `pre` holds the values of
no modulus.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.PublicRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.PublicRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86

/-- `y` with `y R ≡ X`, for `R` invertible modulo `M > 1`. -/
theorem exists_mont {R M : Nat} (hR : Nat.Coprime R M) (hM : 1 < M) (X : Nat) :
    ∃ y, X % M = y * R % M := by
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hR hM
  refine ⟨X * m, ?_⟩
  rw [Nat.mul_assoc, Nat.mul_mod, Nat.mul_comm m R, hm, Nat.mul_one, Nat.mod_mod]

theorem exponentiate_any_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {M : Nat}
    (E : Env base bytes len args M s) (hbase : (args 8).toNat = base.toNat) (hbytes : bytes = (args 9).toNat * 8)
    (hM1 : 1 < M) (hT : val32 s.mem base (numAt len 4) (nw len) < M)
    (hO : val32 s.mem base (numAt len 3) (nw len) = 1) :
    WP isa exponentiate s fun t =>
      Env base bytes len args M t ∧ Frame (Chg base len bytes (s.gpr .esp)) s.mem t.mem ∧
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
  have hR := E.coprime (32 * nw len)
  unfold exponentiate
  refine WP.seq (WP.mono (mulRaw_ok E hbytes (o := 2) (a := 4) (b := 3) (by decide) (by decide) (by decide)
    (by decide) (by rw [hO]; exact hM1)) fun u₁ ⟨E₁, C₁, cs₁, F₁, L₁, _⟩ => ?_)
  have pv : ∀ {d}, (d + 4 * nw len ≤ numAt len 2 ∨ numAt len 2 + wb len ≤ d) → d + 4 * nw len ≤ numAt len 5 →
      val32 u₁.mem base d (nw len) = val32 s.mem base d (nw len) := fun hd h5 =>
    mulFrame_val32 E.room nw' F₁ hd h5 (by omega) f2 f5
  have T₁ := pv (d := numAt len 4) (.inr (by omega)) (by omega)
  have O₁ := pv (d := numAt len 3) (.inr (by omega)) (by omega)
  refine WP.seq (WP.mono (mulRaw_ok E₁ hbytes (o := 1) (a := 1) (b := 4) (by decide) (by decide) (by decide)
    (by decide) (by rw [T₁]; exact hT)) fun u₂ ⟨E₂, C₂, cs₂, F₂, L₂, _⟩ => ?_)
  have pv₂ : ∀ {d}, (d + 4 * nw len ≤ numAt len 1 ∨ numAt len 1 + wb len ≤ d) → d + 4 * nw len ≤ numAt len 5 →
      val32 u₂.mem base d (nw len) = val32 u₁.mem base d (nw len) := fun hd h5 =>
    mulFrame_val32 E₁.room nw' F₂ hd h5 (by omega) f1 f5
  have Y₂ := pv₂ (d := numAt len 2) (.inr (by omega)) (by omega)
  have O₂ := pv₂ (d := numAt len 3) (.inr (by omega)) (by omega)
  refine WP.seq (wp_movS rfl fun u₃ e₃ _ => WP.block_nil ?_)
  have sp₁ : u₁.gpr .esp = s.gpr .esp := cs₁.1 _ (by decide)
  have sp₂ : u₂.gpr .esp = s.gpr .esp := (cs₂.1 _ (by decide)).trans sp₁
  obtain ⟨y, hy⟩ := exists_mont hR hM1 (val32 u₂.mem base (numAt len 2) (nw len))
  obtain ⟨b, hb⟩ := exists_mont hR hM1 (val32 u₂.mem base (numAt len 1) (nw len))
  rw [Nat.mod_eq_of_lt (by rw [Y₂]; exact L₁)] at hy
  rw [Nat.mod_eq_of_lt L₂] at hb
  have I₀ : LoopInv base bytes len args M ((y * b ^ val32 u₃.mem base 128 2) % M) 0 u₃ u₃ :=
    ⟨E₂.keep e₃.keeps (by decide) (by decide) (by rw [e₃.mem]; exact Frame.refl _ _), Frame.refl _ _,
      e₃.gpr, val32_lt _ _ _ _, ⟨y, b, by rw [e₃.mem]; exact hy, by rw [e₃.mem]; exact hb, rfl⟩,
      Keeps.refl _ _, rfl⟩
  refine WP.seq (WP.mono (expLoop_ok hbase hbytes I₀) fun u₄ I => ?_)
  have O₄ : val32 u₄.mem base (numAt len 3) (nw len) = 1 := by rw [I.one, e₃.mem, O₂, O₁, hO]
  refine WP.mono (mulRaw_ok I.env hbytes (o := 2) (a := 2) (b := 3) (by decide) (by decide) (by decide)
    (by decide) (by rw [O₄]; exact hM1)) fun t ⟨Et, Ct, cst, _, _, _⟩ => ?_
  have sp₄ : u₄.gpr .esp = s.gpr .esp := by rw [I.keeps.1 _ (by decide), e₃.other _ (by decide), sp₂]
  refine ⟨Et, ?_, ?_⟩
  · have G₂ : Frame (Chg base len bytes (s.gpr .esp)) u₁.mem u₂.mem := by rw [← sp₁]; exact C₂
    have G₄ : Frame (Chg base len bytes (s.gpr .esp)) u₂.mem u₄.mem := by
      have := I.frame; rwa [e₃.mem, e₃.other _ (by decide), sp₂] at this
    have Gt : Frame (Chg base len bytes (s.gpr .esp)) u₄.mem t.mem := by rw [← sp₄]; exact Ct
    exact ((C₁.trans G₂).trans G₄).trans Gt
  · exact (((cs₁.mono (by decide)).trans (cs₂.mono (by decide))).trans (e₃.keeps.mono (by decide))).trans
      (I.keeps.trans (cst.mono (by decide)))

/-- `exponentiate_ok`'s value when number 4 is `R² mod M`, from any number 4 below `M`. -/
theorem exponentiate_cond_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {M : Nat}
    (E : Env base bytes len args M s) (hbase : (args 8).toNat = base.toNat) (hbytes : bytes = (args 9).toNat * 8)
    (hM1 : 1 < M) (hT : val32 s.mem base (numAt len 4) (nw len) < M)
    (hO : val32 s.mem base (numAt len 3) (nw len) = 1) :
    WP isa exponentiate s fun t =>
      Env base bytes len args M t ∧ Frame (Chg base len bytes (s.gpr .esp)) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t ∧
      (val32 s.mem base (numAt len 4) (nw len) = 2 ^ (32 * nw len) * 2 ^ (32 * nw len) % M →
        val32 t.mem base (numAt len 2) (nw len) =
          val32 s.mem base (numAt len 1) (nw len) ^ val32 s.mem base 128 2 % M) := by
  by_cases hx : val32 s.mem base (numAt len 4) (nw len) = 2 ^ (32 * nw len) * 2 ^ (32 * nw len) % M
  · exact WP.mono (exponentiate_ok E hbase hbytes hM1 hx hO) fun _ ⟨a, b, c, d⟩ => ⟨a, b, d, fun _ => c⟩
  · exact WP.mono (exponentiate_any_ok E hbase hbytes hM1 hT hO) fun _ ⟨a, b, d⟩ =>
      ⟨a, b, d, fun h => absurd h hx⟩

end VG.Proof.Bignum.X86.PublicRt
