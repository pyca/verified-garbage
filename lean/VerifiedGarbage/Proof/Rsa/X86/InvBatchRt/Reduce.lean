module

public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Red
public import VerifiedGarbage.Proof.Divstep.Alg32Def
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
import VerifiedGarbage.Proof.Divstep.Red32
import VerifiedGarbage.Proof.Weierstrass.X86.InvRedMath
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Weierstrass.X86.InvRead

/-! # The reduction of a coefficient row at a run-time width

`reduce_ok`: `[out] = mred p iv t` for the signed `t` at `[11]`, with the inverse word `iv` at the
header's `win + 28`.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.InvBatchRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Impl.Rsa.X86.InvBatchRt
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Rsa.X86.KeyRt VG.Proof.Weierstrass
open VG.Proof.Weierstrass.X86.Inv (wordClob)

variable {L : Lay} {B : Addr} {Z len N : Nat}

theorem rv_arr (w j b : Nat) : rv w { arr := j, byte := b } = 160 + j * (4 * w + 8) + b := by
  simp only [rv, VG.Impl.Rsa.X86.InvBatchRt.offset]; omega

/-- `reduce (a j)`: `[a j] = mred p iv t` for the signed `t` at `[11]` (`n + 1` words), the
modulus `p` at `[2]` and its inverse `iv` at `win + 28`. -/
theorem reduce_ok {s : State} (h : Bx L s B Z len N) {j : Nat} (hj : 13 ≤ j) (hj' : j < 16)
    {p : Nat} {t : Int} (hp : 0 < p) (hm : val32 s.mem B (rv (kw len) mo) (nw len) = p)
    (hinv : (p * w32 s.mem B (win + 28) + 1) % 2 ^ 32 = 0) (ht : |t| ≤ 2 ^ 31 * p)
    (hval : (val32 s.mem B (rv (kw len) (a 11)) (nw len + 1) : Int) % 2 ^ (32 * (nw len + 1)) =
      t % 2 ^ (32 * (nw len + 1))) :
    WP isa (reduce L (a j)) s fun z =>
      Bx L z B Z len N ∧
      Unch B [(rv (kw len) (a 11), 4 * (nw len + 2)), (rv (kw len) tmp, 4 * (nw len + 1)), (signSlot, 4),
        (rv (kw len) (a j), 4 * nw len)] s.mem z.mem ∧
      Keeps wordClob s z ∧
      (val32 z.mem B (rv (kw len) (a j)) (nw len) : Int) = Divstep.W32.mred p (w32 s.mem B (win + 28)) t := by
  have hn := h.nowrap
  have hf := h.fits
  have ke := kw_eq len
  have e48 : signSlot = 48 := rfl
  have e16 : win = 16 := rfl
  simp only [VG.Impl.Rsa.X86.InvBatchRt.offset] at hf
  have r11 : rv (kw len) (a 11) = 160 + 11 * (8 * nw len + 8) := by
    have := rv_arr (kw len) 11 0; simp only [a]; omega
  have r11' : rv (kw len) { arr := 11, byte := 4 } = 160 + 11 * (8 * nw len + 8) + 4 := by
    have := rv_arr (kw len) 11 4; omega
  have r12 : rv (kw len) tmp = 160 + 12 * (8 * nw len + 8) := by
    have := rv_arr (kw len) 12 0; simp only [tmp]; omega
  have r2 : rv (kw len) mo = 160 + 2 * (8 * nw len + 8) := by
    have := rv_arr (kw len) 2 0; simp only [mo]; omega
  have rj : rv (kw len) (a j) = 160 + j * (8 * nw len + 8) := by
    have := rv_arr (kw len) j 0
    rw [show 4 * kw len + 8 = 8 * nw len + 8 by omega] at this; simp only [a]; omega
  have hjZ : 160 + j * (8 * nw len + 8) + (8 * nw len + 8) ≤ Z := by
    have : (j + 1) * (8 * nw len + 8) ≤ 16 * (8 * nw len + 8) := Nat.mul_le_mul_right _ (by omega)
    rw [ke] at hf; rw [Nat.succ_mul] at this; omega
  have h11 : 11 * (8 * nw len + 8) + (8 * nw len + 8) ≤ j * (8 * nw len + 8) := by
    rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
  have h12 : 12 * (8 * nw len + 8) + (8 * nw len + 8) ≤ j * (8 * nw len + 8) := by
    rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
  unfold reduce
  -- The numerator.
  refine WP.seq (WP.mono (redSum_ok h (acc := a 11) rfl rfl (by omega) (by omega) (by omega))
    fun s₁ ⟨H₁, U₁, K₁, V₁⟩ => ?_)
  have ra4 : rv (kw len) { arr := 11, byte := 4 } = rv (kw len) (a 11) + 4 := by omega
  -- What it keeps.
  have unch₁ : ∀ d k, (d + 4 * k ≤ rv (kw len) (a 11) ∨ rv (kw len) (a 11) + 4 * (nw len + 2) ≤ d) →
      d + 4 * k ≤ 48 ∨ 52 ≤ d → d + 4 * k ≤ Z → val32 s₁.mem B d k = val32 s.mem B d k := fun d k h1 h2 h3 =>
    Outs.val32 U₁ (by
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> simp only <;> omega) (by omega)
  have M₁ : val32 s₁.mem B (rv (kw len) mo) (nw len) = p := by rw [unch₁ _ _ (by omega) (by omega) (by omega), hm]
  -- The conditional addition.
  refine WP.seq (WP.mono (addIfNeg_ok H₁ (acc := { arr := 11, byte := 4 }) rfl (by omega) (by omega) (by omega)
    (by omega) (by omega)) fun s₂ ⟨H₂, U₂, K₂, V₂⟩ => ?_)
  rw [ra4] at U₂ V₂
  rw [M₁] at V₂
  have M₂ : val32 s₂.mem B (rv (kw len) mo) (nw len) = p := by
    rw [Outs.val32 U₂ (by
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> simp only <;> omega) (by omega), M₁]
  -- The arithmetic of `mred`.
  have P : 2 ^ (32 * (nw len + 1)) = 2 ^ (32 * nw len) * 2 ^ 32 := by
    rw [pow32_succ, Nat.mul_comm]
  have E : val32 s₁.mem B (rv (kw len) (a 11)) (nw len + 2) =
      (val32 s.mem B (rv (kw len) (a 11)) (nw len + 1) + 2 ^ (32 * nw len) * 2 ^ 32 *
        (if 2 ^ (32 * nw len) * 2 ^ 31 ≤ val32 s.mem B (rv (kw len) (a 11)) (nw len + 1) then 2 ^ 32 - 1 else 0) +
        (w32 s.mem B (rv (kw len) (a 11)) * w32 s.mem B (win + 28) % 2 ^ 32) * p) %
        (2 ^ (32 * nw len) * 2 ^ 32 * 2 ^ 32) := by
    rw [V₁, hm]
    simp only [VG.Proof.Weierstrass.X86.Inv.sign32]
    have P' : 2 ^ (32 * (nw len + 2)) = (2 ^ (32 * nw len) * 2 ^ 32) * 2 ^ 32 := by
      rw [show nw len + 2 = (nw len + 1) + 1 by omega, pow32_succ, P, Nat.mul_comm]
    rw [P', P, Nat.add_right_comm]
  have F : val32 s₂.mem B (rv (kw len) (a 11) + 4) (nw len + 1) =
      (val32 s₁.mem B (rv (kw len) (a 11) + 4) (nw len + 1) +
        if 2 ^ (32 * nw len) * 2 ^ 31 ≤ val32 s₁.mem B (rv (kw len) (a 11) + 4) (nw len + 1) then p else 0) %
        (2 ^ (32 * nw len) * 2 ^ 32) := by
    rw [V₂]
    simp only [VG.Proof.Weierstrass.X86.Inv.sign32, P]
  have H := Divstep.W32.mred_first_nat
    (A := 2 ^ (32 * nw len)) (B := 2 ^ 32) (H := 2 ^ 31) (p := p) (m := w32 s.mem B (win + 28))
    (W := val32 s.mem B (rv (kw len) (a 11)) (nw len + 1))
    (k := w32 s.mem B (rv (kw len) (a 11)) * w32 s.mem B (win + 28) % 2 ^ 32)
    (E := val32 s₁.mem B (rv (kw len) (a 11)) (nw len + 2))
    (R := val32 s₁.mem B (rv (kw len) (a 11) + 4) (nw len + 1))
    (R₁ := val32 s₂.mem B (rv (kw len) (a 11) + 4) (nw len + 1)) (t := t)
    rfl rfl (Nat.two_pow_pos _) hp (by rw [← hm]; exact val32_lt _ _ _ _) hinv ht
    (by rw [← P]; exact val32_lt _ _ _ _)
    (by rw [← P]; exact_mod_cast hval)
    (by rw [← VG.Proof.Weierstrass.X86.Inv.low32]) E (VG.Proof.Weierstrass.X86.Inv.high32 _ _ _ _) F
  rcases H with ⟨bound, result⟩
  -- The conditional subtraction.
  refine WP.mono (csub_ok H₂ (src := { arr := 11, byte := 4 }) (o := a j) rfl rfl (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (fun _ => by omega) (by omega) M₂ (by rw [ra4]; exact bound))
    fun z ⟨H₃, U₃, V₃, K₃⟩ => ⟨H₃, ?_, ((K₁.mono (by decide)).trans (K₂.mono (by decide))).trans (K₃.mono (by decide)), ?_⟩
  · intro x hx
    have h1 := hx (rv (kw len) (a 11), 4 * (nw len + 2)) (by simp)
    have h2 := hx (rv (kw len) tmp, 4 * (nw len + 1)) (by simp)
    have h3 := hx (signSlot, 4) (by simp)
    have h4 := hx (rv (kw len) (a j), 4 * nw len) (by simp)
    rw [U₃ x (by
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> simp only <;> omega),
      U₂ x (by
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> simp only <;> omega),
      U₁ x (by
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> simp only <;> omega)]
  · rw [V₃, ra4]
    exact result

end VG.Proof.Rsa.X86.InvBatchRt
