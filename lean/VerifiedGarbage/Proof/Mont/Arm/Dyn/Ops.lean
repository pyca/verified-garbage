module

public import VerifiedGarbage.Proof.Mont.Arm.Dyn.Mul
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Mont.Arm.Dyn.Csub

/-!
# Runtime-modulus Montgomery arithmetic on 32-bit ARM: the modular addition

`addD M acc o a b` writes `[o] = [a] + [b] mod m` (`addD_ok`), in the layout
of a multiplication (`MulLayD`), whose accumulator holds the sum's digits.
-/

@[expose] public section

namespace VG.Proof.Mont.Arm.Dyn

open VG VG.Arm VG.Impl.Mont VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm
open VG.Proof.X25519.Arm (Rest)

/-- `[o] = [a] + [b] mod m`, for `[a], [b] < m`; `[o]` may be `[a]` or `[b]`. -/
theorem addD_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {M : Mod} {inv acc o a b m : Nat}
    (hn : 0 < M.n) (hL : MulLayD M size inv acc o a b) (hm : val32 s.mem base M.mo (words M) = m) (hm0 : 0 < m)
    (hA : val32 s.mem base a (words M) < m) (hB : val32 s.mem base b (words M) < m) :
    WP isa (addD M acc o a b) s fun t => Ws t base size ∧
      val32 t.mem base o (words M) = (val32 s.mem base a (words M) + val32 s.mem base b (words M)) % m ∧
      Outs base [(o, 4 * words M), (M.tmp, 4 * words M), (acc, 4 * (4 * words M + 2))] s.mem t.mem ∧
      Rest dclob s t := by
  have hnw := hs.nowrap
  obtain ⟨W, hW⟩ : ∃ W, words M = W := ⟨_, rfl⟩
  have hD : digits M = 2 * W := by rw [← hW]; simp only [digits, Impl.Mont.Arm.words]; omega
  obtain ⟨acc_le, a_le, b_le, mo_le, tmp_le, o_le, inv_le, acc16, a16, b16, mo16, tmp16, o16, inv16, sa, sb, smo,
    sinv, stmp, so, tmo, ot⟩ := hL
  simp only [accLen, hD, hW] at acc_le a_le b_le mo_le tmp_le o_le acc16 a16 b16 mo16 tmp16 sa sb smo sinv stmp so tmo ot
  rw [hW] at hm hA hB ⊢
  unfold addD
  refine WP.seq (WP.mono (addDigits_ok hs (M := M) (acc := acc) (a := a) (b := b) hn
    (by rw [hD]; omega_using [acc_le]) (by rw [hW]; exact a_le) (by rw [hW]; exact b_le)
    (by rw [hD]; omega_using [acc16]) (by rw [hW]; exact a16) (by omega_using [b16])
    (by rw [hD, hW]; omega_using [sa]) (by rw [hD, hW]; omega_using [sb])) fun t₁ ⟨w₁, V₁, D₁, O₁, R₁⟩ => ?_)
  simp only [hD, hW] at V₁ D₁ O₁
  have hm₁ : val32 t₁.mem base M.mo W = m := by
    rw [O₁.val32 (by omega_using [smo]) (by omega_using [mo_le, hnw])]; exact hm
  refine WP.mono (csubD_ok w₁ (M := M) (src := acc) (o := o) (m := m) hn
    (by rw [hD]; omega_using [acc_le]) (by rw [hW]; exact o_le) (by rw [hW]; exact tmp_le) (by rw [hW]; exact mo_le)
    (by rw [hD]; omega_using [acc16]) o16 (by rw [hW]; exact tmp16) (by rw [hW]; exact mo16)
    (by rw [hD, hW]; omega_using [stmp]) (by rw [hW]; exact tmo) (by rw [hD, hW]; omega_using [so])
    (by rw [hW]; exact ot) (by rw [hW]; exact hm₁) hm0 (by rw [hD]; exact D₁) (by rw [hD, V₁]; omega_using [hA, hB]))
    fun t ⟨wt, V, O, R⟩ => ⟨wt, ?_, ?_, R₁.trans R⟩
  · rw [hW] at V; rw [V, hD, V₁]
  · rw [hW] at O
    exact (Outs.of_outside (O₁.mono (o' := acc) (n' := 4 * (4 * W + 2)) (Nat.le_refl _) (by omega_using [])) (by simp)).trans (O.mono (by simp))

end VG.Proof.Mont.Arm.Dyn
