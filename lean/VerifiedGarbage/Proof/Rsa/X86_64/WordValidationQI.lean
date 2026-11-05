module

public import VerifiedGarbage.Proof.Rsa.X86_64.WordValidationCtx
public import VerifiedGarbage.Proof.Rsa.X86_64.CrtKeyPhases
import VerifiedGarbage.Proof.Rsa.X86_64.KeySteps

-- separate module: isolate inverse-coefficient arithmetic from the full key-validity composition

/-! # Checking the inverse coefficient with a word remainder -/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.CheckKey
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN aX aAcc aTmp aOne sMask)

section
variable {s t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N : Nat}

theorem crtQInvWord_ok (h : KCtx s t B Z w minv N) {b : Bool} (hm : word t.mem B (8 * sMask) = mask b)
    (hw : 4 ≤ w) (hw' : w < 2 ^ 24)
    (hroom : VG.Proof.Rsa.X86_64.WordValidation.start w + VG.Proof.Rsa.X86_64.WordValidation.span w ≤ Z)
    {pp pq pqi : Addr} {pb qb qib : List Byte} (hpp : word s.mem B (8 * sP) = pp)
    (hpl : word s.mem B (8 * sPlen) = BitVec.ofNat 64 pb.length) (hpq : word s.mem B (8 * sQ) = pq)
    (hql : word s.mem B (8 * sQlen) = BitVec.ofNat 64 qb.length) (hpqi : word s.mem B (8 * sQI) = pqi)
    (srP : Src s B Z pp pb) (srQ : Src s B Z pq qb) (srQI : Src s B Z pqi qib) (hqil : qib.length = pb.length)
    (hp1 : 1 ≤ pb.length) (hpk : pb.length ≤ 8 * w) (hq1 : 1 ≤ qb.length) (hqk : qb.length ≤ 8 * w)
    (hnorm : b = true → 2 ^ (64 * (w / 2) - 1) ≤ Spec.Rsa.os2ip pb ∧ Spec.Rsa.os2ip pb < 2 ^ (64 * (w / 2)))
    (hpqn : b = true → Spec.Rsa.os2ip pb * Spec.Rsa.os2ip qb = N) :
    WP isa WordValidation.qinv t fun t' => KCtx s t' B Z w minv N ∧ ∃ R : Nat,
      (0 < Spec.Rsa.os2ip pb → Spec.Rsa.os2ip qib < Spec.Rsa.os2ip pb →
        R = Spec.Rsa.os2ip qib * Spec.Rsa.os2ip qb % Spec.Rsa.os2ip pb) ∧
      word t'.mem B (8 * sMask) = mask (b && decide (Spec.Rsa.os2ip qib < Spec.Rsa.os2ip pb) && decide (R = 1)) := by
  have hn := h.good.scr.nowrap
  have hZ := h.hZ
  have := h.w2
  simp only [WordValidation.qinv, List.append_assoc]
  refine wsa (by simp [loadNum]) (by simp [loadNum]) (WP.mono (loadK h (j := aM) (by decide) (by decide)
    (by decide) (show sP < 32 by decide) (show sPlen < 32 by decide) (by decide) (by decide) hpp hpl srP hp1 hpk)
    fun t₁ ⟨h₁, v₁, a₁⟩ => ?_)
  refine wsa (by simp [loadNum]) (by simp [ltMask]) (WP.mono (loadK h₁ (j := aX) (by decide) (by decide)
    (by decide) (show sQI < 32 by decide) (show sPlen < 32 by decide) (by decide) (by decide) hpqi
    (by rw [hqil]; exact hpl) srQI (by omega_arith) (by omega_arith)) fun t₂ ⟨h₂, v₂, a₂⟩ => ?_)
  rw [← Arrays.wv_other a₂ (by decide) (by decide) hZ hn] at v₁
  refine wsa (by simp [ltMask]) (by simp [loadNum]) (WP.mono (ltK h₂ (a := aX) (b := aM) (by decide) (by decide))
    fun t₃ ⟨h₃, m₃, o₃⟩ => ?_)
  rw [v₁, v₂, Arrays.mask_eq a₂ hn hZ, Arrays.mask_eq a₁ hn hZ, hm, mask_and'] at m₃
  rw [← Outside.wv_arr o₃ (by decide) hZ hn (by omega_arith)] at v₁ v₂
  refine wsa (by simp [loadNum]) (by simp [mulXR]) (WP.mono (loadK h₃ (j := aR) (by decide) (by decide)
    (by decide) (show sQ < 32 by decide) (show sQlen < 32 by decide) (by decide) (by decide) hpq hql srQ hq1 hqk)
    fun t₄ ⟨h₄, v₄, a₄⟩ => ?_)
  rw [← Arrays.wv_other a₄ (by decide) (by decide) hZ hn] at v₁ v₂
  refine wsa (by simp [mulXR]) (by simp)
    (WP.mono (mulXRK h₄) fun t₅ ⟨h₅, v₅, a₅⟩ => ?_)
  rw [← Arrays.wv_other a₅ (by decide) (by decide) hZ hn] at v₁
  rw [v₂, v₄] at v₅
  refine wsa (by simp) (by simp [eqOne])
    (WP.mono (VG.Proof.Rsa.X86_64.WordValidation.code_ok h₅.good hroom hw hw') fun t₆ ⟨v₆, f₆, k₆⟩ => ?_)
  have h₆ := h₅.wordFrame hroom f₆ k₆
  refine WP.mono (eqOneK h₆) fun t₇ ⟨h₇, m₇, _⟩ =>
    ⟨h₇, Spec.Rsa.os2ip qib * Spec.Rsa.os2ip qb % Spec.Rsa.os2ip pb, fun _ _ => rfl, ?_⟩
  rw [m₇, wordFrame_hdr f₆ (by decide), Arrays.mask_eq a₅ hn hZ,
    Arrays.mask_eq a₄ hn hZ, m₃, mask_and']
  by_cases hb : b = true
  · by_cases hqi : Spec.Rsa.os2ip qib < Spec.Rsa.os2ip pb
    · have fit : Spec.Rsa.os2ip qib * Spec.Rsa.os2ip qb < 2 ^ (64 * w) := by
        have le := Nat.mul_le_mul_right (Spec.Rsa.os2ip qb) (Nat.le_of_lt hqi)
        rw [hpqn hb] at le
        have nlt : N < 2 ^ (64 * w) := by rw [← h₅.n]; exact wv_lt _ _ _ _
        exact Nat.lt_of_le_of_lt le nlt
      have low := VG.Proof.Rsa.X86_64.wv_low_of_lt (m := t₅.mem) (B := B) (e := slot w aAcc)
        (v := w) (w := 2 * w + 2) (by omega_arith) (by rw [v₅]; exact fit)
      have value := v₆ (by rw [v₁]; exact hnorm hb)
      rw [low, v₅, v₁] at value
      rw [value]
    · simp only [decide_eq_false hqi, Bool.and_false, Bool.false_and]
  · have hb' : b = false := by cases b <;> simp_all
    simp only [hb', Bool.false_and]

end

end VG.Proof.Rsa.X86_64.Key
