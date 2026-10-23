module

public import VerifiedGarbage.Proof.Rsa.X86.KcStart
public import VerifiedGarbage.Proof.Rsa.KeyCheckMath
public import VerifiedGarbage.Proof.Rsa.X86.KeyRt.MulMod
import VerifiedGarbage.Proof.Rsa.X86.KcOps
import VerifiedGarbage.Proof.Rsa.X86.InvParts

/-! # The checks of an RSA key on i686: the checks after the division of `n` by `p`

`crtChecks_ok`: from the quotient `X₁` and remainder `X₂` of `n / p`, the
mask is and'ed with `n / p = q`, `n mod p = 0`, `dP < p - 1`, `e dP ≡ 1`,
`dQ < q - 1`, `e dQ ≡ 1`, `qInv < p` and `q qInv ≡ 1` (`crtBits`), the
products known when their factor is below their modulus; `p - 1` and `q - 1`
are left in `aM1` and `aM2`.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.KeyCheck
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.KeyCheck VG.Impl.Rsa.X86.KeyCheckRt
open VG.Proof.Rsa.X86.Keys
open VG.Proof.Rsa.X86.KeyRt (MulIdx)

/-- The arrays after the division of `n` by `p`. -/
abbrev aDivN (v : Vals) (X₁ X₂ : Nat) : Nat → Nat := upd (upd (upd (vals v) aOne 1) aVQ X₁) aVR X₂

/-- The arrays the checks of `d` use. -/
abbrev aFin (v : Vals) : Nat → Nat := upd (upd (vals v) aM1 (2 * (v.p / 2))) aM2 (2 * (v.q / 2))
abbrev liveFin : List Nat := [aZ, aN, aD, aDP, aDQ, aM1, aM2]

theorem mulIdx_m1 : MulIdx nArr aZ aY aX aA aM1 aT := by decide
theorem mulIdx_m2 : MulIdx nArr aZ aY aX aA aM2 aT := by decide
theorem mulIdx_p : MulIdx nArr aZ aY aX aA aP aT := by decide

theorem crtChecks_ok {g : Geo} {s0 s : State} {v : Vals} {X₁ X₂ : Nat}
    (h : Stg g s0 (aDivN v X₁ X₂) (aVR :: aVQ :: live0) (decide (v.p % 2 = 1)) s)
    (hq : ∃ a, 1 ≤ a ∧ a ≤ 1024 ∧ v.q < 2 ^ (8 * a) ∧
      VG.Proof.Bignum.X86.CallArgument s0 g.B g.Z (qLenArg g.full) (BitVec.ofNat 32 a)) :
    WP isa (crtChecks g.full) s fun t => ∃ R₁ R₂ R₃ : Nat,
      (v.dP < 2 * (v.p / 2) → 2 * (2 * (v.p / 2)) ≤ 2 ^ (32 * g.w) →
        R₁ = v.e % 2 ^ 33 * v.dP % (2 * (v.p / 2))) ∧
      (v.dQ < 2 * (v.q / 2) → 2 * (2 * (v.q / 2)) ≤ 2 ^ (32 * g.w) →
        R₂ = v.e % 2 ^ 33 * v.dQ % (2 * (v.q / 2))) ∧
      (v.qI < v.p → 2 * v.p ≤ 2 ^ (32 * g.w) → R₃ = v.q * v.qI % v.p) ∧
      Stg g s0 (aFin v) liveFin
        (VG.Proof.Rsa.crtBits v.p v.q v.dP v.dQ v.qI X₁ X₂ R₁ R₂ R₃) t := by
  obtain ⟨qa, qa1, qa2, qlt, qarg⟩ := hq
  have wpos := h.ws.ws.wpos
  have wle := h.ws.ws.wle
  unfold crtChecks
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  rw [wp_seqs_append (by simp [eqA]) (by simp [eqA])]
  refine WP.mono (h.eqA_ok (a := aVQ) (b := aQ) (by decide) (by decide) (by decide)) fun t1 h1 => ?_
  rw [wp_seqs_append (by simp [eqA]) (by simp)]
  refine WP.mono (h1.eqA_ok (a := aVR) (b := aZ) (by decide) (by decide) (by decide)) fun t2 h2 => ?_
  rw [wp_seqs_cons (by simp)]
  refine WP.mono (h2.copy_ok (o := aM1) (a := aP) (by decide) (by decide) (by decide)) fun t3 h3 => ?_
  rw [wp_seqs_cons (by simp)]
  refine WP.mono (h3.clrLow_ok (j := aM1) (by decide)) fun t4 h4 => ?_
  rw [wp_seqs_cons (by simp)]
  refine WP.mono (h4.copy_ok (o := aM2) (a := aQ) (by decide) (by decide) (by decide)) fun t5 h5 => ?_
  rw [wp_seqs_cons (by simp [ltA])]
  refine WP.mono (h5.clrLow_ok (j := aM2) (by decide)) fun t6 h6 => ?_
  -- `dP`.
  rw [wp_seqs_append (by simp [ltA]) (by simp [mulA])]
  refine WP.mono (h6.ltA_ok (a := aDP) (b := aM1) (by decide) (by decide) (by decide)) fun t7 h7 => ?_
  rw [wp_seqs_append (by simp [mulA]) (by simp [eqA])]
  refine WP.mono (h7.mulA_ok (y := aE) (x := aDP) (m := aM1) (k := 33) (by decide) (by decide) (by decide)
    (by decide) rfl mulIdx_m1 (by decide) (by decide) (by decide) (by decide) (by decide) fun u _ _ _ => cnt33_ok u)
    fun t8 ⟨R₁, hR₁, h8⟩ => ?_
  rw [wp_seqs_append (by simp [eqA]) (by simp [ltA])]
  refine WP.mono (h8.eqA_ok (a := aA) (b := aOne) (by decide) (by decide) (by decide)) fun t9 h9 => ?_
  -- `dQ`.
  rw [wp_seqs_append (by simp [ltA]) (by simp [mulA])]
  refine WP.mono (h9.ltA_ok (a := aDQ) (b := aM2) (by decide) (by decide) (by decide)) fun t10 h10 => ?_
  rw [wp_seqs_append (by simp [mulA]) (by simp [eqA])]
  refine WP.mono (h10.mulA_ok (y := aE) (x := aDQ) (m := aM2) (k := 33) (by decide) (by decide) (by decide)
    (by decide) rfl mulIdx_m2 (by decide) (by decide) (by decide) (by decide) (by decide) fun u _ _ _ => cnt33_ok u)
    fun t11 ⟨R₂, hR₂, h11⟩ => ?_
  rw [wp_seqs_append (by simp [eqA]) (by simp [ltA])]
  refine WP.mono (h11.eqA_ok (a := aA) (b := aOne) (by decide) (by decide) (by decide)) fun t12 h12 => ?_
  -- `qInv`.
  rw [wp_seqs_append (by simp [ltA]) (by simp [mulA])]
  refine WP.mono (h12.ltA_ok (a := aQI) (b := aP) (by decide) (by decide) (by decide)) fun t13 h13 => ?_
  rw [wp_seqs_append (by simp [mulA]) (by simp [eqA])]
  refine WP.mono (h13.mulA_ok (y := aQ) (x := aQI) (m := aP) (k := 8 * qa) (by decide) (by decide)
    (by decide) (by decide) rfl mulIdx_p (by decide) (by decide) (by decide) (by omega) (by omega)
    fun u _ K O => qBits_ok (qarg.keep K (by decide) O))
    fun t14 ⟨R₃, hR₃, h14⟩ => ?_
  refine WP.mono (h14.eqA_ok (a := aA) (b := aOne) (by decide) (by decide) (by decide)) fun t h15 => ?_
  refine ⟨R₁, R₂, R₃, hR₁, hR₂, fun hlt hM => ?_, (h15.sub (live' := liveFin) (by decide)).congr rfl⟩
  refine (hR₃ hlt hM).trans ?_
  show v.q % 2 ^ (8 * qa) * v.qI % v.p = _
  rw [Nat.mod_eq_of_lt qlt]

end VG.Proof.Rsa.X86.KeyCheck
