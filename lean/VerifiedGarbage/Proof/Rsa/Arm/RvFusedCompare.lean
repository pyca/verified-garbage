module

public import VerifiedGarbage.Proof.Rsa.Arm.RvSt
public import VerifiedGarbage.Proof.Rsa.Arm.RvMont5
public import VerifiedGarbage.Proof.Rsa.RecoverExp
import VerifiedGarbage.Proof.Rsa.RecoverMath
import VerifiedGarbage.Proof.Bignum.Math

/-! Comparisons against one and minus one in Montgomery representation. -/

@[expose] public section
namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover
open VG.Proof.Rsa.Arm.Keys
open VG.Proof.Rsa (b2n)

theorem montFlag {P : RP} (hn : P.n % 2 = 1 ∧ 1 < P.n) (neg : Bool) {y : Nat} (hy : y < P.n) :
    (if y * Rm P % P.n = (if neg then P.n - Ov P else Ov P) then 1 else 0) =
      b2n (decide (y = if neg then P.n - 1 else 1)) := by
  have prime : Nat.Coprime (Rm P) P.n := VG.Proof.Bignum.coprime_pow2 hn.1 _
  cases neg
  · simp only [Bool.false_eq_true, ↓reduceIte]
    simp only [VG.Proof.Rsa.eq_one_mont prime hn.2 hy rfl]
    by_cases e : y = 1 <;> simp [e, b2n]
  · simp only [↓reduceIte]
    simp only [VG.Proof.Rsa.eq_neg_mont prime hn.2 hy rfl]
    by_cases e : y = P.n - 1 <;> simp [e, b2n]

section
variable {P : RP} {E : State → Prop} {A AW V : State → Nat → Nat} {L LW LS : List Nat}

theorem St.peqMont (hn : P.n % 2 = 1 ∧ 1 < P.n) (neg : Bool) {d a : Nat} {y : State → Nat}
    (cert : Cert (eqS d a (if neg then aNg else aO) aW))
    (ha : a ∈ L) (hb : (if neg then aNg else aO) ∈ L) (hd : SlotOk d)
    (scratch : aW ∉ L) (wide : ∀ j ∈ LW, aW / 2 ≠ j)
    (slots : ∀ e ∈ LS, e + 4 ≤ sT ∨ sT + 4 ≤ e) (different : d ≠ sT)
    (values : ∀ σ, E σ → A σ a = y σ * Rm P % P.n ∧
      A σ (if neg then aNg else aO) = (if neg then P.n - Ov P else Ov P) ∧ y σ < P.n) :
    VP (St P E A L AW LW V LS P.w nArr) (eqS d a (if neg then aNg else aO) aW)
      (St P E A L AW LW (fun σ => upd (V σ) d (b2n (decide (y σ = if neg then P.n - 1 else 1))))
        (d :: LS) P.w nArr) := by
  refine (St.peqS cert ha hb hd scratch wide slots different).mono (fun _ _ h => h)
    fun σ s h => h.mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨hj, rfl⟩) ?_
  intro e he
  refine ⟨he, ?_⟩
  obtain ⟨a, b, bound⟩ := values σ h.1
  by_cases same : e = d
  · subst same
    simp only [upd_self, a, b]
    exact montFlag hn neg bound
  · simp only [upd_ne _ _ same]

end
end VG.Proof.Rsa.Arm.Recover
