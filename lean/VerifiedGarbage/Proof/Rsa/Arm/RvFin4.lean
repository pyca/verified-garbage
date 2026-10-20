module

public import VerifiedGarbage.Proof.Rsa.Arm.RvFin3
import VerifiedGarbage.Proof.Rsa.Arm.RvTaint4
import VerifiedGarbage.Proof.Rsa.Arm.RvSlots
import VerifiedGarbage.Proof.Rsa.Arm.RvMmul2
import VerifiedGarbage.Proof.Rsa.Arm.RvCtx

/-! # `vg_rsa_recover_primes` on ARMv7: the factors ordered (`order_vp`) -/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa (b2n)

/-- The larger and the smaller factor. -/
abbrev bigF (P : RP) (σ : State) : Nat := max (pF P σ) (qF P σ)
abbrev smallF (P : RP) (σ : State) : Nat := min (pF P σ) (qF P σ)

/-- After the factors are ordered. -/
abbrev Fo (P : RP) (E : State → Prop) : State → State → Prop :=
  Sk P E (fun σ => upd (upd (fun _ => 0) 5 (bigF P σ)) 6 (smallF P σ)) [6, 5] (fun _ _ => 0) []
    (VM P) [sMask] P.w nArr

section
variable {P : RP} {E : State → Prop} {A : State → Nat → Nat} {L : List Nat} {AW : State → Nat → Nat}
  {LW : List Nat} {V : State → Nat → Nat} {LS : List Nat}

/-- `sLt := r11`. -/
theorem Sk.pltStore {x : State → Nat} :
    VP (fun σ s => Sk P E A L AW LW V LS P.w nArr σ s ∧ (s.gpr .r11).toNat = x σ) (.block [.str .r11 .r8 sLt])
      (Sk P E A L AW LW (fun σ => upd (V σ) sLt (x σ)) (sLt :: LS) P.w nArr) := by
  refine VP.ctx ltStore_taint (fun _ _ h => h.1.2.2) fun σ s ⟨⟨e, h, hw⟩, r11⟩ => ?_
  refine h.strSlot hw (d := sLt) (r := .r11) (by decide) fun t ht hwt _ _ => WP.block_nil ⟨e, ?_, hwt⟩
  rw [r11] at ht; exact ht

end

section
variable {P : RP}

theorem order_vp (hn0 : 0 < P.n) (nl : P.n < 2 ^ (32 * P.w)) {E : State → Prop} :
    VP (Fq P E) order (Fo P E) := by
  simp only [order, seqs]
  refine VP.seq (G := Sk P E (fun σ => upd (upd (upd (fun _ => 0) aN P.n) 1 (pF P σ)) aQ (qF P σ)) [aQ, 1, aN]
    (fun _ _ => 0) [] (VM P) [sMask] P.w nArr) (VP.taint [.r8] ctxw_taint (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.r8, h₂.2.r8])
    fun σ s ⟨e, h⟩ => WP.mono (ctxw_ok h.bs h.r8 h.cnt) fun t ⟨ht, r, m⟩ => ⟨e, h.of_rest r m (by decide), ht⟩) ?_
  have hp : ∀ σ, pF P σ ≤ P.n := fun σ => Nat.gcd_le_right _ hn0
  refine VP.seq (Sk.psub3 lt_taint (o := aW) (a := 1) (b := aQ) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) fun σ _ => ⟨?_, ?_⟩) ?_
  · have : upd (upd (upd (fun _ => 0) aN P.n) 1 (pF P σ)) aQ (qF P σ) 1 = pF P σ := by simp [upd, aQ]
    rw [this]; exact Nat.lt_of_le_of_lt (hp σ) nl
  · have : upd (upd (upd (fun _ => 0) aN P.n) 1 (pF P σ)) aQ (qF P σ) aQ = qF P σ := by simp [upd]
    rw [this]; exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) nl
  refine VP.seq Sk.pltStore ?_
  refine VP.seq (Sk.psel selP_taint (o := 5) (a := 1) (b := aQ) (sl := sLt) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (fun σ _ => by simp only [upd_self]; exact VG.Proof.Rsa.b2n_le _)
    (by decide)) ?_
  refine (Sk.psel selQ_taint (o := 6) (a := aQ) (b := 1) (sl := sLt) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (fun σ _ => by simp only [upd_self]; exact VG.Proof.Rsa.b2n_le _)
    (by decide)).mono (fun _ _ h => h) fun σ s h => Sk.mono h h.1 ?_ (fun x hx => by simp at hx) ?_
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    refine ⟨by simp only [List.mem_cons]; omega, ?_⟩
    rcases hx with rfl | rfl
    · by_cases hl : pF P σ < qF P σ
      · simp [upd, aW, aQ, hl, b2n, Nat.min_def]; omega
      · simp [upd, aW, aQ, hl, b2n, Nat.min_def]; omega
    · by_cases hl : pF P σ < qF P σ
      · simp [upd, aW, aQ, hl, b2n, Nat.max_def]; omega
      · simp [upd, aW, aQ, hl, b2n, Nat.max_def]; omega
  · intro d hd
    simp only [List.mem_singleton] at hd; subst hd
    exact ⟨by simp, by simp [upd, sMask, sLt]⟩

end

end VG.Proof.Rsa.Arm.Recover
