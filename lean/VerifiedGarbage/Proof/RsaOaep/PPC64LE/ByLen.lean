module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Two
public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Wp
public import VerifiedGarbage.Impl.RsaOaep.PPC64LE
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Two
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Wp
meta import VerifiedGarbage.Impl.RsaOaep.PPC64LE

/-!
# RSAES-OAEP on PPC64LE: the code for a digest length

Untrusted: everything here is checked by Lean. `byLen b ds` with the digest
length `D` in `r3`, one of `ds`, runs `b D` (`byLen_ok`), and two runs with
the same `D` leak alike (`byLen_ct`): each comparison is `r3 - d` into `r4`,
by the taint analysis with `r3` public (`lens_certs`), and its branch on a
public value.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE VG.Proof.RsaPkcs1Sig.PPC64LE

theorem ofNat_sub_beq64 {j N : Nat} (hj : j < 2 ^ 64) (hN : N < 2 ^ 64) :
    (BitVec.ofNat 64 j - BitVec.ofNat 64 N == 0) = decide (j = N) := by
  by_cases h : j = N
  · subst h; simp
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro e
    have := congrArg BitVec.toNat e
    have h0 : (0 : BitVec 64).toNat = 0 := rfl
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt hN, h0] at this
    omega

/-- The comparisons with each of `lens`: an immediate `subi` takes, and the
taint check with `r3` public. -/
theorem lens_certs : ∀ x ∈ lens, x ≤ 2 ^ 15 ∧
    ∃ hc, (VG.Taint.check taint (VG.PPC64LE.Taint.ofRegs [.r3]) (.block [.subi .r4 .r3 x]) hc).isSome = true := by
  intro x hx
  simp only [lens, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl <;> exact ⟨by decide, _, by taint_decide⟩

section
variable {b : Nat → Prog isa} {D : Nat} (hD : D < 2 ^ 64)
include hD

/-- `byLen b ds`, with `D` in `r3`, runs `b D`. -/
theorem byLen_ok {F : State → Prop} {Q : State → Prop} (h3 : ∀ t, F t → t.gpr .r3 = BitVec.ofNat 64 D)
    (hF : ∀ t t', F t → Only [.r4] t t' → t'.syms = t.syms → F t') (hb : ∀ t, F t → WP isa (b D) t Q) :
    ∀ {ds : List Nat}, D ∈ ds → (∀ x ∈ ds, x ≤ 2 ^ 15) → ∀ t, F t → WP isa (byLen b ds) t Q
  | [], h, _, _, _ => absurd h List.not_mem_nil
  | [x], h, _, t, ht => by obtain rfl := List.mem_singleton.mp h; exact hb t ht
  | x :: y :: ds, h, hx, t, ht => by
    have hx0 := hx x (List.mem_cons_self ..)
    refine WP.seq (WP.of_syms (wp_subi (h := hx0) fun t' o e => wp_nil fun y => ?_))
    have ht' := hF t t' ht o y
    have e4 : (t'.gpr .r4 == 0) = decide (D = x) := by
      rw [e, h3 t ht, ofNat_sub_beq64 hD (by omega)]
    refine WP.ite _ (eval_zero _ _) (fun hc => ?_) (fun hc => ?_)
    · rw [e4] at hc
      obtain rfl := of_decide_eq_true hc
      exact hb t' ht'
    · rw [e4] at hc
      have hne : D ≠ x := of_decide_eq_false hc
      exact byLen_ok h3 hF hb ((List.mem_cons.mp h).resolve_left hne)
        (fun z hz => hx z (List.mem_cons_of_mem _ hz)) t' ht'

/-- Two runs of `byLen b ds`, with `D` in `r3`, are two runs of `b D`. -/
theorem byLen_ct {α : Type} {Φ : α → State → Prop} {R : State → State → Prop}
    (h3 : ∀ a t, Φ a t → t.gpr .r3 = BitVec.ofNat 64 D) (hsp : ∀ a t₁ t₂, Φ a t₁ → Φ a t₂ → t₁.sp = t₂.sp)
    (hF : ∀ a t t', Φ a t → Only [.r4] t t' → t'.syms = t.syms → Φ a t') (hb : RelCT isa (Two Φ) (b D) R) :
    ∀ {ds : List Nat}, D ∈ ds → (∀ x ∈ ds, x ≤ 2 ^ 15 ∧
      ∃ hc, (VG.Taint.check taint (VG.PPC64LE.Taint.ofRegs [.r3]) (.block [.subi .r4 .r3 x]) hc).isSome = true) →
      RelCT isa (Two Φ) (byLen b ds) R
  | [], h, _ => absurd h List.not_mem_nil
  | [x], h, _ => by obtain rfl := List.mem_singleton.mp h; exact hb
  | x :: y :: ds, h, hx => by
    obtain ⟨hx0, _, hcx⟩ := hx x (List.mem_cons_self ..)
    let Ψ : α → State → Prop := fun a t => Φ a t ∧ t.gpr .r4 = BitVec.ofNat 64 D - BitVec.ofNat 64 x
    refine RelCT.seq (two_post (Ψ := Ψ) (two_taint [.r3] (fun a t₁ t₂ h₁ h₂ => ⟨hsp a t₁ t₂ h₁ h₂, fun r hr => by
        rw [List.mem_singleton.mp hr, h3 a t₁ h₁, h3 a t₂ h₂]⟩) hcx)
      fun a t ht => WP.of_syms (wp_subi (h := hx0) fun t' o e => wp_nil fun y => ⟨hF a t t' ht o y,
        by rw [e, h3 a t ht]⟩)) ?_
    have e4 : ∀ a t, Ψ a t → isa.eval (.zero .d .r4) t = some (decide (D = x)) := fun a t ht => by
      rw [eval_zero, ht.2, ofNat_sub_beq64 hD (by omega)]
    refine two_ite (fun a t₁ t₂ h₁ h₂ => by rw [e4 a t₁ h₁, e4 a t₂ h₂]) ?_ ?_
    · by_cases hDx : D = x
      · subst hDx
        exact hb.mono (fun _ _ ⟨a, h₁, h₂⟩ => ⟨a, h₁.1.1, h₂.1.1⟩) fun _ _ h => h
      · exact RelCT.of_false fun _ _ ⟨a, h₁, _⟩ => by
          have := (e4 a _ h₁.1).symm.trans h₁.2
          simp [hDx] at this
    · by_cases hDx : D = x
      · exact RelCT.of_false fun _ _ ⟨a, h₁, _⟩ => by
          have := (e4 a _ h₁.1).symm.trans h₁.2
          simp [hDx] at this
      · exact (byLen_ct h3 hsp hF hb ((List.mem_cons.mp h).resolve_left hDx)
          (fun z hz => hx z (List.mem_cons_of_mem _ hz))).mono
          (fun _ _ ⟨a, h₁, h₂⟩ => ⟨a, h₁.1.1, h₂.1.1⟩) fun _ _ h => h

end

end VG.Proof.RsaOaep.PPC64LE
