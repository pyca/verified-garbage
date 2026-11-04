module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Two
public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Wp
public import VerifiedGarbage.Impl.Ecdsa.Rfc6979.PPC64LE
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.ByLen
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Two
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Wp
meta import VerifiedGarbage.Impl.Ecdsa.Rfc6979.PPC64LE

/-!
# Deterministic ECDSA on PPC64LE: the code for the hash function of a table

Untrusted: everything here is checked by Lean. `byIdx b is` with the hash
function's index `i` in `r9`, one of `is`, runs `b i` (`byIdx_ok`), and two
runs with the same `i` leak alike (`byIdx_ct`): each comparison is `r9 - j`
into `r10`, by the taint analysis with `r9` public (`idxs_certs`), and its
branch on a public value. As RSAES-OAEP's `byIdx`
(`Proof/RsaOaep/PPC64LE/ByLen.lean`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.PPC64LE

open VG VG.PPC64LE VG.Impl.Ecdsa.Rfc6979.PPC64LE VG.Proof.RsaPkcs1Sig.PPC64LE
open VG.Proof.RsaOaep.PPC64LE (ofNat_sub_beq64)
open VG.Proof.RsaOaep.PPC64LE (ofNat_sub_beq64)

/-- The comparisons with each of `idxs`: an immediate `subi` takes, and the
taint check with `r9` public. -/
theorem idxs_certs : ∀ x ∈ idxs, x ≤ 2 ^ 15 ∧
    ∃ hc, (VG.Taint.check taint (VG.PPC64LE.Taint.ofRegs [.r9]) (.block [.subi .r10 .r9 x]) hc).isSome = true := by
  intro x hx
  simp only [idxs, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by decide, _, by taint_decide⟩

section
variable {b : Nat → Prog isa} {D : Nat} (hD : D < 2 ^ 64)
include hD

/-- `byIdx b is`, with `D` in `r9`, runs `b D`. -/
theorem byIdx_ok {F : State → Prop} {Q : State → Prop} (h3 : ∀ t, F t → t.gpr .r9 = BitVec.ofNat 64 D)
    (hF : ∀ t t', F t → Only [.r10] t t' → t'.syms = t.syms → F t') (hb : ∀ t, F t → WP isa (b D) t Q) :
    ∀ {is : List Nat}, D ∈ is → (∀ x ∈ is, x ≤ 2 ^ 15) → ∀ t, F t → WP isa (byIdx b is) t Q
  | [], h, _, _, _ => absurd h List.not_mem_nil
  | [x], h, _, t, ht => by obtain rfl := List.mem_singleton.mp h; exact hb t ht
  | x :: y :: is, h, hx, t, ht => by
    have hx0 := hx x (List.mem_cons_self ..)
    refine WP.seq (WP.of_syms (wp_subi (h := hx0) fun t' o e => wp_nil fun y => ?_))
    have ht' := hF t t' ht o y
    have e4 : (t'.gpr .r10 == 0) = decide (D = x) := by
      rw [e, h3 t ht, ofNat_sub_beq64 hD (by omega)]
    refine WP.ite _ (eval_zero _ _) (fun hc => ?_) (fun hc => ?_)
    · rw [e4] at hc
      obtain rfl := of_decide_eq_true hc
      exact hb t' ht'
    · rw [e4] at hc
      have hne : D ≠ x := of_decide_eq_false hc
      exact byIdx_ok h3 hF hb ((List.mem_cons.mp h).resolve_left hne)
        (fun z hz => hx z (List.mem_cons_of_mem _ hz)) t' ht'

/-- Two runs of `byIdx b is`, with `D` in `r9`, are two runs of `b D`. -/
theorem byIdx_ct {α : Type} {Φ : α → State → Prop} {R : State → State → Prop}
    (h3 : ∀ a t, Φ a t → t.gpr .r9 = BitVec.ofNat 64 D) (hsp : ∀ a t₁ t₂, Φ a t₁ → Φ a t₂ → t₁.sp = t₂.sp)
    (hF : ∀ a t t', Φ a t → Only [.r10] t t' → t'.syms = t.syms → Φ a t') (hb : RelCT isa (Two Φ) (b D) R) :
    ∀ {is : List Nat}, D ∈ is → (∀ x ∈ is, x ≤ 2 ^ 15 ∧
      ∃ hc, (VG.Taint.check taint (VG.PPC64LE.Taint.ofRegs [.r9]) (.block [.subi .r10 .r9 x]) hc).isSome = true) →
      RelCT isa (Two Φ) (byIdx b is) R
  | [], h, _ => absurd h List.not_mem_nil
  | [x], h, _ => by obtain rfl := List.mem_singleton.mp h; exact hb
  | x :: y :: is, h, hx => by
    obtain ⟨hx0, _, hcx⟩ := hx x (List.mem_cons_self ..)
    let Ψ : α → State → Prop := fun a t => Φ a t ∧ t.gpr .r10 = BitVec.ofNat 64 D - BitVec.ofNat 64 x
    refine RelCT.seq (two_post (Ψ := Ψ) (two_taint [.r9] (fun a t₁ t₂ h₁ h₂ => ⟨hsp a t₁ t₂ h₁ h₂, fun r hr => by
        rw [List.mem_singleton.mp hr, h3 a t₁ h₁, h3 a t₂ h₂]⟩) hcx)
      fun a t ht => WP.of_syms (wp_subi (h := hx0) fun t' o e => wp_nil fun y => ⟨hF a t t' ht o y,
        by rw [e, h3 a t ht]⟩)) ?_
    have e4 : ∀ a t, Ψ a t → isa.eval (.zero .d .r10) t = some (decide (D = x)) := fun a t ht => by
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
      · exact (byIdx_ct h3 hsp hF hb ((List.mem_cons.mp h).resolve_left hDx)
          (fun z hz => hx z (List.mem_cons_of_mem _ hz))).mono
          (fun _ _ ⟨a, h₁, h₂⟩ => ⟨a, h₁.1.1, h₂.1.1⟩) fun _ _ h => h

end

end VG.Proof.Ecdsa.Rfc6979.PPC64LE
