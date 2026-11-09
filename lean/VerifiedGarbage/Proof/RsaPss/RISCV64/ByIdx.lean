module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.Two
public import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.Wp
public import VerifiedGarbage.Impl.RsaPss.RISCV64
import VerifiedGarbage.Proof.Framework.RISCV64.Syms
import VerifiedGarbage.Proof.RsaOaep.RISCV64.ByLen
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.Two
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.Wp
meta import VerifiedGarbage.Impl.RsaPss.RISCV64

/-!
# RSASSA-PSS on RISC-V: the code for a hash function's index

Untrusted: everything here is checked by Lean. As RSAES-OAEP's code for a
digest length (`Proof/RsaOaep/RISCV64/ByLen.lean`): `byIdx b is` with the
index `I` in `t5`, one of `is`, runs `b I` (`byIdx_ok`), and two runs with
the same `I` leak alike (`byIdx_ct`): each comparison is `t5 - i` into `t4`,
by the taint analysis with `t5` public (`idx_certs`), and its branch on a
public value.
-/

@[expose] public section

namespace VG.Proof.RsaPss.RISCV64

open VG VG.RISCV64 VG.Impl.RsaPss.RISCV64 VG.Proof.RsaPkcs1Sig.RISCV64
open VG.Proof.RsaOaep.RISCV64 (ofNat_sub_beq64)

/-- The comparisons with each of `idxs`: an immediate `subi` takes, and the
taint check with `t5` public. -/
theorem idx_certs : ∀ x ∈ idxs, x ≤ 2048 ∧
    ∃ hc, (taint.check (VG.RISCV64.Taint.ofRegs [.t5]) (.block [.addi .t4 .t5 (-(x : Int))]) hc).isSome = true := by
  intro x hx
  simp only [idxs, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by decide, _, by taint_decide⟩

section
variable {b : Nat → Prog isa} {I : Nat} (hI : I < 2 ^ 64)
include hI

/-- `byIdx b is`, with `I` in `t5`, runs `b I`. -/
theorem byIdx_ok {F : State → Prop} {Q : State → Prop} (h5 : ∀ t, F t → t.gpr .t5 = BitVec.ofNat 64 I)
    (hF : ∀ t t', F t → Only [.t4] t t' → t'.syms = t.syms → F t') (hb : ∀ t, F t → WP isa (b I) t Q) :
    ∀ {is : List Nat}, I ∈ is → (∀ x ∈ is, x ≤ 2048) → ∀ t, F t → WP isa (byIdx b is) t Q
  | [], h, _, _, _ => absurd h List.not_mem_nil
  | [x], h, _, t, ht => by obtain rfl := List.mem_singleton.mp h; exact hb t ht
  | x :: y :: is, h, hx, t, ht => by
    have hx0 := hx x (List.mem_cons_self ..)
    refine WP.seq (WP.of_syms (wp_subi (h := hx0) fun t' o e => wp_nil fun y => ?_))
    have ht' := hF t t' ht o y
    have e4 : (t'.gpr .t4 == 0) = decide (I = x) := by
      rw [e, h5 t ht, ofNat_sub_beq64 hI (by omega)]
    refine WP.ite _ (eval_zero _ _) (fun hc => ?_) (fun hc => ?_)
    · rw [e4] at hc
      obtain rfl := of_decide_eq_true hc
      exact hb t' ht'
    · rw [e4] at hc
      have hne : I ≠ x := of_decide_eq_false hc
      exact byIdx_ok h5 hF hb ((List.mem_cons.mp h).resolve_left hne)
        (fun z hz => hx z (List.mem_cons_of_mem _ hz)) t' ht'

/-- Two runs of `byIdx b is`, with `I` in `t5`, are two runs of `b I`. -/
theorem byIdx_ct {α : Type} {Φ : α → State → Prop} {R : State → State → Prop}
    (h5 : ∀ a t, Φ a t → t.gpr .t5 = BitVec.ofNat 64 I) (hsp : ∀ a t₁ t₂, Φ a t₁ → Φ a t₂ → t₁.sp = t₂.sp)
    (hF : ∀ a t t', Φ a t → Only [.t4] t t' → t'.syms = t.syms → Φ a t') (hb : RelCT isa (Two Φ) (b I) R) :
    ∀ {is : List Nat}, I ∈ is → (∀ x ∈ is, x ≤ 2048 ∧
      ∃ hc, (taint.check (VG.RISCV64.Taint.ofRegs [.t5]) (.block [.addi .t4 .t5 (-(x : Int))]) hc).isSome = true) →
      RelCT isa (Two Φ) (byIdx b is) R
  | [], h, _ => absurd h List.not_mem_nil
  | [x], h, _ => by obtain rfl := List.mem_singleton.mp h; exact hb
  | x :: y :: is, h, hx => by
    obtain ⟨hx0, _, hcx⟩ := hx x (List.mem_cons_self ..)
    let Ψ : α → State → Prop := fun a t => Φ a t ∧ t.gpr .t4 = BitVec.ofNat 64 I - BitVec.ofNat 64 x
    refine RelCT.seq (two_post (Ψ := Ψ) (two_taint [.t5] (fun a t₁ t₂ h₁ h₂ => ⟨hsp a t₁ t₂ h₁ h₂, fun r hr => by
        rw [List.mem_singleton.mp hr, h5 a t₁ h₁, h5 a t₂ h₂]⟩) hcx)
      fun a t ht => WP.of_syms (wp_subi (h := hx0) fun t' o e => wp_nil fun y => ⟨hF a t t' ht o y,
        by rw [e, h5 a t ht]⟩)) ?_
    have e4 : ∀ a t, Ψ a t → isa.eval (.zero .t4) t = some (decide (I = x)) := fun a t ht => by
      rw [eval_zero, ht.2, ofNat_sub_beq64 hI (by omega)]
    refine two_ite (fun a t₁ t₂ h₁ h₂ => by rw [e4 a t₁ h₁, e4 a t₂ h₂]) ?_ ?_
    · by_cases hIx : I = x
      · subst hIx
        exact hb.mono (fun _ _ ⟨a, h₁, h₂⟩ => ⟨a, h₁.1.1, h₂.1.1⟩) fun _ _ h => h
      · exact RelCT.of_false fun _ _ ⟨a, h₁, _⟩ => by
          have := (e4 a _ h₁.1).symm.trans h₁.2
          simp [hIx] at this
    · by_cases hIx : I = x
      · exact RelCT.of_false fun _ _ ⟨a, h₁, _⟩ => by
          have := (e4 a _ h₁.1).symm.trans h₁.2
          simp [hIx] at this
      · exact (byIdx_ct h5 hsp hF hb ((List.mem_cons.mp h).resolve_left hIx)
          (fun z hz => hx z (List.mem_cons_of_mem _ hz))).mono
          (fun _ _ ⟨a, h₁, h₂⟩ => ⟨a, h₁.1.1, h₂.1.1⟩) fun _ _ h => h

end

end VG.Proof.RsaPss.RISCV64
