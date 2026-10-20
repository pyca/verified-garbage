module

public import VerifiedGarbage.Proof.MlKem.AArch64.Dot.FullTerm
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sha3.AArch64.Sums

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Dot
open VG.AArch64 VG.Spec.MlKem

structure TermInput (s : State) (fg : Nat × Nat) (F G : Nat → Nat) : Prop where
  offF : fg.1 < 65536
  offG : fg.2 < 65536
  boundF : ∀ e < 8, F e < 3329
  boundG : ∀ e < 8, G e < 3329
  valueF : ∀ e < 8, (coeffAt s.mem (s.gpr .x28 + BitVec.ofNat 64 fg.1 + s.gpr .x12) e).toNat = F e
  valueG : ∀ e < 8, (coeffAt s.mem (s.gpr .x28 + BitVec.ofNat 64 fg.2 + s.gpr .x12) e).toNat = G e
  readF : ∀ i < 2, InRegions (s.rd ++ s.wr)
    (s.gpr .x28 + BitVec.ofNat 64 fg.1 + s.gpr .x12 + BitVec.ofNat 64 (16*i)) 16
  readG : ∀ i < 2, InRegions (s.rd ++ s.wr)
    (s.gpr .x28 + BitVec.ofNat 64 fg.2 + s.gpr .x12 + BitVec.ofNat 64 (16*i)) 16

theorem TermInput.keep {s s' : State} {fg : Nat × Nat} {F G : Nat → Nat}
    (h : TermInput s fg F G) (hk : Only [.x1, .x2] s s') : TermInput s' fg F G := by
  refine ⟨h.offF, h.offG, h.boundF, h.boundG, ?_, ?_, ?_, ?_⟩
  · rw [hk.mem, hk.get .x28, hk.get .x12]; exact h.valueF
  · rw [hk.mem, hk.get .x28, hk.get .x12]; exact h.valueG
  · rw [hk.rd, hk.wr, hk.get .x28, hk.get .x12]; exact h.readF
  · rw [hk.rd, hk.wr, hk.get .x28, hk.get .x12]; exact h.readG

def sumTerms (terms : List (Nat × Nat)) (F G : (Nat × Nat) → Nat → Nat)
    (a : Nat → Sums) : Nat → Sums :=
  terms.foldl (fun a fg => advance a (F fg) (G fg)) a

theorem terms_ok (terms : List (Nat × Nat)) {F G : (Nat × Nat) → Nat → Nat}
    {s : State} {a : Nat → Sums} {n : Nat}
    (hc : VConsts s) (ha : Accum s a) (hb : ∀ e < 4, (a e).Bounded n)
    (hn : n + terms.length ≤ 4)
    (hin : ∀ fg ∈ terms, TermInput s fg (F fg) (G fg)) :
    WP isa (.block (terms.flatMap Impl.MlKem.AArch64.Dot.dotTerm)) s fun s' =>
      Only [.x1, .x2] s s' ∧ VConsts s' ∧ Accum s' (sumTerms terms F G a) := by
  induction terms generalizing s a n with
  | nil => exact wp_nil ⟨Only.refl _ _, hc, ha⟩
  | cons fg terms ih =>
    simp only [List.length_cons] at hn
    rw [List.flatMap_cons, WP.block_append_iff]
    have h := hin fg (by simp)
    refine WP.mono (fullTerm_ok h.offF h.offG hc ha hb (by omega)
      h.boundF h.boundG h.valueF h.valueG h.readF h.readG) fun s₁ ⟨hk,hc₁,ha₁⟩ => ?_
    refine WP.mono (ih hc₁ ha₁ (n := n+1) (fun e he => (hb e he).next
      (h.boundF _ (by omega)) (h.boundF _ (by omega))
      (h.boundG _ (by omega)) (h.boundG _ (by omega)))
      (by omega)
      (fun fg hf => (hin fg (by simp [hf])).keep hk)) fun s₂ ⟨hk₂,hc₂,ha₂⟩ => ?_
    exact ⟨(hk.trans hk₂).mono (by simp), hc₂, ha₂⟩

end VG.Proof.MlKem.AArch64.Dot
