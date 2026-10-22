module

public import VerifiedGarbage.Proof.MillerRabin.X86.TimingReady

/-! # Shared public parameters for two runs with independent secret workspaces -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Spec.Rsa.Mont (arrAt numAt)

structure TimingContext (σ₁ σ₂ : State) (base : Addr) (bytes w : Nat) (sp len : BitVec 32) : Prop where
  initial₁ : PieceInput base bytes w sp len σ₁
  initial₂ : PieceInput base bytes w sp len σ₂
  facts₁ : RoundFacts σ₁ base bytes w
  facts₂ : RoundFacts σ₂ base bytes w
  size : bytes = len.toNat * 8

namespace TimingContext

theorem pieces {σ₁ σ₂ : State} {base : Addr} {bytes w : Nat} {sp len : BitVec 32} {c : Prog isa}
    (C : TimingContext σ₁ σ₂ base bytes w sp len) (cert : PieceCert c) :
    RelCT isa (fun s t => Stage base bytes w σ₁ s ∧ Stage base bytes w σ₂ t) c (fun _ _ => True) :=
  C.initial₁.pieces_ct C.initial₂ C.facts₁ C.facts₂ cert

theorem product_input {σ s : State} {base : Addr} {bytes w b : Nat} {sp len : BitVec 32}
    (initial : PieceInput base bytes w sp len σ) (facts : RoundFacts σ base bytes w)
    (h : Stage base bytes w σ s) (reduced : numAt s.mem base w b < val32 σ.mem base 256 (2 * w)) :
    ProductInput base bytes w sp len b s := by
  refine ⟨initial.of_stage facts h, ?_, ?_⟩
  · rw [h.modulus_constant facts.lower facts.fit, h.inverse_constant facts.fit]
    exact facts.inverse
  · rw [h.modulus_constant facts.lower facts.fit]
    rw [candidate_words] at reduced
    exact reduced

theorem multiply {σ₁ σ₂ : State} {base : Addr} {bytes w o a b : Nat} {sp len : BitVec 32}
    (C : TimingContext σ₁ σ₂ base bytes w sp len)
    (ho : 5 ≤ o ∧ o < 28) (ha : 5 ≤ a ∧ a < 28) (hb : 5 ≤ b ∧ b < 28)
    (cert : ∃ hc, (VG.Taint.check VG.X86.taint argsTaint (.block (VG.Impl.MillerRabin.X86.productArgs o a b)) hc).isSome = true) :
    RelCT isa (fun s t => (Stage base bytes w σ₁ s ∧ numAt s.mem base w b < val32 σ₁.mem base 256 (2 * w)) ∧
      (Stage base bytes w σ₂ t ∧ numAt t.mem base w b < val32 σ₂.mem base 256 (2 * w)))
      (VG.Impl.MillerRabin.X86.product o a b) (fun _ _ => True) := by
  apply (product_relCT C.size C.facts₁.lower C.facts₁.upper C.facts₁.fit ho ha hb cert).mono
  · rintro s t ⟨⟨h₁, r₁⟩, ⟨h₂, r₂⟩⟩
    exact ⟨product_input C.initial₁ C.facts₁ h₁ r₁, product_input C.initial₂ C.facts₂ h₂ r₂⟩
  · intro _ _ _
    trivial

theorem header {σ₁ σ₂ : State} {base : Addr} {bytes w d : Nat} {sp len : BitVec 32}
    {rs : List Reg} {c : Prog isa} (C : TimingContext σ₁ σ₂ base bytes w sp len)
    (bound : d + 4 ≤ 1600)
    (cert : ∃ hc, (VG.Taint.check VG.X86.taint (wordTaint rs 1 d) c hc).isSome = true) :
    RelCT isa (fun s t => Stage base bytes w σ₁ s ∧ Stage base bytes w σ₂ t ∧
      s.mem.readW (off base d) 32 = t.mem.readW (off base d) 32 ∧ ∀ r ∈ rs, s.gpr r = t.gpr r) c
      (fun _ _ => True) := by
  obtain ⟨hc, checked⟩ := cert
  refine RelCT.taint (A := taint) (wordTaint rs 1 d) (fun s t ⟨h₁, h₂, wordEq, regs⟩ => ?_) checked
  have i₁ := C.initial₁.of_stage C.facts₁ h₁
  have i₂ := C.initial₂.of_stage C.facts₂ h₂
  apply i₁.agree_word i₂ bound ?_ regs
  dsimp only [VG.X86.Taint.byteAddr, VG.X86.Taint.region]
  rw [i₁.wr, i₂.wr]
  exact wordEq

end TimingContext
end VG.Proof.MillerRabin.X86
