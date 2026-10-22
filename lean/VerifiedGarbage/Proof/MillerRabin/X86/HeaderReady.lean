module

public import VerifiedGarbage.Proof.MillerRabin.X86.TimingContext

/-! # A public counter carried across products and equality tests -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Spec.Rsa.Mont (arrAt numAt)

structure HeaderReady (σ : State) (base : Addr) (bytes w d k : Nat) (s : State) : Prop where
  stage : Stage base bytes w σ s
  value : w32 s.mem base d = k

theorem product_header_ready {σ s : State} {base : Addr} {bytes w o a b d k : Nat}
    (facts : RoundFacts σ base bytes w) (h : HeaderReady σ base bytes w d k s)
    (ho : 5 ≤ o ∧ o < 28) (ha : 5 ≤ a ∧ a < 28) (hb : 5 ≤ b ∧ b < 28)
    (mutable : o = 5 ∨ o = 6 ∨ o = 8 ∨ (11 ≤ o ∧ o < 27)) (hd : d + 4 ≤ 256)
    (reduced : numAt s.mem base w b < val32 σ.mem base 256 (2 * w)) :
    WP isa (VG.Impl.MillerRabin.X86.product o a b) s (HeaderReady σ base bytes w d k) := by
  refine WP.mono (facts.multiply h.stage ho ha hb mutable reduced) ?_
  rintro t ⟨_, stage, _, frame⟩
  exact ⟨stage, (congrArg BitVec.toNat (product_frame_header h.stage.context h.stage.room facts.fit ho.2 hd frame)).trans h.value⟩

theorem equal_header_ready {σ s : State} {base : Addr} {bytes w a b d e k : Nat}
    (facts : RoundFacts σ base bytes w) (h : HeaderReady σ base bytes w d k s)
    (ha : a < 28) (hb : b < 28) (he : e ∈ [184, 188, 212, 232, 236, 240, 244])
    (hd : d + 4 ≤ 256) (apart : d + 4 ≤ e ∨ e + 4 ≤ d) :
    WP isa (VG.Impl.MillerRabin.X86.equal e a b) s (HeaderReady σ base bytes w d k) := by
  refine WP.mono (h.stage.equal facts.lower facts.upper facts.fit ha hb he facts.width) ?_
  rintro t ⟨_, stage, outside, _⟩
  have esmall : e + 4 ≤ 256 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hdrFit : 256 ≤ bytes := Nat.le_trans (Nat.le_add_right _ _) facts.fit
  have frame := VG.Proof.Bignum.outside_frame outside (by omega)
  exact ⟨stage, (congrArg BitVec.toNat (workspace_frame_word h.stage.context.ws.nowrap
    (Nat.le_trans hd hdrFit) (Nat.le_trans esmall hdrFit) apart frame)).trans h.value⟩

theorem TimingContext.counter {σ₁ σ₂ : State} {base : Addr} {bytes w d k : Nat} {sp len : BitVec 32}
    {c : Prog isa} (C : TimingContext σ₁ σ₂ base bytes w sp len) (small : k < 2 ^ 32)
    (bound : d + 4 ≤ 1600)
    (cert : ∃ hc, (VG.Taint.check VG.X86.taint (wordTaint [] 1 d) c hc).isSome = true) :
    RelCT isa (fun s t => HeaderReady σ₁ base bytes w d k s ∧ HeaderReady σ₂ base bytes w d k t) c
      (fun _ _ => True) := by
  apply (C.header bound cert).mono
  · rintro s t ⟨h₁, h₂⟩
    exact ⟨h₁.stage, h₂.stage, (readW_of_w32 small h₁.value).trans (readW_of_w32 small h₂.value).symm,
      fun _ h => (List.not_mem_nil h).elim⟩
  · intro _ _ _
    trivial

end VG.Proof.MillerRabin.X86
