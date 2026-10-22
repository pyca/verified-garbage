module

public import VerifiedGarbage.Proof.MillerRabin.X86.StageStore

/-! # Two immediate header initializations with one framing proof -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.Mont.X86
open VG.Spec.Rsa.Mont (arrAt)

namespace Stage

theorem header_pair {σ s : State} {base : Addr} {bytes w d e : Nat} {x y : BitVec 32}
    (h : Stage base bytes w σ s) (hf : arrAt w 28 ≤ bytes)
    (hd : d ∈ [184, 188, 212, 232, 236, 240, 244])
    (he : e ∈ [184, 188, 212, 232, 236, 240, 244]) :
    WP isa (.block [.mov .eax (.imm x), .store (sc d) .eax,
      .mov .eax (.imm y), .store (sc e) .eax]) s fun t =>
      Stage base bytes w σ t ∧ t.mem = (s.mem.writeW (off base d) x).writeW (off base e) y ∧
      Frame [⟨off base d, 4⟩, ⟨off base e, 4⟩] s.mem t.mem := by
  refine wp_movS rfl fun s₁ U₁ _ => ?_
  have h₁ := h.of_registers U₁.keeps U₁.mem
  refine h₁.store_header hf hd fun s₂ h₂ m₂ _ _ => ?_
  refine wp_movS rfl fun s₃ U₃ _ => ?_
  have h₃ := h₂.of_registers U₃.keeps U₃.mem
  refine h₃.store_header hf he fun t ht mt _ _ => WP.block_nil ?_
  have mem : t.mem = (s.mem.writeW (off base d) x).writeW (off base e) y := by
    rw [mt, U₃.gpr, U₃.mem, m₂, U₁.gpr, U₁.mem]
  refine ⟨ht, mem, ?_⟩
  rw [mem]
  exact ((Frame.refl _ _).writeW (by simp) _ (Region.contains_self _ _)).writeW
    (by simp) _ (Region.contains_self _ _)

end Stage
end VG.Proof.MillerRabin.X86
