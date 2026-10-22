module

public import VerifiedGarbage.Proof.MillerRabin.X86.BodyTiming
import VerifiedGarbage.Proof.Framework.Sig

/-! # The shared round contract's complete constant-time guarantee -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.MillerRabin.X86

theorem round_public {s t : State}
    (h : (Spec.MillerRabin.roundContract abi Spec.MillerRabin.compact stackBytes).pub s t) : RoundPublic s t := by
  sig_pub [Spec.MillerRabin.roundContract, Spec.MillerRabin.roundSig, abi, argSlots, argVal, argBytes,
    stackBelow] at h
  obtain ⟨sp, width, a0, a1⟩ := h
  refine ⟨sp, ?_, List.singleton_inj.mp width⟩
  intro i hi
  have cases : i = 0 ∨ i = 1 := by omega
  rcases cases with rfl | rfl
  · exact a0
  · exact a1

theorem round_constantTime : ConstantTime isa
    (Spec.MillerRabin.roundContract abi Spec.MillerRabin.compact stackBytes).pre
    (Spec.MillerRabin.roundContract abi Spec.MillerRabin.compact stackBytes).pub code := by
  apply RelCT.constantTime
  unfold code
  apply RelCT.frameAlloc (R := fun _ _ => True)
  rintro a b tr₁ tr₂ a' b' ⟨s, t, ⟨pre₁, pre₂, pub⟩, ha, hb⟩ e₁ e₂
  exact (body_ct (roundAbi_of pre₁) (roundAbi_of pre₂) (round_public pub)) a b tr₁ tr₂ a' b' ⟨ha, hb⟩ e₁ e₂

end VG.Proof.MillerRabin.X86
