module

import VerifiedGarbage.Proof.Sha512.AArch64.Variant
public import VerifiedGarbage.Spec.Sha512.Contract
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Impl.Sha512.AArch64.Stream
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.MdStream.AArch64.OneShot
public import VerifiedGarbage.Proof.Sha512.Md

/-!
# The one-shot SHA-512 family digests on AArch64, against their shared contracts

`Compress.oneShot_verified` proves each one-shot digest against
`OneShot.oneK`; `implies` moves it to `Spec.Sha512.digestContract`, whose
`stack` is the digest's frame.
-/

@[expose] public section

namespace VG.Proof.Sha512.AArch64.OneShot

open VG.AArch64 VG.Proof.MdStream.AArch64

/-- The stack the one-shot digests use: their frame. -/
abbrev stack : Nat := Impl.MdStream.AArch64.OneShot.frameBytes Impl.Sha512.AArch64.Stream.params

theorem implies {o : List Instr} {iv : Spec.Sha512.HashValue} {D : Nat} {digest : List Byte → List Byte}
    (hD : D ≤ 64) (hdg : ∀ m, (md.hash iv m).take D = digest m) :
    (OneShot.oneK (P := { Impl.Sha512.AArch64.Stream.params with out := o }) md iv D).Implies
      (Spec.Sha512.digestContract AArch64.abi D digest stack) := by
  refine
    { pre := fun s h => ?_
      post := fun s s' _ h => ?_
      pub := by implies_pub [Spec.Sha512.digestContract, Spec.Sha512.digestSig, Spec.Sha512.digestPost,
        OneShot.oneK, AArch64.abi, AArch64.argRegs]
      sat := ⟨sat D, ?_⟩ }
  · sig_pre [Spec.Sha512.digestContract, Spec.Sha512.digestSig, Spec.Sha512.digestPost, AArch64.abi,
      AArch64.argRegs] at h
    obtain ⟨hsp, hrd, hwr, hdo, hfd, hfo, -, -⟩ := h
    exact pre_out ⟨hrd, hwr, hdo, hsp, hfd, hfo⟩
  · sig_post [Spec.Sha512.digestContract, Spec.Sha512.digestSig, Spec.Sha512.digestPost, AArch64.abi,
      AArch64.argRegs]
    rw [← hdg]
    exact h (s.gpr .x1).isLt
  · have hp := sat_pre₀ hD
    sig_pre [Spec.Sha512.digestContract, Spec.Sha512.digestSig, Spec.Sha512.digestPost, AArch64.abi,
      AArch64.argRegs]
    sig_and_intros
    all_goals first
      | exact hp.sp | rfl | exact hp.d_o | exact hp.f_d | exact hp.f_o | decide
      | exact (show 8192 + D ≤ 2 ^ 64 by omega)

end VG.Proof.Sha512.AArch64.OneShot
