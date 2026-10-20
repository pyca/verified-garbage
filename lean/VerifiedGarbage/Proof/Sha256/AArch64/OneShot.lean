module

import VerifiedGarbage.Proof.Sha256.AArch64.Variant
public import VerifiedGarbage.Spec.Sha256.Contract
public import VerifiedGarbage.Impl.Sha256.AArch64.Stream
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.MdStream.AArch64.OneShot
public import VerifiedGarbage.Proof.Sha256.Md

/-!
# The one-shot SHA-256 and SHA-224 digests on AArch64, against their shared contracts

`Compress.oneShot_verified` proves each one-shot digest against
`OneShot.oneK`; `implies` moves it to `Spec.Sha256.digestContract`, whose
`stack` is the digest's frame.
-/

@[expose] public section

namespace VG.Proof.Sha256.AArch64.OneShot

open VG.AArch64 VG.Proof.MdStream.AArch64

/-- The stack the one-shot digests use: their frame. -/
abbrev stack : Nat := Impl.MdStream.AArch64.OneShot.frameBytes Impl.Sha256.AArch64.Stream.params

theorem implies {o : List Instr} {iv : Spec.Sha256.HashValue} {D : Nat} {digest : List Byte → List Byte}
    (hD : D ≤ 64) (hdg : ∀ m, (md.hash iv m).take D = digest m) :
    (OneShot.oneK (P := { Impl.Sha256.AArch64.Stream.params with out := o }) md iv D).Implies
      (Spec.Sha256.digestContract AArch64.abi D digest stack) := by
  refine
    { pre := fun s h => ?_
      post := fun s s' _ h => ?_
      pub := by implies_pub [Spec.Sha256.digestContract, Spec.Sha256.digestSig, Spec.Sha256.digestPost,
        OneShot.oneK, AArch64.abi, AArch64.argRegs]
      sat := ⟨sat D, ?_⟩ }
  · sig_pre [Spec.Sha256.digestContract, Spec.Sha256.digestSig, Spec.Sha256.digestPost, AArch64.abi,
      AArch64.argRegs] at h
    obtain ⟨hsp, hrd, hwr, hdo, hfd, hfo, -, -⟩ := h
    exact pre_out ⟨hrd, hwr, hdo, hsp, hfd, hfo⟩
  · sig_post [Spec.Sha256.digestContract, Spec.Sha256.digestSig, Spec.Sha256.digestPost, AArch64.abi,
      AArch64.argRegs]
    rw [← hdg]
    exact h trivial
  · have hp := sat_pre₀ hD
    sig_pre [Spec.Sha256.digestContract, Spec.Sha256.digestSig, Spec.Sha256.digestPost, AArch64.abi,
      AArch64.argRegs]
    sig_and_intros
    all_goals first
      | exact hp.sp | rfl | exact hp.d_o | exact hp.f_d | exact hp.f_o | decide
      | exact (show 8192 + D ≤ 2 ^ 64 by omega)

/-- SHA-256's digest is all of the final hash value. -/
theorem hash_take (m : List Byte) : (md.hash Spec.Sha256.H0 m).take 32 = Spec.Sha256.hash m := by
  rw [Proof.Sha256.hash_eq]
  exact List.take_of_length_le (Nat.le_of_eq (Proof.Sha256.md.digest_length _))

/-- SHA-224's digest is the first 28 bytes of the final hash value. -/
theorem sha224_take (m : List Byte) : (md.hash Spec.Sha256.H0_224 m).take 28 = Spec.Sha256.sha224 m := rfl

end VG.Proof.Sha256.AArch64.OneShot
