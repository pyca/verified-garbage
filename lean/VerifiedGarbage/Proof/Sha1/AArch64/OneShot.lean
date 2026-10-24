module

import VerifiedGarbage.Proof.Sha1.AArch64.Variant
public import VerifiedGarbage.Spec.Sha1.Contract
public import VerifiedGarbage.Impl.Sha1.AArch64.Stream
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.MdStream.AArch64.OneShot
public import VerifiedGarbage.Proof.Sha1.Md

/-!
# The one-shot SHA-1 digest on AArch64, against its shared contract

`Compress.oneShot_verified` proves the one-shot digest against
`OneShot.oneK`; `implies` moves it to `Spec.Sha1.digestContract`, whose
`stack` is the digest's frame.
-/

@[expose] public section

namespace VG.Proof.Sha1.AArch64.OneShot

open VG.AArch64 VG.Proof.MdStream.AArch64

/-- The stack the one-shot digest uses: its frame. -/
abbrev stack : Nat := Impl.MdStream.AArch64.OneShot.frameBytes Impl.Sha1.AArch64.Stream.params

/-- SHA-1's digest is all of the final hash value. -/
theorem hash_take (m : List Byte) : (md.hash Spec.Sha1.H0 m).take 20 = Spec.Sha1.hash m := by
  rw [Proof.Sha1.hash_eq]
  exact List.take_of_length_le (Nat.le_of_eq (Proof.Sha1.md.digest_length _))

theorem implies :
    (OneShot.oneK (P := Impl.Sha1.AArch64.Stream.params) md Spec.Sha1.H0 20).Implies
      (Spec.Sha1.digestContract AArch64.abi stack) := by
  refine
    { pre := fun s h => ?_
      post := fun s s' _ h => ?_
      pub := by implies_pub [Spec.Sha1.digestContract, Spec.Sha1.digestSig, Spec.Sha1.digestPost,
        OneShot.oneK, AArch64.abi, AArch64.argRegs]
      sat := ⟨sat, ?_⟩ }
  · sig_pre [Spec.Sha1.digestContract, Spec.Sha1.digestSig, Spec.Sha1.digestPost, AArch64.abi,
      AArch64.argRegs] at h
    obtain ⟨hsp, hrd, hwr, hdo, hfd, hfo, -, -⟩ := h
    exact ⟨hrd, hwr, hdo, hsp, hfd, hfo⟩
  · sig_post [Spec.Sha1.digestContract, Spec.Sha1.digestSig, Spec.Sha1.digestPost, AArch64.abi,
      AArch64.argRegs]
    rw [← hash_take]
    exact h trivial
  · have hp := sat_pre
    sig_pre [Spec.Sha1.digestContract, Spec.Sha1.digestSig, Spec.Sha1.digestPost, AArch64.abi,
      AArch64.argRegs]
    sig_and_intros
    all_goals first
      | exact hp.sp | rfl | exact hp.d_o | exact hp.f_d | exact hp.f_o | decide

end VG.Proof.Sha1.AArch64.OneShot
