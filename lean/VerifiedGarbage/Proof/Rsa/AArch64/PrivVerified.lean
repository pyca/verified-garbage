import VerifiedGarbage.Proof.Rsa.AArch64.PrivCT

/-!
# `vg_rsa_private_checked` on AArch64: the shared contract

`vg_rsa_private_checked`, calling the implementation `v` of
`vg_rsa_private_crt` and its public operation, is verified against
`Spec.Rsa.privateCheckedContract` for the `stackBytes` bytes of stack its
frames use (`code_verified`); its frames nest `stackBytes / 16` units deep
(`privCode_depth`), which its callers need.
-/

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Rsa.AArch64.PrivChecked

/-- The name of `vg_rsa_private_checked` calling `v`. -/
def privName (v : CrtImpl) : String := Spec.Rsa.privateCheckedApi.name ++ v.suffix

/-- Its code. -/
abbrev privCode (v : CrtImpl) : Prog isa := privCodeOf v

theorem code_verified (v : CrtImpl) :
    Verified AArch64.target (privCode v) (Spec.Rsa.privateCheckedContract AArch64.abi stackBytes) :=
  Verified.of_correct (fun s h => code_correct v s h) (code_constantTime v) private_checked_implies

/-- Code without frames uses no stack. -/
theorem aarch64Depth_of_noFrames : ∀ {c : Prog isa}, c.noFrames = true → c.aarch64Depth = 0
  | .block _, _ => rfl
  | .seq a b, h => by
    simp only [Code.noFrames, Bool.and_eq_true] at h
    simp only [Code.aarch64Depth, aarch64Depth_of_noFrames h.1, aarch64Depth_of_noFrames h.2, Nat.max_self]
  | .ite _ a b, h => by
    simp only [Code.noFrames, Bool.and_eq_true] at h
    simp only [Code.aarch64Depth, aarch64Depth_of_noFrames h.1, aarch64Depth_of_noFrames h.2, Nat.max_self]
  | .loop b _, h => by
    simp only [Code.noFrames] at h
    simp only [Code.aarch64Depth, aarch64Depth_of_noFrames h]
  | .call _ b, h => by
    simp only [Code.noFrames] at h
    simp only [Code.aarch64Depth, aarch64Depth_of_noFrames h]
  | .frame .., h => by simp [Code.noFrames] at h

/-- Its frames: `x30`'s, and the 3232 bytes of the inner frame. -/
theorem privCode_depth (v : CrtImpl) : (privCode v).aarch64Depth = stackBytes / 16 := by
  simp only [privCode, privCodeOf, code, body, check, tail, seqs, List.cons_append, List.nil_append,
    Code.aarch64Depth, aarch64Depth_of_noFrames v.noFrames, aarch64Depth_of_noFrames v.pcNoFrames,
    aarch64Depth_of_noFrames v.pdNoFrames, cmpLoop, releaseLoop, Instr.frameUnits, frameBytes, stackBytes]
  decide

end VG.Proof.Rsa.AArch64
