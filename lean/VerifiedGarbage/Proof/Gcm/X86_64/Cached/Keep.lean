import VerifiedGarbage.Impl.Gcm.X86_64.StitchZH
import VerifiedGarbage.Proof.Framework.X86_64.HighKeep

/-! # The cached GCM loops leave the high registers unchanged -/

namespace VG.Proof.Gcm.X86_64.StitchZH
open VG VG.X86_64
open VG.Impl.Aes.X86_64.VaesZH (aes keyOp round)
open VG.Impl.Aes.X86_64.VaesZ (ctrsZ xorDataZ)
open VG.Impl.Gcm.X86_64.Stitch (aregs)
open VG.Impl.Gcm.X86_64.StitchZH

/-- The interleaved work may write low registers, but never cached keys. -/
theorem aes_keeps (rs : List XReg) (g : Nat → List Instr)
    (hg : ∀ j, (g j).all Instr.keepsH = true) : (aes rs g).all Instr.keepsH = true := by
  simp [aes, keyOp, round, Code.all, List.all_flatMap, List.all_map, Instr.keepsH, hg]

theorem batch_keeps (j : Nat) (g : Nat → List Instr)
    (hg : ∀ j, (g j).all Instr.keepsH = true) : (batch j g).all Instr.keepsH = true := by
  simp [batch, Code.all, aes_keeps _ g hg, ctrsZ, xorDataZ, aregs, Instr.keepsH]

theorem gq_keeps (j : Nat) : (Impl.Gcm.X86_64.StitchZ.gq j).all Instr.keepsH = true := by
  unfold Impl.Gcm.X86_64.StitchZ.gq
  split
  · unfold Impl.Gcm.X86_64.StitchZ.ghLoad
    split <;> split <;> rfl
  · split <;> rfl

theorem gq48_keeps (b j : Nat) : (Impl.Gcm.X86_64.StitchZ.gq48 b j).all Instr.keepsH = true := by
  unfold Impl.Gcm.X86_64.StitchZ.gq48
  split
  · unfold Impl.Gcm.X86_64.StitchZ.pair
    cases h : decide (b = 0) <;> rfl
  · split
    · unfold Impl.Gcm.X86_64.StitchZ.pair
      rfl
    · split <;> rfl

end VG.Proof.Gcm.X86_64.StitchZH
