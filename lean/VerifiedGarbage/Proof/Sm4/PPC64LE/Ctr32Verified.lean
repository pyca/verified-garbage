module

import VerifiedGarbage.Proof.Sm4.PPC64LE.ModesVerified
import VerifiedGarbage.Proof.Sm4.PPC64LE.ModesFrame
public import VerifiedGarbage.Proof.Sm4.Ctr32Scratch
public import VerifiedGarbage.Impl.Sm4.PPC64LE.Ctr32
public import VerifiedGarbage.Spec.Sm4.Gcm
public import VerifiedGarbage.Proof.Sm4.Contract
import VerifiedGarbage.Proof.Modes.PPC64LE.Wide
import VerifiedGarbage.Proof.Modes.Ctr32
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchWipe
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sm4.PPC64LE.Ctr32Lit
import VerifiedGarbage.Proof.Sm4.PPC64LE.Lit
import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Sm4.PPC64LE.CallSum
meta import VerifiedGarbage.Proof.Framework.PPC64LE.SlotTaint
meta import VerifiedGarbage.Impl.Sm4.PPC64LE.Ctr32
meta import VerifiedGarbage.Proof.Sm4.PPC64LE.Ctr32Lit
meta import VerifiedGarbage.Proof.Sm4.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Sm4.PPC64LE.CallSum
meta import VerifiedGarbage.Proof.Framework.RegSet
meta import VerifiedGarbage.Proof.Sm4.PPC64LE.ModesConstantTime
public import VerifiedGarbage.Impl.StackScratch.PPC64LE
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Framework.Bitslice.Atoms
public import VerifiedGarbage.Proof.Framework.PPC64LE.StraightK
public import VerifiedGarbage.Proof.Modes.PPC64LE.Seq
public import VerifiedGarbage.Proof.Sm4.PPC64LE.ModesConstantTime
public import VerifiedGarbage.Proof.Sm4.SboxTable

/-!
# SM4's counter mode with GCM's `inc₃₂` on PPC64LE meets its contract

`ctr32_correct` and `ctr32_constantTime`: the counter mode of
`Proof/Modes/PPC64LE/Wide.lean` over SM4's core (`dirCoreSpec .encrypt`),
with the working space as the fifth argument (`modeContract`), is correct
(`ctr32Post`) and constant time as the other modes are
(`ModesConstantTime.lean`).
-/

@[expose] public section

namespace VG.Proof.Sm4.PPC64LE.Modes

open VG VG.PPC64LE VG.Impl.Sm4.PPC64LE VG.Impl.Modes
open VG.Proof.Sm4.PPC64LE (dirCoreSpec modeContract modeTaint modes_agree modeFrameSat)

/-- The data XORed with the encrypted counter blocks, and `inc₃₂ⁿ` of the
counter block, as GCM's blocks. -/
def ctr32Post (s s' : State) : Prop :=
  Spec.Gcm.blocksAt s'.mem (s.gpr .r5) (s.gpr .r6).toNat =
      Spec.Gcm.ctr32 (Spec.Sm4.gcmCipher (Spec.Sm4.scheduleAt s.mem (s.gpr .r3)))
        (Spec.Gcm.blockAt s.mem (s.gpr .r4)) (Spec.Gcm.blocksAt s.mem (s.gpr .r5) (s.gpr .r6).toNat) ∧
    Spec.Gcm.blockAt s'.mem (s.gpr .r4) =
      Nat.repeat Spec.Gcm.inc32 (s.gpr .r6).toNat (Spec.Gcm.blockAt s.mem (s.gpr .r4))

theorem ctr32_constantTime {post : State → State → Prop} :
    ConstantTime isa (modeContract 16 post).pre Proof.Sm4.PPC64LE.modePub ctr32 :=
  VG.Taint.constantTime_of_exists (A := slotTaint) modeTaint modes_agree
    (by taint_decide_sum [prepSum, cryptSum])

theorem ctr32_correct (s : State) (hs : (modeContract 16 ctr32Post).pre s) :
    ∃ t s', Exec isa ctr32 s t s' ∧ abiPreserved s s' ∧ (modeContract 16 ctr32Post).post s s' := by
  refine pick_correct fun v => ?_
  obtain ⟨-, eP, eD, eN, eM, -, -⟩ := Proof.Modes.PPC64LE.args_write_r8 s v
  split
  · refine WP.mono (Proof.Modes.PPC64LE.ctr32Seq_wp (Serial.coreSpec .encrypt) rfl
      ((seqPre_of (Serial.core .encrypt) rfl rfl (Serial.coreSpec .encrypt).layout (M := Mode.ctr32Early) rfl hs).write_r8 v)
      (keyArgs_r8 v (keyArgs_of (Serial.core .encrypt) rfl (M := Mode.ctr32Early) rfl hs))) fun _ ⟨h1, h2, h3, _⟩ => ?_
    simp only [Proof.Modes.PPC64LE.iv0, Proof.Modes.PPC64LE.blocks0, eP, eD, eN, eM, cipher_ser] at h2 h3
    refine ⟨Proof.Modes.PPC64LE.abiPreserved_r8 h1, ?_, h3⟩
    rw [Proof.Modes.gcmBlocks_eq, Proof.Modes.gcmBlocks_eq]
    exact h2
  · refine WP.mono (Proof.Modes.PPC64LE.ctr32Wide_wp (dirCoreSpec .encrypt) (lg := 4) rfl (by decide) (by decide)
      (by decide) ((seqPre_of (dirCore .encrypt) rfl rfl (dirCoreSpec .encrypt).layout (M := Mode.ctr32Early) rfl
        hs).write_r8 v)
      (keyArgs_r8 v (keyArgs_of (dirCore .encrypt) rfl (M := Mode.ctr32Early) rfl hs))) fun _ ⟨h1, h2, h3, _⟩ => ?_
    simp only [Proof.Modes.PPC64LE.iv0, Proof.Modes.PPC64LE.blocks0, eP, eD, eN, eM, cipher_enc] at h2 h3
    refine ⟨Proof.Modes.PPC64LE.abiPreserved_r8 h1, ?_, h3⟩
    rw [Proof.Modes.gcmBlocks_eq, Proof.Modes.gcmBlocks_eq]
    exact h2

end VG.Proof.Sm4.PPC64LE.Modes
