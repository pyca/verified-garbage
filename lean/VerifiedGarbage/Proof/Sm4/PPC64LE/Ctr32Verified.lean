module

import VerifiedGarbage.Proof.Sm4.PPC64LE.ModesVerified
import VerifiedGarbage.Proof.Sm4.PPC64LE.ModesFrame
public import VerifiedGarbage.Proof.Sm4.Ctr32Scratch
public import VerifiedGarbage.Impl.Sm4.PPC64LE.Ctr32
public import VerifiedGarbage.Spec.Sm4.Gcm
public import VerifiedGarbage.Proof.Sm4.Contract
import VerifiedGarbage.Proof.Modes.PPC64LE.Ctr32
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

`ctr32_verified`: the counter mode of `Proof/Modes/PPC64LE/Ctr32.lean` over
SM4's core (`dirCoreSpec .encrypt`), with the working space as the fifth
argument (`modeContract`), meets the contract with a scratch buffer of 408
words (`Proof.Sm4.ctr32ScratchContract`), and constant time as the other
modes do (`ModesConstantTime.lean`). `ctr32_framed`: in its frame,
`vg_sm4_ctr32`'s contract.
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
    ∃ t s', Exec isa ctr32 s t s' ∧ abiPreserved s s' ∧ (modeContract 16 ctr32Post).post s s' :=
  WP.mono (Proof.Modes.PPC64LE.ctr32_wp (dirCoreSpec .encrypt) rfl
    (seqPre_of .encrypt (M := Mode.ctr32) rfl hs)
    (keyArgs_of .encrypt (M := Mode.ctr32) rfl hs))
    fun _ ⟨h1, h2, h3⟩ => by
      simp only [cipher_enc] at h2 h3
      refine ⟨h1, ?_, h3⟩
      rw [Proof.Modes.gcmBlocks_eq, Proof.Modes.gcmBlocks_eq]
      exact h2

theorem ctr32_verified : Verified target ctr32 (Proof.Sm4.ctr32ScratchContract abi (slots + 6)) := by
  refine Verified.of_correct ctr32_correct ctr32_constantTime ?_
  sig_implies [Proof.Sm4.ctr32ScratchContract, Proof.Sm4.ctr32ScratchSig, Proof.Sm4.ctr32Sig,
    Proof.Sm4.ctr32Post, abi, argRegs, modeContract, ctr32Post, modePub_iff, slots_eq] [modeSat] using modeSat

theorem ctr32FrameSat_pre (post : Proof.Sm4.ctr32Sig.Post PPC64LE.abi.ptrBits) :
    ∃ s, (Proof.Sm4.ctr32Sig.contract PPC64LE.abi (post := post) (writeArgs := true)
      (stack := 0 + 3296)).pre s := by
  implies_sat [Proof.Sm4.ctr32Sig, PPC64LE.abi, PPC64LE.argRegs] [modeFrameSat] using modeFrameSat

/-- `vg_sm4_ctr32` with its working space on the stack, wiped before returning. -/
theorem ctr32_framed :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratchWiped 3296 .r7 408 ctr32)
      (Proof.Sm4.ctr32Contract PPC64LE.abi 3296) :=
  PPC64LE.Verified.stackScratchWiped (sig := Proof.Sm4.ctr32Sig) (nm := "scratch") (e := .u64)
    (n := 408) (post := Proof.Sm4.ctr32Post PPC64LE.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 3296) (words := 408) ctr32_verified (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.Sm4.ctr32Post_local _) (Proof.Sm4.ctr32PostOut_local _) (ctr32FrameSat_pre _)

end VG.Proof.Sm4.PPC64LE.Modes
