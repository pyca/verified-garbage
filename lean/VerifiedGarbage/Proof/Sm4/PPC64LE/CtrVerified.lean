module

public import VerifiedGarbage.Proof.Sm4.PPC64LE.ModesVerified
import VerifiedGarbage.Proof.Sm4.PPC64LE.ModesFrame
public import VerifiedGarbage.Proof.Sm4.Scratch
public import VerifiedGarbage.Impl.Sm4.PPC64LE.Ctr
public import VerifiedGarbage.Spec.Sm4.Ctr
import VerifiedGarbage.Proof.Modes.PPC64LE.Ctr
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchWipe
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sm4.PPC64LE.CtrLit
import VerifiedGarbage.Proof.Sm4.PPC64LE.Lit
import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Sm4.PPC64LE.CallSum
meta import VerifiedGarbage.Proof.Framework.PPC64LE.SlotTaint
meta import VerifiedGarbage.Impl.Sm4.PPC64LE.Ctr
meta import VerifiedGarbage.Proof.Sm4.PPC64LE.CtrLit
meta import VerifiedGarbage.Proof.Sm4.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Sm4.PPC64LE.CallSum
meta import VerifiedGarbage.Proof.Framework.RegSet
meta import VerifiedGarbage.Proof.Sm4.PPC64LE.ModesConstantTime
public import VerifiedGarbage.Impl.StackScratch.PPC64LE
public import VerifiedGarbage.Spec.Ctr
public import VerifiedGarbage.TCB.PPC64LE.Target

/-!
# SM4-CTR on PPC64LE meets its contract

`ctr_verified`: the counter mode of `Proof/Modes/PPC64LE/Ctr.lean` over
SM4's core (`dirCoreSpec .encrypt`), with the working space as the fifth
argument (`modeContract`), meets the contract with a scratch buffer of 408
words (`Proof.Sm4.ctrScratchContract`), and constant time as the other modes
do (`ModesConstantTime.lean`). `ctr_framed`: in its frame, `vg_sm4_ctr`'s
contract.
-/

@[expose] public section

namespace VG.Proof.Sm4.PPC64LE.Modes

open VG VG.PPC64LE VG.Impl.Sm4.PPC64LE VG.Impl.Modes
open VG.Proof.Sm4.PPC64LE (dirCoreSpec modeContract modeTaint modes_agree modeFrameSat)

/-- The data XORed with the encrypted counters, and the next counter. -/
def ctrPost (s s' : State) : Prop :=
  dataAt s'.mem s = Spec.Ctr.crypt (ciph s) (ivAt s.mem s) (dataAt s.mem s) ∧
    ivAt s'.mem s = Spec.Ctr.next (ivAt s.mem s) (s.gpr .r6).toNat

theorem ctr_constantTime {post : State → State → Prop} :
    ConstantTime isa (modeContract 16 post).pre Proof.Sm4.PPC64LE.modePub ctr :=
  VG.Taint.constantTime_of_exists (A := slotTaint) modeTaint modes_agree
    (by taint_decide_sum [prepSum, cryptSum])

theorem ctr_correct (s : State) (hs : (modeContract 16 ctrPost).pre s) :
    ∃ t s', Exec isa ctr s t s' ∧ abiPreserved s s' ∧ (modeContract 16 ctrPost).post s s' :=
  WP.mono (Proof.Modes.PPC64LE.ctr_wp (dirCoreSpec .encrypt) rfl
    (seqPre_of .encrypt (M := Mode.ctr) rfl hs)
    (keyArgs_of .encrypt (M := Mode.ctr) rfl hs))
    fun _ ⟨h1, h2, h3⟩ => by simp only [cipher_enc] at h2 h3; exact ⟨h1, h2, h3⟩

theorem ctr_verified : Verified target ctr (Proof.Sm4.ctrScratchContract abi (slots + 6)) := by
  refine Verified.of_correct ctr_correct ctr_constantTime ?_
  sig_implies [Proof.Sm4.ctrScratchContract, Proof.Sm4.ctrScratchSig, Spec.Sm4.ctrSig, Proof.Sm4.ctrPost,
    abi, argRegs, modeContract, ctrPost, modePub_iff, slots_eq] [modeSat] using modeSat

theorem ctrFrameSat_pre (post : Spec.Sm4.ctrSig.Post PPC64LE.abi.ptrBits) :
    ∃ s, (Spec.Sm4.ctrSig.contract PPC64LE.abi (post := post) (writeArgs := true)
      (stack := 0 + 3296)).pre s := by
  implies_sat [Spec.Sm4.ctrSig, PPC64LE.abi, PPC64LE.argRegs] [modeFrameSat] using modeFrameSat

/-- `vg_sm4_ctr` with its working space on the stack, wiped before returning. -/
theorem ctr_framed :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratchWiped 3296 .r7 408 ctr)
      (Spec.Sm4.ctrContract PPC64LE.abi 3296) :=
  PPC64LE.Verified.stackScratchWiped (sig := Spec.Sm4.ctrSig) (nm := "scratch") (e := .u64)
    (n := 408) (post := Proof.Sm4.ctrPost PPC64LE.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 3296) (words := 408) ctr_verified (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.Sm4.ctrPost_local _) (Proof.Sm4.ctrPostOut_local _) (ctrFrameSat_pre _)

end VG.Proof.Sm4.PPC64LE.Modes
