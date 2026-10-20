module

public import VerifiedGarbage.Proof.Sm4.Arm.ModeCore
public import VerifiedGarbage.Proof.Sm4.Scratch
import VerifiedGarbage.Proof.Modes.Arm.Ctr
import VerifiedGarbage.Proof.Framework.Arm.StackScratchWipe
public import VerifiedGarbage.Impl.Sm4.Arm.Ctr
public import VerifiedGarbage.Proof.Modes.Arm.SeqCT
import VerifiedGarbage.Proof.Modes.Arm.OfbCfb
import VerifiedGarbage.Proof.Modes.Arm.Cbc
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Sm4.Arm.ModeCore
meta import VerifiedGarbage.Proof.Sm4.Scratch
meta import VerifiedGarbage.Proof.Modes.Arm.Ctr
meta import VerifiedGarbage.Proof.Framework.Arm.StackScratchWipe
meta import VerifiedGarbage.Impl.Sm4.Arm.Ctr
meta import VerifiedGarbage.Proof.Modes.Arm.SeqCT
meta import VerifiedGarbage.Proof.Modes.Arm.OfbCfb
meta import VerifiedGarbage.Proof.Modes.Arm.Cbc
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# SM4-CTR on ARMv7 meets its contract

The generic CTR one block at a time over SM4's ECB encryption
(`Proof.Modes.Arm.seq_verified` with `ecbSpec .encrypt`) meets the contract
with a scratch buffer of 9 64-bit words (`Proof.Sm4.ctrScratchContract`), with the
1480 bytes of stack the ECB function uses; the `ctr_framed` theorem keeps the
buffer on the stack, zeroed on return: 80 bytes more.
-/

@[expose] public section

namespace VG.Proof.Sm4.Arm

open VG VG.Arm VG.Impl.Sm4.Arm VG.Impl.Modes.Arm VG.Proof.Modes.Arm

/-- A state satisfying the precondition with the scratch buffer (one block at
`0x3000`), the IV read and written. -/
def ctrSat (len : Nat) : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | .r3 => 1 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 128⟩, ⟨0x8000, 4⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x3000, len⟩, ⟨0, 72⟩]

/-- A state satisfying the functions' precondition. -/
def ctrFrameState (len : Nat) : State := { ctrSat len with rd := [⟨0x1000, 128⟩], wr := [⟨0x2000, 16⟩, ⟨0x3000, len⟩] }

theorem ctrTaint : SeqTaint (ecbCore .encrypt) VG.Impl.Modes.Arm.ctr :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

theorem ctr_implies : (seqArm (ecbCore .encrypt) (ecbSpec .encrypt) VG.Impl.Modes.Arm.ctr).Implies
    (Proof.Sm4.ctrScratchContract Arm.abi 9 1480) where
  pre s h := seqArm_pre_rw rfl (len := (· * 16)) (fun n => rfl) (by
    sig_pre [Proof.Sm4.ctrScratchContract, Proof.Sm4.ctrScratchSig, Spec.Sm4.ctrSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    exact h)
  post s s' _ h := by
    sig_post [Proof.Sm4.ctrScratchContract, Proof.Sm4.ctrScratchSig, Proof.Sm4.ctrPost, Spec.Sm4.ctrSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    have e := ctr_post h
    obtain ⟨e1, e2, e3, -, -⟩ := args_plain (c := ecbCore .encrypt) rfl s
    simp only [show (ecbCore .encrypt).bs = 16 from rfl, e1, e2, e3] at e
    simp only [ecbSpec, dirCipher, State.addr, VG.Proof.Modes.blocksOf_16] at e
    exact e
  pub s₁ s₂ _ _ h := by
    sig_pub [Proof.Sm4.ctrScratchContract, Proof.Sm4.ctrScratchSig, Spec.Sm4.ctrSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    exact seqArm_pub rfl h
  sat := by
    sig_implies_sat [Proof.Sm4.ctrScratchContract, Proof.Sm4.ctrScratchSig, Spec.Sm4.ctrSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
      Arm.State.addr] [ctrSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using ctrSat 16

theorem ctr_verified : Verified Arm.target ctr (Proof.Sm4.ctrScratchContract Arm.abi 9 1480) :=
  seq_verified (ecbSpec .encrypt) (ctr_ok _ rfl) ctrTaint ctr_implies

theorem ctrFrameSat : ∃ s, (Spec.Sm4.ctrContract Arm.abi 1560).pre s := by
  implies_sat [Spec.Sm4.ctrContract, Spec.Sm4.ctrSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
    Arm.State.addr] [ctrFrameState, ctrSat] using ctrFrameState 16

/-- `ctr`, with its scratch buffer on the stack (zeroed on return). -/
theorem ctr_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratchWiped 80 0 18 ctr) (Spec.Sm4.ctrContract Arm.abi 1560) :=
  Arm.Verified.stackScratchWiped (sig := Spec.Sm4.ctrSig) (nm := "scratch") (e := .u64) (n := 9)
    (post := Proof.Sm4.ctrPost Arm.abi.ptrBits) (wa := true) (stack := 1480) (m := 0) (bytes := 80)
    ctr_verified (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Sm4.ctrPost_local _)
    (Proof.Sm4.ctrPostOut_local _) ctrFrameSat

end VG.Proof.Sm4.Arm
