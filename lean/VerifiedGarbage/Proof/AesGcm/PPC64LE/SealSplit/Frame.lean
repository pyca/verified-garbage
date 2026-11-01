module

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.SealSplit.Verified
public import VerifiedGarbage.Impl.StackScratch.PPC64LE.Args
public import VerifiedGarbage.Proof.Gcm.OutOfPlaceContract
import VerifiedGarbage.Proof.AesGcm.ScratchSplit
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchArgs
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.SigEval
import VerifiedGarbage.Proof.Framework.Offset

-- separate module: the source-first public API keeps its workspace on the stack.
/-! # Framed POWER8 split seal -/

@[expose] public section
namespace VG.Proof.AesGcm.PPC64LE.SealSplit
open VG VG.PPC64LE


def frameSat : State := {sat with
  rd := [⟨0x1000,256⟩,⟨0x2000,0⟩,⟨0x3000,0⟩,⟨0x7000,0⟩,⟨0x9060,24⟩]
  wr := [⟨0x4000,0⟩,⟨0x5000,16⟩]}


theorem frameSat_pre : ∃ s, (Proof.Gcm.sealSplitContract PPC64LE.abi 2800).pre s := by
  refine ⟨frameSat,?_⟩
  sig_eval [Proof.Gcm.sealSplitContract,Proof.Gcm.sealSplitSig,Proof.Gcm.sealSplitPre,PPC64LE.abi,PPC64LE.argRegs,
    stackArg,stackArgAddr,List.getD,List.range,List.range.loop,stackBelow,frameSat,sat,Mem.readW,Mem.read]
  sig_and_intros
  all_goals first | rfl | decide | exact Region.disjoint_of_sep (by decide)


theorem framed [VG.Proof.Gcm.PPC64LE.GhashLaw] [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw] :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratchArgs 2688 3 Impl.AesGcm.PPC64LE.SealSplit.seal)
      (Proof.Gcm.sealSplitContract PPC64LE.abi 2800) :=
  PPC64LE.Verified.stackScratchArgs (sig := Proof.Gcm.sealSplitSig) (nm := "work") (e := .u64) (n := 320)
    (pre := Proof.Gcm.sealSplitPre PPC64LE.abi.ptrBits) (post := Proof.Gcm.sealSplitPost PPC64LE.abi.ptrBits)
    (wa := true) (stack := 112) (bytes := 2688) (m := 3) scratch_verified (by decide) (by decide)
    (Proof.AesGcm.sealSplitPre_local _) (Proof.AesGcm.sealSplitPost_local _) frameSat_pre

end VG.Proof.AesGcm.PPC64LE.SealSplit
