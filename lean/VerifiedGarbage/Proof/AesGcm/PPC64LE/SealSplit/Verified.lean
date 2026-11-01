module

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.SealSplit.Correct
import VerifiedGarbage.Proof.AesGcm.PPC64LE.SealSplit.CT
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.SigEval
import VerifiedGarbage.Proof.Framework.Offset

-- separate module: verification of the source-first scratch entry.
/-! # Verified split-seal scratch implementation -/

@[expose] public section
namespace VG.Proof.AesGcm.PPC64LE.SealSplit
open VG VG.PPC64LE


def sat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 10 | .r5 => 0x2000 | .r7 => 0x3000 | .r9 => 0x7000 | _ => 0
  lr := 0
  sp := 0x9000
  mem a := bif Nat.beq a.toNat 0x9061 then 0x40 else
    bif Nat.beq a.toNat 0x9071 then 0x50 else bif Nat.beq a.toNat 0x9079 then 0x60 else 0
  rd := [⟨0x1000,256⟩,⟨0x2000,0⟩,⟨0x3000,0⟩,⟨0x7000,0⟩,⟨0x9060,32⟩]
  wr := [⟨0x4000,0⟩,⟨0x5000,16⟩,⟨0x6000,2560⟩]


theorem sat_pre : scratchContract.pre sat := by
  sig_eval [scratchContract,Sig.scratchContract,Sig.withScratch,Curry.withScratch,Curry.app,Spec.Gcm.sealSplitSig,
    Spec.Gcm.sealSplitPre,PPC64LE.abi,PPC64LE.argRegs,stackArg,stackArgAddr,List.getD,List.range,List.range.loop,
    stackBelow,sat,Mem.readW,Mem.read]
  sig_and_intros
  all_goals first | rfl | decide | exact Region.disjoint_of_sep (by decide)


theorem scratch_verified [VG.Proof.Gcm.PPC64LE.GhashLaw] [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw] :
    Verified PPC64LE.target Impl.AesGcm.PPC64LE.SealSplit.seal scratchContract :=
  ⟨fun _ hs => scratch_wp hs,scratch_ct,⟨sat,sat_pre⟩⟩

end VG.Proof.AesGcm.PPC64LE.SealSplit
