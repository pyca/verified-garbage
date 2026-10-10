import VerifiedGarbage.Proof.TripleDes.X86.Key.ConstantTime
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.TripleDes.Scratch

namespace VG.Proof.TripleDes.X86.Key
open VG VG.X86
open VG.Proof.Rc2.X86 (addr32)

def satState : State where
  gpr r := if r = .esp then 0x4000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x4005 then 0x10 else if a = 0x4008 then 16 else
    if a = 0x400d then 0x20 else if a = 0x4011 then 0x30 else 0
  rd := [⟨0x1000, 16⟩, ⟨0x4004, 16⟩]
  wr := [⟨0x2000, 384⟩, ⟨0x3000, 512⟩]

theorem verified : Verified target Impl.TripleDes.X86.Key.expandKey
    (Proof.TripleDes.expandKeyScratchContract abi) := by
  refine Verified.of_correct expand_correct
    (expandKey_constantTime _ _ (fun _ _ h₁ h₂ hp => keyTaint_agree h₁ h₂ hp)) ?_
  sig_implies [Proof.TripleDes.expandKeyScratchContract, Proof.TripleDes.expandKeyScratchSig, Spec.TripleDes.expandKeyPre, Spec.TripleDes.expandKeyPost, abi, argSlots, argVal,
    argBytes, addr32, contract]
    [satState, arg, argAddr, Mem.readW, Mem.read] using satState

end VG.Proof.TripleDes.X86.Key
