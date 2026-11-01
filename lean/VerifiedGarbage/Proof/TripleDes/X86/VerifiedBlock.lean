module

import VerifiedGarbage.Proof.TripleDes.X86.BlockCT
public import VerifiedGarbage.Spec.TripleDes.Contract
public import VerifiedGarbage.Proof.TripleDes.Contract
public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Impl.TripleDes.X86.Block
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.TripleDes.X86.FunctionsLit

@[expose] public section

namespace VG.Proof.TripleDes.X86
open VG VG.X86 VG.Impl.TripleDes.X86
open VG.Proof.Rc2.X86 (addr32)

def blockSatState : State where
  gpr r := if r = .esp then 0x4000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x4005 then 0x10 else if a = 0x4009 then 0x20 else if a = 0x400d then 0x30 else 0
  rd := [⟨0x1000, 384⟩, ⟨0x4004, 12⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, 512⟩]

theorem encrypt_verified : Verified target encryptBlock (Proof.TripleDes.encryptBlockContract abi) := by
  refine Verified.of_correct (block_correct .encrypt)
    (encryptBlock_constantTime _ _ (fun _ _ h₁ h₂ hp => blockTaint_agree h₁ h₂ hp)) ?_
  sig_implies [Proof.TripleDes.encryptBlockContract, Proof.TripleDes.blockSig, abi, argSlots, argVal,
    argBytes, addr32, blockContract, blockResult]
    [blockSatState, arg, argAddr, Mem.readW, Mem.read] using blockSatState

theorem decrypt_verified : Verified target decryptBlock (Proof.TripleDes.decryptBlockContract abi) := by
  refine Verified.of_correct (block_correct .decrypt)
    (decryptBlock_constantTime _ _ (fun _ _ h₁ h₂ hp => blockTaint_agree h₁ h₂ hp)) ?_
  sig_implies [Proof.TripleDes.decryptBlockContract, Proof.TripleDes.blockSig, abi, argSlots, argVal,
    argBytes, addr32, blockContract, blockResult]
    [blockSatState, arg, argAddr, Mem.readW, Mem.read] using blockSatState

end VG.Proof.TripleDes.X86
