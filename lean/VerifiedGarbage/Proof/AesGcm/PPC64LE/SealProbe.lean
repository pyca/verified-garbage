module

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Contract
public import VerifiedGarbage.Proof.AesGcm.Scratch
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.SigEval

@[expose] public section

namespace VG.Proof.AesGcm.PPC64LE

open VG VG.PPC64LE

def sealSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 10 | .r5 => 0x2000 | .r7 => 0x3000 | .r9 => 0x4000 | _ => 0
  lr := 0
  sp := 0x9000
  mem a := bif Nat.beq a.toNat 0x9061 then 0x50 else bif Nat.beq a.toNat 0x9069 then 0x60 else 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x9060, 16⟩]
  wr := [⟨0x4000, 0⟩, ⟨0x5000, 16⟩, ⟨0x6000, 2560⟩]

theorem probePre : ∀ s, (Proof.AesGcm.sealScratchContract PPC64LE.abi).pre s → sealPPC64LE.pre s := by
  sig_implies_pre [Proof.AesGcm.sealScratchContract, Proof.AesGcm.sealScratchSig, Spec.Gcm.sealPre,
    Spec.Gcm.sealPost, sealPPC64LE, sealPre, onePub, args, rounds, PPC64LE.abi, PPC64LE.argRegs,
    stackArg, stackArgAddr, List.getD, List.range, List.range.loop]

theorem probePost : ∀ s s', (Proof.AesGcm.sealScratchContract PPC64LE.abi).pre s → sealPPC64LE.post s s' → (Proof.AesGcm.sealScratchContract PPC64LE.abi).post s s' := by
  sig_implies_post [Proof.AesGcm.sealScratchContract, Proof.AesGcm.sealScratchSig, Spec.Gcm.sealPre,
    Spec.Gcm.sealPost, sealPPC64LE, sealPre, onePub, args, rounds, PPC64LE.abi, PPC64LE.argRegs,
    stackArg, stackArgAddr, List.getD, List.range, List.range.loop]

theorem probePub : ∀ s₁ s₂, (Proof.AesGcm.sealScratchContract PPC64LE.abi).pre s₁ → (Proof.AesGcm.sealScratchContract PPC64LE.abi).pre s₂ → (Proof.AesGcm.sealScratchContract PPC64LE.abi).pub s₁ s₂ → sealPPC64LE.pub s₁ s₂ := by
  sig_implies_pub [Proof.AesGcm.sealScratchContract, Proof.AesGcm.sealScratchSig, Spec.Gcm.sealPre,
    Spec.Gcm.sealPost, sealPPC64LE, sealPre, onePub, args, rounds, PPC64LE.abi, PPC64LE.argRegs,
    stackArg, stackArgAddr, List.getD, List.range, List.range.loop]

theorem probeSat : ∃ s, (Proof.AesGcm.sealScratchContract PPC64LE.abi).pre s := by
  sig_implies_sat [Proof.AesGcm.sealScratchContract, Proof.AesGcm.sealScratchSig, Spec.Gcm.sealPre,
    Spec.Gcm.sealPost, sealPPC64LE, sealPre, onePub, args, rounds, PPC64LE.abi, PPC64LE.argRegs,
    stackArg, stackArgAddr, List.getD, List.range, List.range.loop]
    [sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using sealSat

end VG.Proof.AesGcm.PPC64LE
