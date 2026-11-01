module

public import VerifiedGarbage.Proof.TripleDes.PPC64LE.Pre
public import VerifiedGarbage.Spec.TripleDes.Contract
public import VerifiedGarbage.Proof.TripleDes.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.TripleDes.PPC64LE.FunctionsLit
import VerifiedGarbage.Proof.TripleDes.PPC64LE.RoundLit

@[expose] public section

namespace VG.Proof.TripleDes.PPC64LE

open VG VG.PPC64LE VG.Impl.TripleDes.PPC64LE
open VG.Spec.TripleDes (Direction)

theorem block_gprCorrect (d : Direction) (s : State) (hs : (blockContract d).pre s) :
    WP isa (block d) s (fun s' => (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧
      (blockContract d).post s s') := by
  have hp := headPre_of_contract d s hs
  have hwrite : InRegions s.wr (s.gpr .r4) 8 := by
    rw [hs.2.1]
    exact ⟨⟨s.gpr .r4, 8⟩, by simp, Region.contains_self _ _⟩
  apply WP.mono (block_ok (Spec.TripleDes.scheduleAt s.mem (s.gpr .r3)) (s.gpr .r3) d s hp hwrite)
  intro s' hpost
  refine ⟨?_, hpost.result⟩
  intro r hr
  have hkeep : ∀ q ∈ preserved, q ∈ savedRegs ∨ q ∈ loadKept := by decide
  rcases hkeep r hr with h | h
  · exact hpost.saved r h
  · exact hpost.regs r h

theorem encrypt_correct (s : State) (hs : (blockContract .encrypt).pre s) :
    ∃ t s', Exec isa encryptBlock s t s' ∧ abiPreserved s s' ∧
      (blockContract .encrypt).post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := block_gprCorrect .encrypt s hs
  change Exec isa encryptBlock s t s' at he
  exact ⟨t, s', he, ⟨ha, Exec.sp he, Exec.lr he (by lit_decide) (by lit_decide)⟩, hp⟩

theorem decrypt_correct (s : State) (hs : (blockContract .decrypt).pre s) :
    ∃ t s', Exec isa decryptBlock s t s' ∧ abiPreserved s s' ∧
      (blockContract .decrypt).post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := block_gprCorrect .decrypt s hs
  change Exec isa decryptBlock s t s' at he
  exact ⟨t, s', he, ⟨ha, Exec.sp he, Exec.lr he (by lit_decide) (by lit_decide)⟩, hp⟩

def satState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 0x3000 | _ => 0
  lr := 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x1000, 384⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, 512⟩]

theorem publicRegs_three (s t : State) : PublicRegs [.r3, .r4, .r5] s t ↔
    s.sp = t.sp ∧ s.gpr .r3 = t.gpr .r3 ∧ s.gpr .r4 = t.gpr .r4 ∧ s.gpr .r5 = t.gpr .r5 := by
  simp [PublicRegs]

theorem encrypt_verified : Verified target encryptBlock (Proof.TripleDes.encryptBlockContract abi) := by
  refine Verified.of_correct encrypt_correct
    (encryptBlock_constantTime _) ?_
  sig_implies [Proof.TripleDes.encryptBlockContract, Proof.TripleDes.blockSig, abi, argRegs,
    blockContract, publicRegs_three, blockResult] [satState] using satState

theorem decrypt_verified : Verified target decryptBlock (Proof.TripleDes.decryptBlockContract abi) := by
  refine Verified.of_correct decrypt_correct
    (decryptBlock_constantTime _) ?_
  sig_implies [Proof.TripleDes.decryptBlockContract, Proof.TripleDes.blockSig, abi, argRegs,
    blockContract, publicRegs_three, blockResult] [satState] using satState

end VG.Proof.TripleDes.PPC64LE
