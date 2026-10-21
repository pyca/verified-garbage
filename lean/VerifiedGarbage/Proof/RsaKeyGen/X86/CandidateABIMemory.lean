module

import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateABIArgs
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateBody
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateMemory
import VerifiedGarbage.Proof.RsaKeyGen.RandMemory
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Mont.X86.Compact.Frame
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateABI
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateABIRegions
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateABITable
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateABIValid

/-! # Saving registers retains the contract's original input snapshots and static table -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86

def callEBytes (s : State) : List Byte := Spec.Rsa.bytesAt s.mem ((arg s 3).setWidth 64) (arg s 4).toNat
def callPBytes (s : State) : List Byte := Spec.Rsa.bytesAt s.mem ((arg s 5).setWidth 64) (arg s 6).toNat
def callEntropy (s : State) : List Byte := Spec.Rsa.bytesAt s.mem ((arg s 7).setWidth 64) (arg s 8).toNat

theorem call_memory {s : State} (h : contract.pre s) :
    MemoryFacts (callEnvironment s) (callEBytes s) (callPBytes s) (callEntropy s) s := by
  have A := call_layout h
  have D := call_separation h
  have read (r : Region) (mem : r ∈ (callEnvironment s).readRegions) : InRegions (s.rd ++ s.wr) r.base r.len :=
    ⟨r, List.mem_append_left _ (by rw [A.readRegions]; exact mem), Region.contains_self _ _⟩
  refine ⟨read (callEnvironment s).exponentRegion List.mem_cons_self, read (callEnvironment s).otherRegion (List.mem_cons_of_mem _ List.mem_cons_self),
    read (callEnvironment s).randRegion (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)),
    read (callEnvironment s).tableRegion (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))),
    rfl, rfl, rfl, D.tableWords, rfl⟩

theorem entry_memory {s : State} (h : contract.pre s) :
    MemoryFacts (callEnvironment s) (callEBytes s) (callPBytes s) (callEntropy s) (Compact.entered s) := by
  have A := call_layout h
  have v := call_valid h
  have M := call_memory h
  have fit : 16 ≤ (s.gpr .esp).toNat := by have := A.low; omega
  have F : Frame [(⟨(callEnvironment s).p.setWidth 64, 16⟩ : Region)] s.mem (Compact.entered s).mem :=
    pushed_frame (rs := Compact.savedRegisters) (by decide) fit
  have read {a : Addr} {n : Nat} (R : InRegions (s.rd ++ s.wr) a n) :
      InRegions ((Compact.entered s).rd ++ (Compact.entered s).wr) a n := by
    obtain ⟨r, mem, contains⟩ := R
    refine ⟨r, ?_, contains⟩
    change r ∈ s.rd ++ (below (s.gpr .esp) 16 :: s.wr)
    exact (List.mem_append.mp mem).elim (List.mem_append_left _) (fun member => List.mem_append_right _ (List.mem_cons_of_mem _ member))
  have bytes (r : Region) (mem : r ∈ (callEnvironment s).readRegions) :
      Spec.Rsa.bytesAt (Compact.entered s).mem r.base r.len = Spec.Rsa.bytesAt s.mem r.base r.len :=
    VG.Proof.RsaKeyGen.frame_bytesAt F (by
      intro R member; obtain rfl := List.mem_singleton.mp member
      exact v.savedFar r (List.mem_append_right _ mem)) (v.readFit mem)
  refine ⟨read M.exponentRead, read M.otherRead, read M.randRead, read M.tableRead,
    bytes (callEnvironment s).exponentRegion List.mem_cons_self, bytes (callEnvironment s).otherRegion (List.mem_cons_of_mem _ List.mem_cons_self),
    bytes (callEnvironment s).randRegion (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)), ?_, rfl⟩
  intro i index
  have tableMem : (callEnvironment s).tableRegion ∈ (callEnvironment s).readRegions :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have same := F.readW (r := (callEnvironment s).tableRegion) (w := 64)
    (a := off ((callEnvironment s).table.setWidth 64) (8 * i))
    (Offset.contains_base _ (by change 8 * i + 8 ≤ 8192; omega) (by omega))
    (by intro r mem; obtain rfl := List.mem_singleton.mp mem; exact v.savedFar _ (List.mem_append_right _ tableMem)) (by decide)
  exact same.trans (M.table i index)

theorem entry_input {s : State} (h : contract.pre s) :
    EntryInput (callEnvironment s) (callEBytes s) (callPBytes s) (callEntropy s) (Compact.entered s) := by
  have A := call_layout h
  have v := call_valid h
  refine ⟨entry_arguments h, ?_, ?_, entry_memory h⟩
  · change InRegions (below (s.gpr .esp) 16 :: s.wr) (callEnvironment s).outRegion.base (callEnvironment s).outRegion.len
    exact ⟨_, List.mem_cons_of_mem _ (A.writeMember List.mem_cons_self), Region.contains_self _ _⟩
  · refine ⟨?_, ?_⟩
    · change (callEnvironment s).usedRegion ∈ below (s.gpr .esp) 16 :: s.wr
      exact List.mem_cons_of_mem _ (A.writeMember (List.mem_cons_of_mem _ List.mem_cons_self))
    · change ((arg s 2).setWidth 64).toNat + 8 ≤ 2 ^ 32
      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans (arg s 2).isLt (by decide))]
      exact v.usedFit

end VG.Proof.RsaKeyGen.X86.Candidate
