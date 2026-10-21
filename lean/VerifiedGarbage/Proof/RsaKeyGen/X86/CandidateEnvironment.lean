module

import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateGeometry
import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveContext
public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
public import VerifiedGarbage.Impl.RsaKeyGen.TrialTable32
public import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Proof.MillerRabin.X86.Context
public import VerifiedGarbage.Spec.RsaKeyGen.Contract
public import Init.Data.BitVec.Basic
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Mont.X86.Words

/-! # Public candidate geometry and disjoint memory regions at the native body entry -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86

structure Environment where
  workspace : BitVec 32
  capacity : Nat
  out : BitVec 32
  used : BitVec 32
  exponent : BitVec 32
  other : BitVec 32
  rand : BitVec 32
  table : BitVec 32
  length : Nat
  exponentLength : Nat
  otherLength : Nat
  randLength : Nat
  p : BitVec 32

def Environment.base (E : Environment) : Addr := E.workspace.setWidth 64
def Environment.size (E : Environment) : Nat := 8 * E.capacity
def Environment.width (E : Environment) : Nat := E.length / 8
def Environment.geometry (E : Environment) : Geometry := ⟨E.base, E.size, E.width⟩
def Environment.workspaceRegion (E : Environment) : Region := ⟨E.base, E.size⟩
def Environment.outRegion (E : Environment) : Region := ⟨E.out.setWidth 64, E.length⟩
def Environment.usedRegion (E : Environment) : Region := ⟨E.used.setWidth 64, 8⟩
def Environment.exponentRegion (E : Environment) : Region := ⟨E.exponent.setWidth 64, E.exponentLength⟩
def Environment.otherRegion (E : Environment) : Region := ⟨E.other.setWidth 64, E.otherLength⟩
def Environment.randRegion (E : Environment) : Region := ⟨E.rand.setWidth 64, E.randLength⟩
def Environment.tableRegion (E : Environment) : Region := ⟨E.table.setWidth 64, 8192⟩
def Environment.writeRegions (E : Environment) : List Region := [E.outRegion, E.usedRegion, E.workspaceRegion]
def Environment.readRegions (E : Environment) : List Region := [E.exponentRegion, E.otherRegion, E.randRegion, E.tableRegion]

def Environment.argument (E : Environment) : Nat → BitVec 32
  | 0 => E.out
  | 1 => BitVec.ofNat 32 E.length
  | 2 => E.used
  | 3 => E.exponent
  | 4 => BitVec.ofNat 32 E.exponentLength
  | 5 => E.other
  | 6 => BitVec.ofNat 32 E.otherLength
  | 7 => E.rand
  | 8 => BitVec.ofNat 32 E.randLength
  | 9 => E.workspace
  | _ => BitVec.ofNat 32 E.capacity

structure Environment.Valid (E : Environment) : Prop where
  length : Spec.RsaKeyGen.primeLenValid E.length
  exponentLength : 1 ≤ E.exponentLength ∧ E.exponentLength ≤ 8
  otherLength : E.otherLength = 0 ∨ E.otherLength = E.length
  capacity : Spec.Rsa.scratchWords E.length ≤ E.capacity
  workspaceFit : E.workspace.toNat + E.size ≤ 2 ^ 32
  outFit : E.out.toNat + E.length ≤ 2 ^ 32
  usedFit : E.used.toNat + 8 ≤ 2 ^ 32
  exponentFit : E.exponent.toNat + E.exponentLength ≤ 2 ^ 32
  otherFit : E.other.toNat + E.otherLength ≤ 2 ^ 32
  randFit : E.rand.toNat + E.randLength ≤ 2 ^ 32
  randLengthFit : E.randLength < 2 ^ 32
  tableFit : E.table.toNat + 8192 ≤ 2 ^ 32
  low : 96 ≤ E.p.toNat
  argsFit : E.p.toNat + 64 ≤ 2 ^ 32
  workspaceStack : E.p.toNat ≤ E.base.toNat ∨ E.base.toNat + E.size + 96 ≤ E.p.toNat
  savedFar : ∀ r ∈ E.writeRegions ++ E.readRegions, r.Disjoint ⟨E.p.setWidth 64, 16⟩
  argsFar : (⟨(E.p + 20#32).setWidth 64, 44⟩ : Region).Disjoint E.workspaceRegion
  outUsed : E.outRegion.Disjoint E.usedRegion
  outWorkspace : E.outRegion.Disjoint E.workspaceRegion
  usedWorkspace : E.usedRegion.Disjoint E.workspaceRegion
  readWrite : ∀ r ∈ E.readRegions, ∀ R ∈ E.writeRegions, r.Disjoint R
  stackFar : ∀ r ∈ E.writeRegions ++ E.readRegions, r.Disjoint (below E.p 96)

theorem Environment.Valid.geometry {E : Environment} (v : E.Valid) : E.geometry.Valid :=
  CandidateGeometry.geometry_valid v.length v.capacity

theorem Environment.Valid.length_eq {E : Environment} (v : E.Valid) : 8 * E.width = E.length :=
  CandidateGeometry.length_eq v.length

theorem Environment.Valid.width_bounds {E : Environment} (v : E.Valid) : 4 ≤ E.width ∧ E.width ≤ 64 :=
  CandidateGeometry.width_bounds v.length

theorem Environment.Valid.capacityFit {E : Environment} (v : E.Valid) : E.capacity < 2 ^ 32 := by
  have fit := v.workspaceFit
  unfold Environment.size at fit
  omega

theorem Environment.Valid.readWorkspace {E : Environment} (v : E.Valid) {r : Region} (mem : r ∈ E.readRegions) :
    r.Disjoint E.workspaceRegion := v.readWrite r mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))

def MutableFrame (E : Environment) (m m' : Mem) : Prop := Frame (E.writeRegions ++ [below E.p 96]) m m'

def WorkFrame (E : Environment) (m m' : Mem) : Prop := Frame [E.workspaceRegion, below E.p 96] m m'

structure MemoryFacts (E : Environment) (eBytes pBytes entropy : List Byte) (s : State) : Prop where
  exponentRead : InRegions (s.rd ++ s.wr) (E.exponent.setWidth 64) E.exponentLength
  otherRead : InRegions (s.rd ++ s.wr) (E.other.setWidth 64) E.otherLength
  randRead : InRegions (s.rd ++ s.wr) (E.rand.setWidth 64) E.randLength
  tableRead : InRegions (s.rd ++ s.wr) (E.table.setWidth 64) 8192
  exponentBytes : Spec.Rsa.bytesAt s.mem (E.exponent.setWidth 64) E.exponentLength = eBytes
  otherBytes : Spec.Rsa.bytesAt s.mem (E.other.setWidth 64) E.otherLength = pBytes
  entropy : Spec.Rsa.bytesAt s.mem (E.rand.setWidth 64) E.randLength = entropy
  table : ∀ i < 1024, s.mem.readW (off (E.table.setWidth 64) (8 * i)) 64 =
    BitVec.ofNat 64 (VG.Impl.RsaKeyGen.TrialTable32.entry i)
  symbol : s.syms VG.Impl.RsaKeyGen.TrialTable32.symbol = E.table

structure Input (E : Environment) (eBytes pBytes entropy : List Byte) (s : State) : Prop where
  scratch : Scr s E.base E.size
  stack : s.gpr .esp = E.p
  header : ∀ i < 11, s.mem.readW (off E.base (4 * i)) 32 = E.argument i
  usedPointer : s.mem.readW (off E.base 44) 32 = E.used
  outWrite : InRegions s.wr (E.out.setWidth 64) E.length
  usedWrite : VG.Proof.Mont.X86.Rt.Ws s (E.used.setWidth 64) 8
  memory : MemoryFacts E eBytes pBytes entropy s

end VG.Proof.RsaKeyGen.X86.Candidate
