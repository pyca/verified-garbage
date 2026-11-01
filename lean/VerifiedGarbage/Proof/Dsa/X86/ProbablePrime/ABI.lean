module

public import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.Enter
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Mont.X86.Compact.Frame
import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.Width
import VerifiedGarbage.Proof.Mont.X86.Compact.EntryArgs
import VerifiedGarbage.Proof.RsaKeyGen.TrialTable32
import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.RsaKeyGen.RandMemory
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Dsa.ProbablePrimeContract

/-! # The shared probable-prime contract on the i686 cdecl ABI -/

@[expose] public section
namespace VG.Proof.Dsa.X86.ProbablePrime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.ProbablePrime

def contract (bits : Nat) : Contract isa :=
  Proof.Dsa.ProbablePrime.contract (layout bits) (abi.withConsts VG.Impl.RsaKeyGen.TrialTable32.consts) 152

def callEnvironment (bits : Nat) (s : State) : Environment where
  bits := bits
  workspace := arg s 0
  capacity := (arg s 1).toNat
  rand := arg s 2
  randLength := (arg s 3).toNat
  used := arg s 4
  table := s.syms VG.Impl.RsaKeyGen.TrialTable32.symbol
  p := s.gpr .esp - 16#32

def callEntropy (s : State) : List Byte := Spec.Rsa.bytesAt s.mem ((arg s 2).setWidth 64) (arg s 3).toNat

def reservedRegion (s : State) : Region := ⟨(s.gpr .esp).setWidth 64 - 152#64, 152⟩

def tableRegionOf (s : State) : Region :=
  ⟨(s.syms VG.Impl.RsaKeyGen.TrialTable32.symbol).setWidth 64, 8192⟩

/-- What the precondition says, in the shape `sig_pre` leaves it. -/
structure CallFacts (bits : Nat) (s : State) : Prop where
  low : 152 ≤ (s.gpr .esp).toNat
  argsFit : (s.gpr .esp).toNat + 4 + 20 ≤ 2 ^ 32
  rdTable : s.rd.drop (s.rd.length - 1) = Abi.constRegions (fun name => (s.syms name).setWidth 64)
    VG.Impl.RsaKeyGen.TrialTable32.consts
  tableHeld : Abi.constsHeld s.mem (fun name => (s.syms name).setWidth 64) VG.Impl.RsaKeyGen.TrialTable32.consts
  tableFar : ∀ t ∈ Abi.constRegions (fun name => (s.syms name).setWidth 64) VG.Impl.RsaKeyGen.TrialTable32.consts,
    t.base.toNat + t.len ≤ 2 ^ 32 ∧ (∀ r ∈ s.wr, t.Disjoint r) ∧
    t.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ∧ t.Disjoint (reservedRegion s)
  tableAligned : ∀ t ∈ Abi.constRegions (fun name => (s.syms name).setWidth 64)
    VG.Impl.RsaKeyGen.TrialTable32.consts, t.base.toNat % 64 = 0
  rdPrefix : s.rd.take (s.rd.length - 1) = [⟨(arg s 2).setWidth 64, (arg s 3).toNat⟩]
  wr : s.wr = [⟨(arg s 0).setWidth 64, (arg s 1).toNat * 8⟩, ⟨(arg s 4).setWidth 64, 8⟩, ⟨argAddr s 0, 20⟩]
  wsRand : (⟨(arg s 0).setWidth 64, (arg s 1).toNat * 8⟩ : Region).Disjoint ⟨(arg s 2).setWidth 64, (arg s 3).toNat⟩
  wsUsed : (⟨(arg s 0).setWidth 64, (arg s 1).toNat * 8⟩ : Region).Disjoint ⟨(arg s 4).setWidth 64, 8⟩
  wsArgs : (⟨(arg s 0).setWidth 64, (arg s 1).toNat * 8⟩ : Region).Disjoint ⟨argAddr s 0, 20⟩
  randUsed : (⟨(arg s 2).setWidth 64, (arg s 3).toNat⟩ : Region).Disjoint ⟨(arg s 4).setWidth 64, 8⟩
  randArgs : (⟨(arg s 2).setWidth 64, (arg s 3).toNat⟩ : Region).Disjoint ⟨argAddr s 0, 20⟩
  usedArgs : (⟨(arg s 4).setWidth 64, 8⟩ : Region).Disjoint ⟨argAddr s 0, 20⟩
  retWs : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨(arg s 0).setWidth 64, (arg s 1).toNat * 8⟩
  retRand : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨(arg s 2).setWidth 64, (arg s 3).toNat⟩
  retUsed : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨(arg s 4).setWidth 64, 8⟩
  retArgs : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨argAddr s 0, 20⟩
  stackWs : (reservedRegion s).Disjoint ⟨(arg s 0).setWidth 64, (arg s 1).toNat * 8⟩
  stackRand : (reservedRegion s).Disjoint ⟨(arg s 2).setWidth 64, (arg s 3).toNat⟩
  stackUsed : (reservedRegion s).Disjoint ⟨(arg s 4).setWidth 64, 8⟩
  stackArgs : (reservedRegion s).Disjoint ⟨argAddr s 0, 20⟩
  wsFit : (arg s 0).toNat + (arg s 1).toNat * 8 ≤ 2 ^ 32
  randFit : (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 32
  usedFit : (arg s 4).toNat + 8 ≤ 2 ^ 32
  room : scratchBytes (width bits) + bits / 8 ≤ 8 * (arg s 1).toNat
  odd : Proof.Dsa.ProbablePrime.candidateAt (layout bits) s.mem ((arg s 0).setWidth 64) % 2 = 1
  length : Spec.Dsa.bitLength (Proof.Dsa.ProbablePrime.candidateAt (layout bits) s.mem ((arg s 0).setWidth 64)) = bits

theorem call_facts {bits : Nat} {s : State} (h : (contract bits).pre s) : CallFacts bits s := by
  sig_pre [contract, Proof.Dsa.ProbablePrime.contract, Proof.Dsa.ProbablePrime.sig,
    abi, argSlots, argVal, argBytes, Abi.withConsts, VG.Impl.RsaKeyGen.TrialTable32.consts, stackBelow] at h
  sig_split h
  constructor <;> try with_reducible assumption
  all_goals dsimp only [reservedRegion, VG.Impl.RsaKeyGen.TrialTable32.consts]
  all_goals with_reducible assumption

end VG.Proof.Dsa.X86.ProbablePrime
