module

import VerifiedGarbage.Proof.Dsa.X86.Generation.Finish
import VerifiedGarbage.Proof.Dsa.X86.Generation.Frame
public import VerifiedGarbage.Spec.Dsa.Generate
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.RsaKeyGen.TrialTable32
public import VerifiedGarbage.Proof.Dsa.X86.Generation.GPart
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Proof.Rsa.X86.DivContext
public import VerifiedGarbage.Spec.Ffdh
public import VerifiedGarbage.TCB.X86.Target

/-! # The generation contract's precondition at the call -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86

/-- The contract, as the registration gives it. -/
abbrev genContract : Contract isa := Spec.Dsa.generateParametersContract
  (abi.withConsts VG.Impl.RsaKeyGen.TrialTable32.consts) 216

def reservedRegion (s : State) : Region := ⟨(s.gpr .esp).setWidth 64 - 216#64, 216⟩

/-- What the precondition says, in the shape `sig_pre` leaves it. -/
structure CallFacts (s : State) : Prop where
  low : 216 ≤ (s.gpr .esp).toNat
  argsFit : (s.gpr .esp).toNat + 4 + 48 ≤ 2 ^ 32
  rdTable : s.rd.drop (s.rd.length - 1) = Abi.constRegions (fun name => (s.syms name).setWidth 64)
    VG.Impl.RsaKeyGen.TrialTable32.consts
  tableHeld : Abi.constsHeld s.mem (fun name => (s.syms name).setWidth 64) VG.Impl.RsaKeyGen.TrialTable32.consts
  tableFar : ∀ t ∈ Abi.constRegions (fun name => (s.syms name).setWidth 64) VG.Impl.RsaKeyGen.TrialTable32.consts,
    t.base.toNat + t.len ≤ 2 ^ 32 ∧ (∀ r ∈ s.wr, t.Disjoint r) ∧
    t.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ∧ t.Disjoint (reservedRegion s)
  rdPrefix : s.rd.take (s.rd.length - 1) = [(⟨(arg s 4).setWidth 64, (arg s 5).toNat⟩ : Region), (⟨(arg s 6).setWidth 64, (arg s 7).toNat⟩ : Region), (⟨(arg s 8).setWidth 64, (arg s 9).toNat⟩ : Region)]
  wr : s.wr = [(⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩ : Region), (⟨(arg s 10).setWidth 64, (arg s 11).toNat * 8⟩ : Region), ⟨argAddr s 0, 48⟩]
  outSeeds : (⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩ : Region).Disjoint (⟨(arg s 4).setWidth 64, (arg s 5).toNat⟩ : Region)
  outHs : (⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩ : Region).Disjoint (⟨(arg s 6).setWidth 64, (arg s 7).toNat⟩ : Region)
  outWit : (⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩ : Region).Disjoint (⟨(arg s 8).setWidth 64, (arg s 9).toNat⟩ : Region)
  outScr : (⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩ : Region).Disjoint (⟨(arg s 10).setWidth 64, (arg s 11).toNat * 8⟩ : Region)
  outArgs : (⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩ : Region).Disjoint ⟨argAddr s 0, 48⟩
  seedsScr : (⟨(arg s 4).setWidth 64, (arg s 5).toNat⟩ : Region).Disjoint (⟨(arg s 10).setWidth 64, (arg s 11).toNat * 8⟩ : Region)
  seedsArgs : (⟨(arg s 4).setWidth 64, (arg s 5).toNat⟩ : Region).Disjoint ⟨argAddr s 0, 48⟩
  hsScr : (⟨(arg s 6).setWidth 64, (arg s 7).toNat⟩ : Region).Disjoint (⟨(arg s 10).setWidth 64, (arg s 11).toNat * 8⟩ : Region)
  hsArgs : (⟨(arg s 6).setWidth 64, (arg s 7).toNat⟩ : Region).Disjoint ⟨argAddr s 0, 48⟩
  witScr : (⟨(arg s 8).setWidth 64, (arg s 9).toNat⟩ : Region).Disjoint (⟨(arg s 10).setWidth 64, (arg s 11).toNat * 8⟩ : Region)
  witArgs : (⟨(arg s 8).setWidth 64, (arg s 9).toNat⟩ : Region).Disjoint ⟨argAddr s 0, 48⟩
  scrArgs : (⟨(arg s 10).setWidth 64, (arg s 11).toNat * 8⟩ : Region).Disjoint ⟨argAddr s 0, 48⟩
  retOut : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint (⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩ : Region)
  retSeeds : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint (⟨(arg s 4).setWidth 64, (arg s 5).toNat⟩ : Region)
  retHs : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint (⟨(arg s 6).setWidth 64, (arg s 7).toNat⟩ : Region)
  retWit : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint (⟨(arg s 8).setWidth 64, (arg s 9).toNat⟩ : Region)
  retScr : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint (⟨(arg s 10).setWidth 64, (arg s 11).toNat * 8⟩ : Region)
  retArgs : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨argAddr s 0, 48⟩
  stackOut : (reservedRegion s).Disjoint (⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩ : Region)
  stackSeeds : (reservedRegion s).Disjoint (⟨(arg s 4).setWidth 64, (arg s 5).toNat⟩ : Region)
  stackHs : (reservedRegion s).Disjoint (⟨(arg s 6).setWidth 64, (arg s 7).toNat⟩ : Region)
  stackWit : (reservedRegion s).Disjoint (⟨(arg s 8).setWidth 64, (arg s 9).toNat⟩ : Region)
  stackScr : (reservedRegion s).Disjoint (⟨(arg s 10).setWidth 64, (arg s 11).toNat * 8⟩ : Region)
  stackArgs : (reservedRegion s).Disjoint ⟨argAddr s 0, 48⟩
  outFit : (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32
  seedsFit : (arg s 4).toNat + (arg s 5).toNat ≤ 2 ^ 32
  hsFit : (arg s 6).toNat + (arg s 7).toNat ≤ 2 ^ 32
  witFit : (arg s 8).toNat + (arg s 9).toNat ≤ 2 ^ 32
  scrFit : (arg s 10).toNat + (arg s 11).toNat * 8 ≤ 2 ^ 32
  lengths : Spec.Dsa.generationLengthsValid (arg s 2).toNat (arg s 3).toNat
  outLen : (arg s 1).toNat = 2 * (arg s 2).toNat + (arg s 3).toNat
  seedsWhole : (arg s 5).toNat % (arg s 3).toNat = 0
  hsWhole : (arg s 7).toNat % (arg s 2).toNat = 0
  room : Spec.Dsa.generationScratchWords (arg s 2).toNat ≤ (arg s 11).toNat

theorem call_facts {s : State} (h : genContract.pre s) : CallFacts s := by
  sig_pre [genContract, Spec.Dsa.generateParametersContract, Spec.Dsa.generateParametersSig,
    abi, argSlots, argVal, argBytes, Abi.withConsts, VG.Impl.RsaKeyGen.TrialTable32.consts, stackBelow] at h
  sig_split h
  constructor <;> try with_reducible assumption
  all_goals dsimp only [reservedRegion, VG.Impl.RsaKeyGen.TrialTable32.consts]
  all_goals with_reducible assumption

end VG.Proof.Dsa.X86.Generation
