module
public import VerifiedGarbage.Spec.Dsa.Generate
public import VerifiedGarbage.Proof.Dsa.X86.VerifyingABI

/-! # Resources of the parameter generator's twelve-argument cdecl interface -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86

abbrev argRegion (s : State) (i n : Nat) : Region := ⟨argumentPointer s i, n⟩

structure ParameterABI (s : State) : Prop where
  stackLow : 292 ≤ (s.gpr .esp).toNat
  stackBound : (s.gpr .esp).toNat + 4 + 48 ≤ 2 ^ 32
  rd : s.rd = [argRegion s 4 (arg s 5).toNat, argRegion s 6 (arg s 7).toNat, argRegion s 8 (arg s 9).toNat]
  wr : s.wr = [argRegion s 0 (arg s 1).toNat, argRegion s 10 ((arg s 11).toNat * 8), ⟨argAddr s 0, 48⟩]
  outSeeds : (argRegion s 0 (arg s 1).toNat).Disjoint (argRegion s 4 (arg s 5).toNat)
  outHs : (argRegion s 0 (arg s 1).toNat).Disjoint (argRegion s 6 (arg s 7).toNat)
  outWitnesses : (argRegion s 0 (arg s 1).toNat).Disjoint (argRegion s 8 (arg s 9).toNat)
  outScratch : (argRegion s 0 (arg s 1).toNat).Disjoint (argRegion s 10 ((arg s 11).toNat * 8))
  outArgs : (argRegion s 0 (arg s 1).toNat).Disjoint ⟨argAddr s 0, 48⟩
  seedsScratch : (argRegion s 4 (arg s 5).toNat).Disjoint (argRegion s 10 ((arg s 11).toNat * 8))
  seedsArgs : (argRegion s 4 (arg s 5).toNat).Disjoint ⟨argAddr s 0, 48⟩
  hsScratch : (argRegion s 6 (arg s 7).toNat).Disjoint (argRegion s 10 ((arg s 11).toNat * 8))
  hsArgs : (argRegion s 6 (arg s 7).toNat).Disjoint ⟨argAddr s 0, 48⟩
  witnessesScratch : (argRegion s 8 (arg s 9).toNat).Disjoint (argRegion s 10 ((arg s 11).toNat * 8))
  witnessesArgs : (argRegion s 8 (arg s 9).toNat).Disjoint ⟨argAddr s 0, 48⟩
  scratchArgs : (argRegion s 10 ((arg s 11).toNat * 8)).Disjoint ⟨argAddr s 0, 48⟩
  retOut : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint (argRegion s 0 (arg s 1).toNat)
  stackOut : (⟨(s.gpr .esp).setWidth 64 - 292#64, 292⟩ : Region).Disjoint (argRegion s 0 (arg s 1).toNat)
  outBound : (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32
  retSeeds : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint (argRegion s 4 (arg s 5).toNat)
  stackSeeds : (⟨(s.gpr .esp).setWidth 64 - 292#64, 292⟩ : Region).Disjoint (argRegion s 4 (arg s 5).toNat)
  seedsBound : (arg s 4).toNat + (arg s 5).toNat ≤ 2 ^ 32
  retHs : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint (argRegion s 6 (arg s 7).toNat)
  stackHs : (⟨(s.gpr .esp).setWidth 64 - 292#64, 292⟩ : Region).Disjoint (argRegion s 6 (arg s 7).toNat)
  hsBound : (arg s 6).toNat + (arg s 7).toNat ≤ 2 ^ 32
  retWitnesses : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint (argRegion s 8 (arg s 9).toNat)
  stackWitnesses : (⟨(s.gpr .esp).setWidth 64 - 292#64, 292⟩ : Region).Disjoint (argRegion s 8 (arg s 9).toNat)
  witnessesBound : (arg s 8).toNat + (arg s 9).toNat ≤ 2 ^ 32
  retScratch : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint (argRegion s 10 ((arg s 11).toNat * 8))
  stackScratch : (⟨(s.gpr .esp).setWidth 64 - 292#64, 292⟩ : Region).Disjoint (argRegion s 10 ((arg s 11).toNat * 8))
  scratchBound : (arg s 10).toNat + ((arg s 11).toNat * 8) ≤ 2 ^ 32
  lengths : Spec.Dsa.generationLengthsValid (arg s 2).toNat (arg s 3).toNat
  outLength : (arg s 1).toNat = 2 * (arg s 2).toNat + (arg s 3).toNat
  seedLength : (arg s 5).toNat % (arg s 3).toNat = 0
  hLength : (arg s 7).toNat % (arg s 2).toNat = 0
  scratchLength : Spec.Dsa.generationScratchWords (arg s 2).toNat ≤ (arg s 11).toNat

theorem parameterABI_of {s : State} (h : (Spec.Dsa.generateParametersContract abi 292).pre s) :
    ParameterABI s := by
  sig_pre [Spec.Dsa.generateParametersContract, Spec.Dsa.generateParametersSig, abi, argSlots, argVal, argBytes,
    stackBelow] at h
  sig_split h
  constructor <;> with_reducible assumption
end VG.Proof.Dsa.X86.Generation
