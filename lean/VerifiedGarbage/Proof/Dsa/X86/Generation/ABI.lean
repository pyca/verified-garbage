module

public import VerifiedGarbage.Spec.Dsa.ParameterSearchContract
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.RsaKeyGen.TrialTable32
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Proof.Rsa.X86.DivContext
public import VerifiedGarbage.Spec.Ffdh
public import VerifiedGarbage.TCB.X86.Target

/-! # The generation contract's precondition at the call -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86

/-- The contract, as the registration gives it. -/
abbrev genContract : Contract isa := Spec.Dsa.parameterSearchContract
  (abi.withConsts VG.Impl.RsaKeyGen.TrialTable32.consts) 216

def reservedRegion (s : State) : Region := ⟨(s.gpr .esp).setWidth 64 - 216#64, 216⟩

/-- The modulus's width, `state[1]`. -/
abbrev pLenOf (s : State) : Nat := (s.mem.readW (BitVec.setWidth 64 (arg s 7) + 8) 64).toNat

/-- What the precondition says, in the shape `sig_pre` leaves it. -/
structure CallFacts (s : State) : Prop where
  low : 216 ≤ (s.gpr .esp).toNat
  argsFit : (s.gpr .esp).toNat + 4 + 32 ≤ 2 ^ 32
  rdTable : s.rd.drop (s.rd.length - 1) = Abi.constRegions (fun name => (s.syms name).setWidth 64)
    VG.Impl.RsaKeyGen.TrialTable32.consts
  tableHeld : Abi.constsHeld s.mem (fun name => (s.syms name).setWidth 64) VG.Impl.RsaKeyGen.TrialTable32.consts
  tableFar : ∀ t ∈ Abi.constRegions (fun name => (s.syms name).setWidth 64) VG.Impl.RsaKeyGen.TrialTable32.consts,
    t.base.toNat + t.len ≤ 2 ^ 32 ∧ (∀ r ∈ s.wr, t.Disjoint r) ∧
    t.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ∧ t.Disjoint (reservedRegion s)
  tableAligned : ∀ t ∈ Abi.constRegions (fun name => (s.syms name).setWidth 64)
    VG.Impl.RsaKeyGen.TrialTable32.consts, t.base.toNat % 64 = 0
  rdPrefix : s.rd.take (s.rd.length - 1) = [(⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩ : Region)]
  wr : s.wr = [(⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩ : Region), ⟨(arg s 2).setWidth 64, 8⟩,
    ⟨(arg s 5).setWidth 64, (arg s 6).toNat * 8⟩, ⟨(arg s 7).setWidth 64, 32⟩, ⟨argAddr s 0, 32⟩]
  outUsed : (⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩ : Region).Disjoint ⟨(arg s 2).setWidth 64, 8⟩
  outRand : (⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩ : Region).Disjoint ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩
  outScr : (⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩ : Region).Disjoint
    ⟨(arg s 5).setWidth 64, (arg s 6).toNat * 8⟩
  outSt : (⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩ : Region).Disjoint ⟨(arg s 7).setWidth 64, 32⟩
  outArgs : (⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩ : Region).Disjoint ⟨argAddr s 0, 32⟩
  usedRand : (⟨(arg s 2).setWidth 64, 8⟩ : Region).Disjoint ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩
  usedScr : (⟨(arg s 2).setWidth 64, 8⟩ : Region).Disjoint ⟨(arg s 5).setWidth 64, (arg s 6).toNat * 8⟩
  usedSt : (⟨(arg s 2).setWidth 64, 8⟩ : Region).Disjoint ⟨(arg s 7).setWidth 64, 32⟩
  usedArgs : (⟨(arg s 2).setWidth 64, 8⟩ : Region).Disjoint ⟨argAddr s 0, 32⟩
  randScr : (⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩ : Region).Disjoint
    ⟨(arg s 5).setWidth 64, (arg s 6).toNat * 8⟩
  randSt : (⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩ : Region).Disjoint ⟨(arg s 7).setWidth 64, 32⟩
  randArgs : (⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩ : Region).Disjoint ⟨argAddr s 0, 32⟩
  scrSt : (⟨(arg s 5).setWidth 64, (arg s 6).toNat * 8⟩ : Region).Disjoint ⟨(arg s 7).setWidth 64, 32⟩
  scrArgs : (⟨(arg s 5).setWidth 64, (arg s 6).toNat * 8⟩ : Region).Disjoint ⟨argAddr s 0, 32⟩
  stArgs : (⟨(arg s 7).setWidth 64, 32⟩ : Region).Disjoint ⟨argAddr s 0, 32⟩
  retOut : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩
  retUsed : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨(arg s 2).setWidth 64, 8⟩
  retRand : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩
  retScr : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨(arg s 5).setWidth 64, (arg s 6).toNat * 8⟩
  retSt : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨(arg s 7).setWidth 64, 32⟩
  retArgs : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨argAddr s 0, 32⟩
  stackOut : (reservedRegion s).Disjoint ⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩
  stackUsed : (reservedRegion s).Disjoint ⟨(arg s 2).setWidth 64, 8⟩
  stackRand : (reservedRegion s).Disjoint ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩
  stackScr : (reservedRegion s).Disjoint ⟨(arg s 5).setWidth 64, (arg s 6).toNat * 8⟩
  stackSt : (reservedRegion s).Disjoint ⟨(arg s 7).setWidth 64, 32⟩
  stackArgs : (reservedRegion s).Disjoint ⟨argAddr s 0, 32⟩
  outFit : (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32
  usedFit : (arg s 2).toNat + 8 ≤ 2 ^ 32
  randFit : (arg s 3).toNat + (arg s 4).toNat ≤ 2 ^ 32
  scrFit : (arg s 5).toNat + (arg s 6).toNat * 8 ≤ 2 ^ 32
  stFit : (arg s 7).toNat + 32 ≤ 2 ^ 32
  pValid : Spec.Dsa.generationPLenValid (pLenOf s) = true
  outLen : (arg s 1).toNat = 2 * pLenOf s + Spec.Dsa.generationQLen (pLenOf s)
  room : Spec.Dsa.generationScratchWords (pLenOf s) ≤ (arg s 6).toNat
  seeds : (s.mem.readW (BitVec.setWidth 64 (arg s 7)) 64).toNat ≤ Spec.Dsa.parameterSeeds
  budget : s.mem.readW (BitVec.setWidth 64 (arg s 7) + 16) 64 =
    BitVec.ofNat 64 (Spec.Dsa.parameterEntropy (pLenOf s))
  randLen : (arg s 4).toNat ≤ Spec.Dsa.parameterEntropy (pLenOf s)

theorem call_facts {s : State} (h : genContract.pre s) : CallFacts s := by
  sig_pre [genContract, Spec.Dsa.parameterSearchContract, Spec.Dsa.parameterSearchSig,
    abi, argSlots, argVal, argBytes, Abi.withConsts, VG.Impl.RsaKeyGen.TrialTable32.consts, stackBelow] at h
  sig_split h
  constructor <;> try with_reducible assumption
  all_goals dsimp only [reservedRegion, VG.Impl.RsaKeyGen.TrialTable32.consts]
  all_goals with_reducible assumption

end VG.Proof.Dsa.X86.Generation
