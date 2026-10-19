module

public import VerifiedGarbage.Spec.Dsa.SignVerify
public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Framework.Contract
public import Mathlib.Logic.Function.Basic
public import Mathlib.Tactic.Set
public import Mathlib.Tactic.SplitIfs
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Spec.Weierstrass

/-! # Verification resources supplied by the shared cdecl contract -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86

abbrev argumentPointer (s : State) (i : Nat) : Addr := (arg s i).setWidth 64

structure VerifyingABI (s : State) : Prop where
  stackLow : 32 ≤ (s.gpr .esp).toNat
  stackBound : (s.gpr .esp).toNat + 44 ≤ 2 ^ 32
  rd : s.rd = [⟨argumentPointer s 0, (arg s 1).toNat⟩,
    ⟨argumentPointer s 4, (arg s 5).toNat⟩, ⟨argumentPointer s 6, (arg s 7).toNat⟩]
  wr : s.wr = [⟨argumentPointer s 8, (arg s 9).toNat * 8⟩, ⟨argAddr s 0, 40⟩]
  keyScratch : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint
    ⟨argumentPointer s 8, (arg s 9).toNat * 8⟩
  signatureScratch : (⟨argumentPointer s 4, (arg s 5).toNat⟩ : Region).Disjoint
    ⟨argumentPointer s 8, (arg s 9).toNat * 8⟩
  digestScratch : (⟨argumentPointer s 6, (arg s 7).toNat⟩ : Region).Disjoint
    ⟨argumentPointer s 8, (arg s 9).toNat * 8⟩
  scratchArgs : (⟨argumentPointer s 8, (arg s 9).toNat * 8⟩ : Region).Disjoint ⟨argAddr s 0, 40⟩
  retScratch : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint
    ⟨argumentPointer s 8, (arg s 9).toNat * 8⟩
  belowScratch : (⟨(s.gpr .esp).setWidth 64 - 32#64, 32⟩ : Region).Disjoint
    ⟨argumentPointer s 8, (arg s 9).toNat * 8⟩
  belowKey : (⟨(s.gpr .esp).setWidth 64 - 32#64, 32⟩ : Region).Disjoint
    ⟨argumentPointer s 0, (arg s 1).toNat⟩
  belowSignature : (⟨(s.gpr .esp).setWidth 64 - 32#64, 32⟩ : Region).Disjoint
    ⟨argumentPointer s 4, (arg s 5).toNat⟩
  belowDigest : (⟨(s.gpr .esp).setWidth 64 - 32#64, 32⟩ : Region).Disjoint
    ⟨argumentPointer s 6, (arg s 7).toNat⟩
  keyBound : (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32
  signatureBound : (arg s 4).toNat + (arg s 5).toNat ≤ 2 ^ 32
  digestBound : (arg s 6).toNat + (arg s 7).toNat ≤ 2 ^ 32
  scratchBound : (arg s 8).toNat + (arg s 9).toNat * 8 ≤ 2 ^ 32
  lengths : Spec.Dsa.lengthsValid (arg s 2).toNat (arg s 3).toNat
  keyLength : (arg s 1).toNat = 3 * (arg s 2).toNat + (arg s 3).toNat
  signatureLength : (arg s 5).toNat = 2 * (arg s 3).toNat
  scratchLength : Spec.Dsa.scratchWords (arg s 2).toNat ≤ (arg s 9).toNat

theorem verifyingABI_of {s : State} (h : (Spec.Dsa.verifyContract abi 32).pre s) : VerifyingABI s := by
  sig_pre [Spec.Dsa.verifyContract, Spec.Dsa.verifySig, abi, argSlots, argVal, argBytes, stackBelow] at h
  sig_split h
  constructor <;> with_reducible assumption

end VG.Proof.Dsa.X86
