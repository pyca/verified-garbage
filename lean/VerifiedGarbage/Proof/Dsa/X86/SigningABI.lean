module

public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Dsa.X86.VerifyingABI
public import VerifiedGarbage.Spec.Dsa.SignVerify
public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Dsa.Arithmetic
public import VerifiedGarbage.Proof.Dsa.Digest
public import VerifiedGarbage.Proof.Dsa.Encoding
public import VerifiedGarbage.Proof.Dsa.X86.Bytes
public import VerifiedGarbage.Proof.Dsa.X86.CoreSetup
public import VerifiedGarbage.Proof.Dsa.X86.EntrySave
public import VerifiedGarbage.Proof.Dsa.X86.FetchByte
public import VerifiedGarbage.Proof.Dsa.X86.Layout
public import VerifiedGarbage.Proof.Dsa.X86.LoadSlot
public import VerifiedGarbage.Proof.Dsa.X86.LocalOperand
public import VerifiedGarbage.Proof.Dsa.X86.Moduli
public import VerifiedGarbage.Proof.Dsa.X86.Reduce
public import VerifiedGarbage.Proof.Dsa.X86.RunBytes
public import VerifiedGarbage.Proof.Dsa.X86.SaveArgument
public import VerifiedGarbage.Proof.Dsa.X86.StackArgument
public import VerifiedGarbage.Proof.Dsa.X86.StageFrame
public import VerifiedGarbage.Proof.Mont.X86.ContextLayout
public import VerifiedGarbage.Proof.Mont.X86.ContextMath
public import VerifiedGarbage.Proof.Mont.X86.ContextMul
public import VerifiedGarbage.Proof.Mont.X86.DynamicAdd
public import VerifiedGarbage.Proof.Mont.X86.DynamicFrame
public import VerifiedGarbage.Proof.Mont.X86.DynamicSelect
public import VerifiedGarbage.Proof.Mont.X86.ExponentInitMath
public import VerifiedGarbage.Proof.Mont.X86.ExponentLoop
public import VerifiedGarbage.Proof.Mont.X86.ExponentMask
public import VerifiedGarbage.Proof.Mont.X86.ExponentShift
public import VerifiedGarbage.Proof.Mont.X86.ExponentStep
public import VerifiedGarbage.Proof.Mont.X86.ExponentWord
public import VerifiedGarbage.Proof.Mont.X86.Exponentiate
public import VerifiedGarbage.Proof.Mont.X86.Inverse
public import VerifiedGarbage.Proof.Mont.X86.PowerInit
public import VerifiedGarbage.Proof.Mont.X86.PowerLoop
public import VerifiedGarbage.Proof.Mont.X86.PowerTwo
public import VerifiedGarbage.Proof.Mont.X86.RowW
public import VerifiedGarbage.Proof.Mont.X86.WordOps
public import VerifiedGarbage.Proof.Weierstrass.X86.Bytes
public import VerifiedGarbage.Proof.Weierstrass.X86.BytesLen
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Dsa.Digest
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.X86.Bytes
import VerifiedGarbage.Proof.Dsa.X86.CoreSetup
import VerifiedGarbage.Proof.Dsa.X86.EntrySave
import VerifiedGarbage.Proof.Dsa.X86.FetchByte
import VerifiedGarbage.Proof.Dsa.X86.Layout
import VerifiedGarbage.Proof.Dsa.X86.LoadSlot
import VerifiedGarbage.Proof.Dsa.X86.LocalOperand
import VerifiedGarbage.Proof.Dsa.X86.Moduli
import VerifiedGarbage.Proof.Dsa.X86.Reduce
import VerifiedGarbage.Proof.Dsa.X86.RunBytes
import VerifiedGarbage.Proof.Dsa.X86.SaveArgument
import VerifiedGarbage.Proof.Dsa.X86.StackArgument
import VerifiedGarbage.Proof.Dsa.X86.StageFrame
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Mont.X86.ContextMath
import VerifiedGarbage.Proof.Mont.X86.ContextMul
import VerifiedGarbage.Proof.Mont.X86.DynamicAdd
import VerifiedGarbage.Proof.Mont.X86.DynamicFrame
import VerifiedGarbage.Proof.Mont.X86.DynamicSelect
import VerifiedGarbage.Proof.Mont.X86.ExponentInitMath
import VerifiedGarbage.Proof.Mont.X86.ExponentLoop
import VerifiedGarbage.Proof.Mont.X86.ExponentMask
import VerifiedGarbage.Proof.Mont.X86.ExponentShift
import VerifiedGarbage.Proof.Mont.X86.ExponentStep
import VerifiedGarbage.Proof.Mont.X86.ExponentWord
import VerifiedGarbage.Proof.Mont.X86.Exponentiate
import VerifiedGarbage.Proof.Mont.X86.Inverse
import VerifiedGarbage.Proof.Mont.X86.PowerInit
import VerifiedGarbage.Proof.Mont.X86.PowerLoop
import VerifiedGarbage.Proof.Mont.X86.PowerTwo
import VerifiedGarbage.Proof.Mont.X86.RowW
import VerifiedGarbage.Proof.Mont.X86.WordOps
import VerifiedGarbage.Proof.Weierstrass.X86.Bytes
import VerifiedGarbage.Proof.Weierstrass.X86.BytesLen

/-! # Signing resources supplied by the shared cdecl contract -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86

structure SigningABI (s : State) : Prop where
  stackLow : 32 ≤ (s.gpr .esp).toNat
  stackBound : (s.gpr .esp).toNat + 48 ≤ 2 ^ 32
  rd : s.rd = [⟨argumentPointer s 2, (arg s 3).toNat⟩,
    ⟨argumentPointer s 5, (arg s 6).toNat⟩, ⟨argumentPointer s 7, (arg s 8).toNat⟩]
  wr : s.wr = [⟨argumentPointer s 0, (arg s 1).toNat⟩, ⟨argumentPointer s 9, (arg s 10).toNat * 8⟩, ⟨argAddr s 0, 44⟩]
  outScratch : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint
    ⟨argumentPointer s 9, (arg s 10).toNat * 8⟩
  retOut : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint
    ⟨argumentPointer s 0, (arg s 1).toNat⟩
  outBound : (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32
  keyScratch : (⟨argumentPointer s 2, (arg s 3).toNat⟩ : Region).Disjoint
    ⟨argumentPointer s 9, (arg s 10).toNat * 8⟩
  nonceScratch : (⟨argumentPointer s 5, (arg s 6).toNat⟩ : Region).Disjoint
    ⟨argumentPointer s 9, (arg s 10).toNat * 8⟩
  digestScratch : (⟨argumentPointer s 7, (arg s 8).toNat⟩ : Region).Disjoint
    ⟨argumentPointer s 9, (arg s 10).toNat * 8⟩
  scratchArgs : (⟨argumentPointer s 9, (arg s 10).toNat * 8⟩ : Region).Disjoint ⟨argAddr s 0, 44⟩
  retScratch : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint
    ⟨argumentPointer s 9, (arg s 10).toNat * 8⟩
  belowScratch : (⟨(s.gpr .esp).setWidth 64 - 32#64, 32⟩ : Region).Disjoint
    ⟨argumentPointer s 9, (arg s 10).toNat * 8⟩
  belowKey : (⟨(s.gpr .esp).setWidth 64 - 32#64, 32⟩ : Region).Disjoint
    ⟨argumentPointer s 2, (arg s 3).toNat⟩
  belowNonce : (⟨(s.gpr .esp).setWidth 64 - 32#64, 32⟩ : Region).Disjoint
    ⟨argumentPointer s 5, (arg s 6).toNat⟩
  belowDigest : (⟨(s.gpr .esp).setWidth 64 - 32#64, 32⟩ : Region).Disjoint
    ⟨argumentPointer s 7, (arg s 8).toNat⟩
  keyBound : (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 32
  nonceBound : (arg s 5).toNat + (arg s 6).toNat ≤ 2 ^ 32
  digestBound : (arg s 7).toNat + (arg s 8).toNat ≤ 2 ^ 32
  scratchBound : (arg s 9).toNat + (arg s 10).toNat * 8 ≤ 2 ^ 32
  lengths : Spec.Dsa.lengthsValid (arg s 4).toNat (arg s 6).toNat
  keyLength : (arg s 3).toNat = 3 * (arg s 4).toNat + 2 * (arg s 6).toNat
  outLength : (arg s 1).toNat = 2 * (arg s 6).toNat
  scratchLength : Spec.Dsa.scratchWords (arg s 4).toNat ≤ (arg s 10).toNat

theorem signingABI_of {s : State} (h : (Spec.Dsa.signContract abi 32).pre s) : SigningABI s := by
  sig_pre [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argSlots, argVal, argBytes, stackBelow] at h
  sig_split h
  constructor <;> with_reducible assumption

end VG.Proof.Dsa.X86
