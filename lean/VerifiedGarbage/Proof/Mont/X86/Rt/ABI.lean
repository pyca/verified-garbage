module

public import VerifiedGarbage.Proof.Mont.X86.ArgWs
public import VerifiedGarbage.Proof.Mont.X86.ArgFar
public import VerifiedGarbage.Proof.Framework.X86.Spill
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Mont.X86.Rt.Sub
public import VerifiedGarbage.Proof.Mont.X86.Csub

/-! # What `vg_rsa_mont_mul_at`'s contract gives on entry

`RtABI s`: the facts of `mulContract abi 0`'s precondition, as `sig_pre`
states them; from them, the working space (`Ws`), the arguments on the stack
(`Args`) and the layout (`Lay`) of the proofs.
-/

@[expose] public section

namespace VG.Proof.Mont.X86.Rt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont.X86.Rt VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Rsa.MontMul (Apart numAt scratchBytes)
open VG.Proof.Mont.X86.Dynamic (ArgFar ofs_far)

/-- The working space, from the first argument, and its bytes. -/
abbrev wsOf (s : State) : Addr := (arg s 0).setWidth 64
abbrev lenOf (s : State) : Nat := (arg s 1).toNat * 8

structure RtABI (s : State) : Prop where
  stackBound : (s.gpr .esp).toNat + 4 + 36 ≤ 2 ^ 32
  rd : s.rd = [⟨argAddr s 0, 36⟩]
  wr : s.wr = [⟨wsOf s, lenOf s⟩]
  argScratch : (⟨wsOf s, lenOf s⟩ : Region).Disjoint ⟨argAddr s 0, 36⟩
  retScratch : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨wsOf s, lenOf s⟩
  retArgs : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨argAddr s 0, 36⟩
  bound : (arg s 0).toNat + lenOf s ≤ 2 ^ 32
  pos : 0 < (arg s 2).toNat
  mo_le : (arg s 3).toNat + 8 * (arg s 2).toNat ≤ 8 * (arg s 1).toNat
  inv_le : (arg s 4).toNat + 4 ≤ 8 * (arg s 1).toNat
  s_le : (arg s 5).toNat + scratchBytes (arg s 2).toNat ≤ 8 * (arg s 1).toNat
  o_le : (arg s 6).toNat + 8 * (arg s 2).toNat ≤ 8 * (arg s 1).toNat
  a_le : (arg s 7).toNat + 8 * (arg s 2).toNat ≤ 8 * (arg s 1).toNat
  b_le : (arg s 8).toNat + 8 * (arg s 2).toNat ≤ 8 * (arg s 1).toNat
  smo : Apart (arg s 3).toNat (8 * (arg s 2).toNat) ((arg s 5).toNat, scratchBytes (arg s 2).toNat)
  sinv : Apart (arg s 4).toNat 4 ((arg s 5).toNat, scratchBytes (arg s 2).toNat)
  so : Apart (arg s 6).toNat (8 * (arg s 2).toNat) ((arg s 5).toNat, scratchBytes (arg s 2).toNat)
  sa : Apart (arg s 7).toNat (8 * (arg s 2).toNat) ((arg s 5).toNat, scratchBytes (arg s 2).toNat)
  sb : Apart (arg s 8).toNat (8 * (arg s 2).toNat) ((arg s 5).toNat, scratchBytes (arg s 2).toNat)
  omo : Apart (arg s 6).toNat (8 * (arg s 2).toNat) ((arg s 3).toNat, 8 * (arg s 2).toNat)
  oinv : Apart (arg s 6).toNat (8 * (arg s 2).toNat) ((arg s 4).toNat, 4)
  inv : (numAt s.mem (wsOf s) (arg s 3).toNat (8 * (arg s 2).toNat) *
    numAt s.mem (wsOf s) (arg s 4).toNat 4 + 1) % 2 ^ 32 = 0
  bLt : numAt s.mem (wsOf s) (arg s 8).toNat (8 * (arg s 2).toNat) <
    numAt s.mem (wsOf s) (arg s 3).toNat (8 * (arg s 2).toNat)

end VG.Proof.Mont.X86.Rt
