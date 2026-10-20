module

public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Contract
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Bounds
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
open VG VG.Arm VG.Proof.Mont

private theorem widen_toNat (a : BitVec 32) : (a.setWidth 64).toNat = a.toNat := by
  rw [BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (Nat.lt_trans a.isLt (by decide))

theorem cached_layout {p : KeyPublic .cached} {s : State} (h : KeyInput p s) :
    KeyLayout (sampling := .cached) s := by
  have pre := h.1
  have strip : stripConsts [] s = s := by simp [stripConsts, State.withRegions]
  change (Spec.Ffdh.cachedKeySearchContract abi (stackUse .cached)).pre (stripConsts [] s) at pre
  rw [strip] at pre
  sig_pre [Spec.Ffdh.cachedKeySearchContract, Spec.Ffdh.cachedKeySearchSig,
    Spec.Ffdh.keySearchSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at pre
  sig_split pre
  have stackAddr : stackArgAddr s 0 = State.addr s.sp := by simp [stackArgAddr]
  have stackEq : stackUse .cached = 240 := rfl
  constructor <;>
    simp only [reads, writes, contextReads, GenerationPolicy.cachedContext, KeyConstants.consts,
      inX, inY, inUsed, inDomain, inRand, inScratch, inControl, inArgs, inContext,
      argsBytes, State.addr, stackAddr, ite_true, List.cons_append, List.nil_append, List.append_nil,
      constRegs, Abi.constRegions_nil, List.mem_cons, List.not_mem_nil, or_false,
      List.pairwise_cons, List.Pairwise.nil, forall_eq_or_imp, forall_eq,
      false_implies, and_true, stackEq, widen_toNat, Nat.mul_comm] at *
  sig_and_intros
  sig_close
  exact fun _ => True.intro

end VG.Proof.Ffdh.Arm.KeySearch
