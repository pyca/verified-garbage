module

public import VerifiedGarbage.Proof.Rsa.X86.PrivCrtArgs
import VerifiedGarbage.Proof.Rsa.X86.PrivStackWord
import VerifiedGarbage.Proof.Rsa.X86.PrivRegions
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Rsa.Contract

/-! # The CRT call's narrowed regions satisfy the shared cdecl signature -/

@[expose] public section
namespace VG.Proof.Rsa.X86.PrivChecked
open VG VG.X86 VG.Impl.Rsa.X86.PrivChecked VG.Proof.Bignum.X86

def crtRd (g : PrivGeometry) : List Region :=
  [g.sourceRegion 0, g.sourceRegion 2, g.sourceRegion 3, g.sourceRegion 4,
    g.sourceRegion 5, g.sourceRegion 6, g.sourceRegion 7]
def crtWr (g : PrivGeometry) : List Region :=
  [⟨byteAddr g.temporary, g.length⟩, g.workspaceRegion, ⟨byteAddr g.stack, 72⟩]

theorem crtArgs_values {g : PrivGeometry} {bs : Fin 8 → List Byte} {s : State}
    (h : PrivContext g bs s) (a : CrtArgs g s) {j : Nat} (hj : j < 18) :
    arg (s.callEntry.withRegions (crtRd g) (crtWr g)) j = crtArgument g j := by
  rw [arg_withRegions, arg_callEntry (by rw [h.sp]; have := h.valid.stackLow; omega)
    (by rw [h.sp]; have := h.valid.stackHigh; omega)]
  change s.mem.readW (addr (s.gpr .esp) (4 * j)) 32 = _
  rw [h.address (by omega)]
  exact a j hj

theorem crtCall_pre {g : PrivGeometry} {bs : Fin 8 → List Byte} {s : State}
    (h : PrivContext g bs s) (a : CrtArgs g s) :
    (Proof.Rsa.privateCrtContract abi 96).pre (s.callEntry.withRegions (crtRd g) (crtWr g)) := by
  have sa := fun {j} (hj : j < 18) => crtArgs_values h a hj
  have kfit : g.length < 2 ^ 32 := by have := h.valid.maxLength; omega
  have pfit : g.pLength < 2 ^ 32 := by have := h.valid.pFits; omega
  have qfit : g.qLength < 2 ^ 32 := by have := h.valid.qFits; omega
  have wfit : g.scratchLength < 2 ^ 32 := by have := h.valid.workspaceFit; omega
  sig_pre [Proof.Rsa.privateCrtContract, Proof.Rsa.privateCrtSig, abi, argSlots, argVal, argBytes, stackBelow]
  simp only [sa (by decide : 0 < 18), sa (by decide : 1 < 18), sa (by decide : 2 < 18),
    sa (by decide : 3 < 18), sa (by decide : 4 < 18), sa (by decide : 5 < 18),
    sa (by decide : 6 < 18), sa (by decide : 7 < 18), sa (by decide : 8 < 18),
    sa (by decide : 9 < 18), sa (by decide : 10 < 18), sa (by decide : 11 < 18),
    sa (by decide : 12 < 18), sa (by decide : 13 < 18), sa (by decide : 14 < 18),
    sa (by decide : 15 < 18), sa (by decide : 16 < 18), sa (by decide : 17 < 18),
    crtArgument, PrivGeometry.argument, Nat.reduceAdd, Nat.reduceLT, Nat.reduceEqDiff,
    ite_true, ite_false, BitVec.toNat_ofNat, Nat.mod_eq_of_lt kfit, Nat.mod_eq_of_lt pfit,
    Nat.mod_eq_of_lt qfit, Nat.mod_eq_of_lt wfit,
    argAddr_withRegions, argAddr_callEntry, h.sp, Nat.mul_zero, BitVec.add_zero]
  have temporarySub : (⟨byteAddr g.temporary, g.length⟩ : Region).Sub g.innerRegion := by
    rw [PrivGeometry.temporary, h.valid.offsetAddr (by decide)]
    exact Offset.sub_base _ (by have := h.valid.maxLength; simp only [candidateOffset, VG.Impl.Rsa.X86.PrivChecked.frameBytes]; omega)
  have outgoingSub : (⟨byteAddr g.stack, 72⟩ : Region).Sub g.innerRegion :=
    Region.sub_prefix (by decide : 72 ≤ VG.Impl.Rsa.X86.PrivChecked.frameBytes)
  have tempSources := fun i => (h.valid.stackSources i).sub_left (fun x hx => h.valid.innerSub x (temporarySub x hx))
  have tempWorkspace := h.valid.stackWorkspace.sub_left (fun x hx => h.valid.innerSub x (temporarySub x hx))
  have tempArgs : (⟨byteAddr g.temporary, g.length⟩ : Region).Disjoint ⟨byteAddr g.stack, 72⟩ := by
    rw [PrivGeometry.temporary, h.valid.offsetAddr (by decide)]
    exact Offset.disjoint_base _ (by decide : 72 ≤ candidateOffset) (by have := h.valid.maxLength; simp only [candidateOffset]; omega)
  have calleeSources := fun i => (h.valid.stackSources i).sub_left h.valid.calleeSub
  have calleeWorkspace := h.valid.stackWorkspace.sub_left h.valid.calleeSub
  have argsWorkspace := (h.valid.stackWorkspace.sub_left (fun x hx => h.valid.innerSub x (outgoingSub x hx))).symm
  have low : (g.stack - 4).toNat = g.stack.toNat - 4 := sub_toNat (k := 4) (by have := h.valid.stackLow; omega)
  rw [low]
  have retSub : (⟨(g.stack - 4).setWidth 64, 4⟩ : Region).Sub g.calleeRegion :=
    VG.X86.below_sub (by decide : 4 ≤ 100) h.valid.stackLow
  have belowSub : (⟨(g.stack - 4).setWidth 64 - 96#64, 96⟩ : Region).Sub g.calleeRegion := by
    rw [← VG.X86.Taint.sub_setWidth (by rw [low]; have := h.valid.stackLow; omega : 96 ≤ (g.stack - 4).toNat)]
    exact VG.X86.below_inner (by decide : 96 + 4 ≤ 100) h.valid.stackLow
  have retTemp := (h.valid.calleeInner.sub_right temporarySub).sub_left retSub
  have belowTemp := (h.valid.calleeInner.sub_right temporarySub).sub_left belowSub
  have retSources := fun i => (calleeSources i).sub_left retSub
  have belowSources := fun i => (calleeSources i).sub_left belowSub
  have retWorkspace := calleeWorkspace.sub_left retSub
  have belowWorkspace := calleeWorkspace.sub_left belowSub
  have retArgs := (h.valid.calleeInner.sub_right outgoingSub).sub_left retSub
  have belowArgs := (h.valid.calleeInner.sub_right outgoingSub).sub_left belowSub
  have sourceArgs := fun i => ((h.valid.stackSources i).sub_left
    (fun x hx => h.valid.innerSub x (outgoingSub x hx))).symm
  simp only [Nat.mul_comm g.scratchLength 8]
  exact ⟨by have := h.valid.stackLow; omega,
    by have := h.valid.stackHigh; omega,
    rfl,
    rfl,
    tempSources 0,
    tempSources 2,
    tempSources 3,
    tempSources 4,
    tempSources 5,
    tempSources 6,
    tempSources 7,
    tempWorkspace,
    tempArgs,
    h.valid.sourcesWorkspace 0,
    sourceArgs 0,
    h.valid.sourcesWorkspace 2,
    sourceArgs 2,
    h.valid.sourcesWorkspace 3,
    sourceArgs 3,
    h.valid.sourcesWorkspace 4,
    sourceArgs 4,
    h.valid.sourcesWorkspace 5,
    sourceArgs 5,
    h.valid.sourcesWorkspace 6,
    sourceArgs 6,
    h.valid.sourcesWorkspace 7,
    sourceArgs 7,
    argsWorkspace,
    retTemp,
    retSources 0,
    retSources 2,
    retSources 3,
    retSources 4,
    retSources 5,
    retSources 6,
    retSources 7,
    retWorkspace,
    retArgs,
    belowTemp,
    belowSources 0,
    belowSources 2,
    belowSources 3,
    belowSources 4,
    belowSources 5,
    belowSources 6,
    belowSources 7,
    belowWorkspace,
    belowArgs,
    h.valid.temporaryFit,
    h.valid.sourceFits 0,
    h.valid.sourceFits 2,
    h.valid.sourceFits 3,
    h.valid.sourceFits 4,
    h.valid.sourceFits 5,
    h.valid.sourceFits 6,
    h.valid.sourceFits 7,
    h.valid.workspaceFit,
    ⟨h.valid.minLength, h.valid.maxLength⟩,
    trivial,
    trivial,
    h.valid.pPositive,
    h.valid.pFits,
    h.valid.qPositive,
    h.valid.qFits,
    trivial,
    trivial,
    trivial,
    h.valid.space⟩

end VG.Proof.Rsa.X86.PrivChecked
