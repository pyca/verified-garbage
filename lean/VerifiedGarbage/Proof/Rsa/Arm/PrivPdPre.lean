module

public import VerifiedGarbage.Proof.Rsa.Arm.PrivPdArgs
public import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Rsa.Scratch
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # The re-exponentiation call satisfies the shared buffer contract -/

@[expose] public section
namespace VG.Proof.Rsa.Arm
open VG VG.Arm VG.Impl.Rsa.Arm.PrivChecked VG.Proof.Bignum.Arm VG.Proof.Mont

def pdRd (g : PrivGeometry) : List Region :=
  [⟨State.addr g.precomputation, 16 * Spec.Rsa.modulusWords g.length⟩,
    g.sourceRegion 1, ⟨State.addr g.temporary, g.length⟩, ⟨State.addr g.stack, 24⟩]
def pdWr (g : PrivGeometry) : List Region := [g.outputRegion, g.workspaceRegion]

theorem pdArgs_stack {g : PrivGeometry} {bs : Fin 8 → List Byte} {s : State}
    (h : PrivContext g bs s) (a : PdArgs g s) {j : Nat} (hj : j < 6) :
    stackArg (s.callEntry.withRegions (pdRd g) (pdWr g)) j = pdArgument g j := by
  simp only [stackArg, stackArgAddr, State.withRegions_mem, State.callEntry_mem,
    State.withRegions_sp, State.callEntry_sp, h.sp]
  rw [addr_add (by have := h.valid.stackHigh; simp only [frameBytes] at this; omega)]
  exact a.arguments j hj

theorem pdCall_pre {g : PrivGeometry} {bs : Fin 8 → List Byte} {s : State}
    (h : PrivContext g bs s) (a : PdArgs g s) :
    (Spec.Rsa.publicPrecomputedCheckedContract abi 56).pre (s.callEntry.withRegions (pdRd g) (pdWr g)) := by
  have sa := fun {j} (hj : j < 6) => pdArgs_stack h a hj
  have kfit : g.length < 2 ^ 32 := by have := h.valid.maxLength; omega
  have efit : g.exponentLength < 2 ^ 32 := by have := h.valid.exponentFits; omega
  have wfit : g.scratchLength < 2 ^ 32 := by have := h.valid.workspaceFit; omega
  have pfit : 2 * Spec.Rsa.modulusWords g.length < 2 ^ 32 := by
    have := h.valid.maxLength; simp only [Spec.Rsa.modulusWords]; omega
  sig_pre [Spec.Rsa.publicPrecomputedCheckedContract, Spec.Rsa.publicPrecomputedSig, abi, argRegs, reduceClassify, Loc.val, State.addr]
  simp only [h.sp, a.output, a.outputLength, a.precomputation, a.precomputationLength,
    sa (by decide : 0 < 6), sa (by decide : 1 < 6), sa (by decide : 2 < 6),
    sa (by decide : 3 < 6), sa (by decide : 4 < 6), sa (by decide : 5 < 6), pdArgument,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt kfit, Nat.mod_eq_of_lt efit,
    Nat.mod_eq_of_lt wfit, Nat.mod_eq_of_lt pfit]
  have argAddr : stackArgAddr (s.callEntry.withRegions (pdRd g) (pdWr g)) 0 = State.addr g.stack := by
    simp [stackArgAddr, h.sp]
  rw [argAddr, show 2 * Spec.Rsa.modulusWords g.length * 8 = 16 * Spec.Rsa.modulusWords g.length by omega,
    show g.scratchLength * 8 = 8 * g.scratchLength from Nat.mul_comm _ _]
  have preSub : (⟨State.addr g.precomputation, 16 * Spec.Rsa.modulusWords g.length⟩ : Region).Sub g.innerRegion := by
    rw [PrivGeometry.precomputation, h.valid.offsetAddr (by decide)]
    exact Offset.sub_base _ (by have := h.valid.maxLength; simp only [oPre, frameBytes, Spec.Rsa.modulusWords]; omega)
  have tempSub : (⟨State.addr g.temporary, g.length⟩ : Region).Sub g.innerRegion := by
    rw [PrivGeometry.temporary, h.valid.offsetAddr (by decide)]
    exact Offset.sub_base _ (by have := h.valid.maxLength; simp only [oM, frameBytes]; omega)
  have preStack : (⟨State.addr g.precomputation, 16 * Spec.Rsa.modulusWords g.length⟩ : Region).Sub g.wholeStack :=
    fun x hx => h.valid.innerSub x (preSub x hx)
  have tempStack : (⟨State.addr g.temporary, g.length⟩ : Region).Sub g.wholeStack :=
    fun x hx => h.valid.innerSub x (tempSub x hx)
  have argSub : (⟨State.addr g.stack, 24⟩ : Region).Sub g.innerRegion := Region.sub_prefix (by decide)
  have argStack : (⟨State.addr g.stack, 24⟩ : Region).Sub g.wholeStack :=
    fun x hx => h.valid.innerSub x (argSub x hx)
  have callee : (⟨g.stack.setWidth 64 - BitVec.ofNat 64 56, 56⟩ : Region) = g.calleeRegion := by
    unfold PrivGeometry.calleeRegion FrameStack.belowA
    rw [FrameStack.addr_sub' h.valid.stackLow]; rfl
  refine ⟨h.valid.stackLow, by have := h.valid.stackHigh; omega, rfl, rfl,
    (h.valid.stackOutput.sub_left preStack).symm, h.valid.outputSources 1,
    (h.valid.stackOutput.sub_left tempStack).symm, h.valid.outputWorkspace,
    (h.valid.stackOutput.sub_left argStack).symm,
    h.valid.stackWorkspace.sub_left preStack, h.valid.sourcesWorkspace 1,
    h.valid.stackWorkspace.sub_left tempStack, (h.valid.stackWorkspace.sub_left argStack).symm,
    ?_, ?_, ?_, ?_, ?_, ?_, h.valid.outputFit, h.valid.precomputationFit, h.valid.sourceFits 1,
    h.valid.temporaryFit, h.valid.workspaceFit, ⟨h.valid.minLength, h.valid.maxLength⟩, rfl,
    trivial, h.valid.exponentPositive, h.valid.exponentFits, publicScratch_le ⟨h.valid.minLength, h.valid.maxLength⟩ h.valid.space⟩
  · rw [callee]; exact h.valid.stackOutput.sub_left h.valid.calleeSub
  · rw [callee]; exact h.valid.calleeInner.sub_right preSub
  · rw [callee]; exact (h.valid.stackSources 1).sub_left h.valid.calleeSub
  · rw [callee]; exact h.valid.calleeInner.sub_right tempSub
  · rw [callee]; exact h.valid.stackWorkspace.sub_left h.valid.calleeSub
  · rw [callee]; exact h.valid.calleeInner.sub_right argSub
end VG.Proof.Rsa.Arm
