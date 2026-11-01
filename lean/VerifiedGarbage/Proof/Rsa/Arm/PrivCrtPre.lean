module

public import VerifiedGarbage.Proof.Rsa.Arm.PrivCrtArgs
public import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Rsa.Arm.PrivRegions
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Rsa.Contract

/-! # The private CRT call satisfies the shared buffer contract -/

@[expose] public section
namespace VG.Proof.Rsa.Arm
open VG VG.Arm VG.Impl.Rsa.Arm.PrivChecked VG.Proof.Bignum.Arm VG.Proof.Mont

def crtRd (g : PrivGeometry) : List Region :=
  [g.sourceRegion 0, g.sourceRegion 2, g.sourceRegion 3, g.sourceRegion 4,
    g.sourceRegion 5, g.sourceRegion 6, g.sourceRegion 7, ⟨State.addr g.stack, 56⟩]
def crtWr (g : PrivGeometry) : List Region :=
  [⟨State.addr g.temporary, g.length⟩, g.workspaceRegion]

theorem crtArgs_stack {g : PrivGeometry} {bs : Fin 8 → List Byte} {s : State}
    (h : PrivContext g bs s) (a : CrtArgs g s) {j : Nat} (hj : j < 14) :
    stackArg (s.callEntry.withRegions (crtRd g) (crtWr g)) j = g.argument (j + 2) := by
  simp only [stackArg, stackArgAddr, State.withRegions_mem, State.callEntry_mem,
    State.withRegions_sp, State.callEntry_sp, h.sp]
  rw [addr_add (by have := h.valid.stackHigh; simp only [frameBytes] at this; omega)]
  exact a.arguments j hj

theorem crtCall_pre {g : PrivGeometry} {bs : Fin 8 → List Byte} {s : State}
    (h : PrivContext g bs s) (a : CrtArgs g s) :
    (Proof.Rsa.privateCrtContract abi 56).pre (s.callEntry.withRegions (crtRd g) (crtWr g)) := by
  have sa := fun {j} (hj : j < 14) => crtArgs_stack h a hj
  have kfit : g.length < 2 ^ 32 := by have := h.valid.maxLength; omega
  have pfit : g.pLength < 2 ^ 32 := by have := h.valid.pFits; omega
  have qfit : g.qLength < 2 ^ 32 := by have := h.valid.qFits; omega
  have wfit : g.scratchLength < 2 ^ 32 := by have := h.valid.workspaceFit; omega
  sig_pre [Proof.Rsa.privateCrtContract, Proof.Rsa.privateCrtSig, abi, argRegs, reduceClassify, Loc.val, State.addr]
  simp only [
    h.sp, a.output, a.outputLength, a.modulus, a.length,
    sa (by decide : 0 < 14), sa (by decide : 1 < 14), sa (by decide : 2 < 14),
    sa (by decide : 3 < 14), sa (by decide : 4 < 14), sa (by decide : 5 < 14),
    sa (by decide : 6 < 14), sa (by decide : 7 < 14), sa (by decide : 8 < 14),
    sa (by decide : 9 < 14), sa (by decide : 10 < 14), sa (by decide : 11 < 14),
    sa (by decide : 12 < 14), sa (by decide : 13 < 14), PrivGeometry.argument,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt kfit, Nat.mod_eq_of_lt pfit,
    Nat.mod_eq_of_lt qfit, Nat.mod_eq_of_lt wfit]
  have argAddr : stackArgAddr (s.callEntry.withRegions (crtRd g) (crtWr g)) 0 = State.addr g.stack := by
    simp [stackArgAddr, h.sp]
  rw [argAddr]
  have temporarySub : (⟨State.addr g.temporary, g.length⟩ : Region).Sub g.innerRegion := by
    rw [PrivGeometry.temporary, h.valid.offsetAddr (by decide)]
    exact Offset.sub_base _ (by have := h.valid.maxLength; simp only [oM, frameBytes]; omega)
  have outgoingSub : (⟨State.addr g.stack, 56⟩ : Region).Sub g.innerRegion :=
    Region.sub_prefix (by decide : 56 ≤ frameBytes)
  have tempSources := fun i => (h.valid.stackSources i).sub_left (fun x hx => h.valid.innerSub x (temporarySub x hx))
  have tempWorkspace := h.valid.stackWorkspace.sub_left (fun x hx => h.valid.innerSub x (temporarySub x hx))
  have tempArgs : (⟨State.addr g.temporary, g.length⟩ : Region).Disjoint ⟨State.addr g.stack, 56⟩ := by
    rw [PrivGeometry.temporary, h.valid.offsetAddr (by decide)]
    exact Offset.disjoint_base _ (by decide : 56 ≤ oM) (by have := h.valid.maxLength; simp only [oM]; omega)
  have callee : (⟨State.addr g.stack - BitVec.ofNat 64 56, 56⟩ : Region) = g.calleeRegion := by
    unfold PrivGeometry.calleeRegion FrameStack.belowA
    rw [FrameStack.addr_sub' h.valid.stackLow]
  simp only [State.addr] at callee
  have calleeSources := fun i => (h.valid.stackSources i).sub_left h.valid.calleeSub
  have calleeWorkspace := h.valid.stackWorkspace.sub_left h.valid.calleeSub
  have argsWorkspace := (h.valid.stackWorkspace.sub_left (fun x hx => h.valid.innerSub x (outgoingSub x hx))).symm
  refine ⟨h.valid.stackLow, by have := h.valid.stackHigh; omega, rfl, ?_,
    tempSources 0, tempSources 2, tempSources 3, tempSources 4, tempSources 5, tempSources 6, tempSources 7,
    ?_, tempArgs, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    h.valid.temporaryFit, h.valid.sourceFits 0, h.valid.sourceFits 2, h.valid.sourceFits 3,
    h.valid.sourceFits 4, h.valid.sourceFits 5, h.valid.sourceFits 6, h.valid.sourceFits 7,
    ?_, ⟨h.valid.minLength, h.valid.maxLength⟩, trivial, trivial,
    h.valid.pPositive, h.valid.pFits, h.valid.qPositive, h.valid.qFits, trivial, trivial, trivial, h.valid.space⟩
  · simp only [crtWr, PrivGeometry.workspaceRegion, State.addr, Nat.mul_comm]
  · simpa only [PrivGeometry.workspaceRegion, State.addr, Nat.mul_comm] using tempWorkspace
  · change (g.sourceRegion 0).Disjoint ⟨State.addr g.workspace, g.scratchLength * 8⟩
    rw [Nat.mul_comm]
    exact h.valid.sourcesWorkspace 0
  · change (g.sourceRegion 2).Disjoint ⟨State.addr g.workspace, g.scratchLength * 8⟩
    rw [Nat.mul_comm]
    exact h.valid.sourcesWorkspace 2
  · change (g.sourceRegion 3).Disjoint ⟨State.addr g.workspace, g.scratchLength * 8⟩
    rw [Nat.mul_comm]
    exact h.valid.sourcesWorkspace 3
  · change (g.sourceRegion 4).Disjoint ⟨State.addr g.workspace, g.scratchLength * 8⟩
    rw [Nat.mul_comm]
    exact h.valid.sourcesWorkspace 4
  · change (g.sourceRegion 5).Disjoint ⟨State.addr g.workspace, g.scratchLength * 8⟩
    rw [Nat.mul_comm]
    exact h.valid.sourcesWorkspace 5
  · change (g.sourceRegion 6).Disjoint ⟨State.addr g.workspace, g.scratchLength * 8⟩
    rw [Nat.mul_comm]
    exact h.valid.sourcesWorkspace 6
  · change (g.sourceRegion 7).Disjoint ⟨State.addr g.workspace, g.scratchLength * 8⟩
    rw [Nat.mul_comm]
    exact h.valid.sourcesWorkspace 7
  · simpa only [PrivGeometry.workspaceRegion, State.addr, Nat.mul_comm] using argsWorkspace
  · rw [callee]; exact h.valid.calleeInner.sub_right temporarySub
  · rw [callee]; exact calleeSources 0
  · rw [callee]; exact calleeSources 2
  · rw [callee]; exact calleeSources 3
  · rw [callee]; exact calleeSources 4
  · rw [callee]; exact calleeSources 5
  · rw [callee]; exact calleeSources 6
  · rw [callee]; exact calleeSources 7
  · rw [callee]; simpa only [PrivGeometry.workspaceRegion, State.addr, Nat.mul_comm] using calleeWorkspace
  · rw [callee]; exact h.valid.calleeInner.sub_right outgoingSub
  · simpa only [Nat.mul_comm] using h.valid.workspaceFit
end VG.Proof.Rsa.Arm
