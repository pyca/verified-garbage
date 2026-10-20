module

public import VerifiedGarbage.Proof.Rsa.Arm.PrivPcArgs
public import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Rsa.Scratch
import VerifiedGarbage.Proof.Rsa.Arm.PrivRegions
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset

/-! # The public precomputation call satisfies the shared buffer contract -/

@[expose] public section
namespace VG.Proof.Rsa.Arm
open VG VG.Arm VG.Impl.Rsa.Arm.PrivChecked VG.Proof.Bignum.Arm VG.Proof.Mont

def pcRd (g : PrivGeometry) : List Region := [g.sourceRegion 0, ⟨State.addr g.stack, 8⟩]
def pcWr (g : PrivGeometry) : List Region :=
  [⟨State.addr g.precomputation, 16 * Spec.Rsa.modulusWords g.length⟩, g.workspaceRegion]

theorem pcArgs_stack {g : PrivGeometry} {bs : Fin 8 → List Byte} {s : State}
    (h : PrivContext g bs s) (a : PcArgs g s) :
    stackArg (s.callEntry.withRegions (pcRd g) (pcWr g)) 0 = g.workspace ∧
    stackArg (s.callEntry.withRegions (pcRd g) (pcWr g)) 1 = BitVec.ofNat 32 g.scratchLength := by
  simp only [stackArg, stackArgAddr, State.withRegions_mem, State.callEntry_mem,
    State.withRegions_sp, State.callEntry_sp, h.sp]
  constructor
  · simpa only [Nat.mul_zero, BitVec.add_zero] using a.workspace
  · rw [addr_add (by have := h.valid.stackHigh; simp only [frameBytes] at this; omega)]
    exact a.workspaceLength

theorem pcCall_pre {g : PrivGeometry} {bs : Fin 8 → List Byte} {s : State}
    (h : PrivContext g bs s) (a : PcArgs g s) :
    (Spec.Rsa.publicPrecomputeContract abi 56).pre (s.callEntry.withRegions (pcRd g) (pcWr g)) := by
  have sa := pcArgs_stack h a
  have kfit : g.length < 2 ^ 32 := by have := h.valid.maxLength; omega
  have wfit : g.scratchLength < 2 ^ 32 := by have := h.valid.workspaceFit; omega
  have pfit : 2 * Spec.Rsa.modulusWords g.length < 2 ^ 32 := by
    have := h.valid.maxLength; simp only [Spec.Rsa.modulusWords]; omega
  sig_pre [Spec.Rsa.publicPrecomputeContract, Spec.Rsa.publicPrecomputeSig, abi, argRegs, reduceClassify, Loc.val, State.addr]
  simp only [h.sp, a.output, a.outputLength, a.modulus, a.length, sa.1, sa.2,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt kfit, Nat.mod_eq_of_lt wfit, Nat.mod_eq_of_lt pfit]
  have argAddr : stackArgAddr (s.callEntry.withRegions (pcRd g) (pcWr g)) 0 = State.addr g.stack := by
    simp [stackArgAddr, h.sp]
  rw [argAddr, show 2 * Spec.Rsa.modulusWords g.length * 8 = 16 * Spec.Rsa.modulusWords g.length by omega,
    show g.scratchLength * 8 = 8 * g.scratchLength from Nat.mul_comm _ _]
  have preSub : (⟨State.addr g.precomputation, 16 * Spec.Rsa.modulusWords g.length⟩ : Region).Sub g.innerRegion := by
    rw [PrivGeometry.precomputation, h.valid.offsetAddr (by decide)]
    exact Offset.sub_base _ (by have := h.valid.maxLength; simp only [oPre, frameBytes, Spec.Rsa.modulusWords]; omega)
  have preStack : (⟨State.addr g.precomputation, 16 * Spec.Rsa.modulusWords g.length⟩ : Region).Sub g.wholeStack :=
    fun x hx => h.valid.innerSub x (preSub x hx)
  have argSub : (⟨State.addr g.stack, 8⟩ : Region).Sub g.innerRegion := Region.sub_prefix (by decide)
  have callee : (⟨g.stack.setWidth 64 - BitVec.ofNat 64 56, 56⟩ : Region) = g.calleeRegion := by
    unfold PrivGeometry.calleeRegion FrameStack.belowA
    rw [FrameStack.addr_sub' h.valid.stackLow]; rfl
  refine ⟨h.valid.stackLow, by have := h.valid.stackHigh; omega, rfl, rfl,
    (h.valid.stackSources 0).sub_left preStack, h.valid.stackWorkspace.sub_left preStack, ?_,
    h.valid.sourcesWorkspace 0, ?_, ?_, ?_, ?_, ?_, h.valid.precomputationFit,
    h.valid.sourceFits 0, h.valid.workspaceFit, ⟨h.valid.minLength, h.valid.maxLength⟩, rfl, publicScratch_le ⟨h.valid.minLength, h.valid.maxLength⟩ h.valid.space⟩
  · change (⟨State.addr g.precomputation, 16 * Spec.Rsa.modulusWords g.length⟩ : Region).Disjoint _
    rw [PrivGeometry.precomputation, h.valid.offsetAddr (by decide)]
    exact Offset.disjoint_base _ (by decide : 8 ≤ oPre)
      (by have := h.valid.maxLength; simp only [oPre, Spec.Rsa.modulusWords]; omega)
  · exact (h.valid.stackWorkspace.sub_left (fun x hx => h.valid.innerSub x (argSub x hx))).symm
  · rw [callee]; exact h.valid.calleeInner.sub_right preSub
  · rw [callee]; exact (h.valid.stackSources 0).sub_left h.valid.calleeSub
  · rw [callee]; exact h.valid.stackWorkspace.sub_left h.valid.calleeSub
  · rw [callee]; exact h.valid.calleeInner.sub_right argSub
end VG.Proof.Rsa.Arm
