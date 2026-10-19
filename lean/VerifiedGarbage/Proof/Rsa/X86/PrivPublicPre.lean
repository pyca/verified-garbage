module

public import VerifiedGarbage.Proof.Rsa.X86.PrivPublicArgs
import VerifiedGarbage.Proof.Rsa.Scratch

/-! # The re-exponentiation call satisfies the shared buffer contract -/

@[expose] public section
namespace VG.Proof.Rsa.X86.PrivChecked
open VG VG.X86 VG.Impl.Rsa.X86.PrivChecked VG.Proof.Bignum.X86

def pdRd (g : PrivGeometry) : List Region :=
  [⟨byteAddr g.precomputation, 16 * Spec.Rsa.modulusWords g.length⟩,
    g.sourceRegion 1, ⟨byteAddr g.temporary, g.length⟩]
def pdWr (g : PrivGeometry) : List Region := [g.outputRegion, g.workspaceRegion, ⟨byteAddr g.stack, 40⟩]

theorem pdArgs_values {g : PrivGeometry} {bs : Fin 8 → List Byte} {s : State}
    (h : PrivContext g bs s) (a : Arguments g (pdArgument g) 10 s) {j : Nat} (hj : j < 10) :
    arg (s.callEntry.withRegions (pdRd g) (pdWr g)) j = pdArgument g j := by
  rw [arg_withRegions, arg_callEntry (by rw [h.sp]; have := h.valid.stackLow; omega)
    (by rw [h.sp]; have := h.valid.stackHigh; omega)]
  change s.mem.readW (addr (s.gpr .esp) (4 * j)) 32 = _
  rw [h.address (by omega)]
  exact a j hj

theorem pdCall_pre {g : PrivGeometry} {bs : Fin 8 → List Byte} {s : State}
    (h : PrivContext g bs s) (a : Arguments g (pdArgument g) 10 s) :
    (Spec.Rsa.publicPrecomputedCheckedContract abi 20).pre (s.callEntry.withRegions (pdRd g) (pdWr g)) := by
  have sa := fun {j} (hj : j < 10) => pdArgs_values h a hj
  have kfit : g.length < 2 ^ 32 := by have := h.valid.maxLength; omega
  have efit : g.exponentLength < 2 ^ 32 := by have := h.valid.exponentFits; omega
  have wfit : g.scratchLength < 2 ^ 32 := by have := h.valid.workspaceFit; omega
  have pfit : 2 * Spec.Rsa.modulusWords g.length < 2 ^ 32 := by
    have := h.valid.maxLength; simp only [Spec.Rsa.modulusWords]; omega
  sig_pre [Spec.Rsa.publicPrecomputedCheckedContract, Spec.Rsa.publicPrecomputedSig, abi, argSlots, argVal, argBytes, stackBelow]
  simp only [sa (by decide : 0 < 10), sa (by decide : 1 < 10), sa (by decide : 2 < 10),
    sa (by decide : 3 < 10), sa (by decide : 4 < 10), sa (by decide : 5 < 10),
    sa (by decide : 6 < 10), sa (by decide : 7 < 10), sa (by decide : 8 < 10),
    sa (by decide : 9 < 10), pdArgument, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt kfit, Nat.mod_eq_of_lt efit, Nat.mod_eq_of_lt wfit, Nat.mod_eq_of_lt pfit,
    argAddr_withRegions, argAddr_callEntry, h.sp, Nat.mul_zero, BitVec.add_zero]
  rw [show 2 * Spec.Rsa.modulusWords g.length * 8 = 16 * Spec.Rsa.modulusWords g.length by omega,
    show g.scratchLength * 8 = 8 * g.scratchLength from Nat.mul_comm _ _]
  have preSub : (⟨byteAddr g.precomputation, 16 * Spec.Rsa.modulusWords g.length⟩ : Region).Sub g.innerRegion := by
    rw [PrivGeometry.precomputation, h.valid.offsetAddr (by decide)]
    exact Offset.sub_base _ (by have := h.valid.maxLength; simp only [precomputeOffset, VG.Impl.Rsa.X86.PrivChecked.frameBytes, Spec.Rsa.modulusWords]; omega)
  have tempSub : (⟨byteAddr g.temporary, g.length⟩ : Region).Sub g.innerRegion := by
    rw [PrivGeometry.temporary, h.valid.offsetAddr (by decide)]
    exact Offset.sub_base _ (by have := h.valid.maxLength; simp only [candidateOffset, VG.Impl.Rsa.X86.PrivChecked.frameBytes]; omega)
  have preStack : (⟨byteAddr g.precomputation, 16 * Spec.Rsa.modulusWords g.length⟩ : Region).Sub g.wholeStack :=
    fun x hx => h.valid.innerSub x (preSub x hx)
  have tempStack : (⟨byteAddr g.temporary, g.length⟩ : Region).Sub g.wholeStack :=
    fun x hx => h.valid.innerSub x (tempSub x hx)
  have argSub : (⟨byteAddr g.stack, 40⟩ : Region).Sub g.innerRegion := Region.sub_prefix (by decide)
  have argStack : (⟨byteAddr g.stack, 40⟩ : Region).Sub g.wholeStack :=
    fun x hx => h.valid.innerSub x (argSub x hx)
  have preArgs : (⟨byteAddr g.precomputation, 16 * Spec.Rsa.modulusWords g.length⟩ : Region).Disjoint ⟨byteAddr g.stack, 40⟩ := by
    rw [PrivGeometry.precomputation, h.valid.offsetAddr (by decide)]
    exact Offset.disjoint_base _ (by decide : 40 ≤ precomputeOffset)
      (by have := h.valid.maxLength; simp only [precomputeOffset, Spec.Rsa.modulusWords]; omega)
  have tempArgs : (⟨byteAddr g.temporary, g.length⟩ : Region).Disjoint ⟨byteAddr g.stack, 40⟩ := by
    rw [PrivGeometry.temporary, h.valid.offsetAddr (by decide)]
    exact Offset.disjoint_base _ (by decide : 40 ≤ candidateOffset)
      (by have := h.valid.maxLength; simp only [candidateOffset]; omega)
  have low : (g.stack - 4).toNat = g.stack.toNat - 4 := sub_toNat (k := 4) (by have := h.valid.stackLow; omega)
  have retSub : (⟨(g.stack - 4).setWidth 64, 4⟩ : Region).Sub g.calleeRegion :=
    VG.X86.below_sub (by decide : 4 ≤ 44) h.valid.stackLow
  have belowSub : (⟨(g.stack - 4).setWidth 64 - 20#64, 20⟩ : Region).Sub g.calleeRegion := by
    rw [← VG.X86.Taint.sub_setWidth (by rw [low]; have := h.valid.stackLow; omega : 20 ≤ (g.stack - 4).toNat)]
    exact VG.X86.below_inner (by decide : 20 + 4 ≤ 44) h.valid.stackLow
  have cOut := h.valid.stackOutput.sub_left h.valid.calleeSub
  have cPre := h.valid.calleeInner.sub_right preSub
  have cExp := (h.valid.stackSources 1).sub_left h.valid.calleeSub
  have cTmp := h.valid.calleeInner.sub_right tempSub
  have cWork := h.valid.stackWorkspace.sub_left h.valid.calleeSub
  have cArgs := h.valid.calleeInner.sub_right argSub
  rw [low]
  exact ⟨by have := h.valid.stackLow; omega, by have := h.valid.stackHigh; omega, rfl, rfl,
    (h.valid.stackOutput.sub_left preStack).symm, h.valid.outputSources 1,
    (h.valid.stackOutput.sub_left tempStack).symm, h.valid.outputWorkspace,
    (h.valid.stackOutput.sub_left argStack).symm,
    h.valid.stackWorkspace.sub_left preStack, preArgs, h.valid.sourcesWorkspace 1,
    ((h.valid.stackSources 1).sub_left argStack).symm,
    h.valid.stackWorkspace.sub_left tempStack, tempArgs, (h.valid.stackWorkspace.sub_left argStack).symm,
    cOut.sub_left retSub, cPre.sub_left retSub, cExp.sub_left retSub,
    cTmp.sub_left retSub, cWork.sub_left retSub, cArgs.sub_left retSub,
    cOut.sub_left belowSub, cPre.sub_left belowSub, cExp.sub_left belowSub,
    cTmp.sub_left belowSub, cWork.sub_left belowSub, cArgs.sub_left belowSub,
    h.valid.outputFit, h.valid.precomputationFit, h.valid.sourceFits 1,
    h.valid.temporaryFit, h.valid.workspaceFit, ⟨h.valid.minLength, h.valid.maxLength⟩, rfl,
    trivial, h.valid.exponentPositive, h.valid.exponentFits, publicScratch_le ⟨h.valid.minLength, h.valid.maxLength⟩ h.valid.space⟩

end VG.Proof.Rsa.X86.PrivChecked
