module

public import VerifiedGarbage.Proof.Rsa.X86.PrivPrecomputeArgs
import VerifiedGarbage.Proof.Rsa.Scratch
import VerifiedGarbage.Proof.Rsa.X86.PrivStackWord
import VerifiedGarbage.Proof.Rsa.X86.PrivRegions
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract

/-! # Public precomputation's cdecl arguments and disjoint buffer contract -/

@[expose] public section
namespace VG.Proof.Rsa.X86.PrivChecked
open VG VG.X86 VG.Impl.Rsa.X86.PrivChecked VG.Proof.Bignum.X86

def pcRd (g : PrivGeometry) : List Region := [g.sourceRegion 0]
def pcWr (g : PrivGeometry) : List Region :=
  [⟨byteAddr g.precomputation, 16 * Spec.Rsa.modulusWords g.length⟩, g.workspaceRegion, ⟨byteAddr g.stack, 24⟩]

theorem pcArgs_values {g : PrivGeometry} {bs : Fin 8 → List Byte} {s : State}
    (h : PrivContext g bs s) (a : Arguments g (pcArgument g) 6 s) {j : Nat} (hj : j < 6) :
    arg (s.callEntry.withRegions (pcRd g) (pcWr g)) j = pcArgument g j := by
  rw [arg_withRegions, arg_callEntry (by rw [h.sp]; have := h.valid.stackLow; omega)
    (by rw [h.sp]; have := h.valid.stackHigh; omega)]
  change s.mem.readW (addr (s.gpr .esp) (4 * j)) 32 = _
  rw [h.address (by omega)]
  exact a j hj

theorem pcCall_pre {g : PrivGeometry} {bs : Fin 8 → List Byte} {s : State}
    (h : PrivContext g bs s) (a : Arguments g (pcArgument g) 6 s) :
    (Spec.Rsa.publicPrecomputeContract abi 96).pre (s.callEntry.withRegions (pcRd g) (pcWr g)) := by
  have sa := fun {j} (hj : j < 6) => pcArgs_values h a hj
  have kfit : g.length < 2 ^ 32 := by have := h.valid.maxLength; omega
  have wfit : g.scratchLength < 2 ^ 32 := by have := h.valid.workspaceFit; omega
  have pfit : 2 * Spec.Rsa.modulusWords g.length < 2 ^ 32 := by
    have := h.valid.maxLength; simp only [Spec.Rsa.modulusWords]; omega
  sig_pre [Spec.Rsa.publicPrecomputeContract, Spec.Rsa.publicPrecomputeSig, abi, argSlots, argVal, argBytes, stackBelow]
  simp only [sa (by decide : 0 < 6), sa (by decide : 1 < 6), sa (by decide : 2 < 6),
    sa (by decide : 3 < 6), sa (by decide : 4 < 6), sa (by decide : 5 < 6), pcArgument,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt kfit, Nat.mod_eq_of_lt wfit, Nat.mod_eq_of_lt pfit,
    argAddr_withRegions, argAddr_callEntry, h.sp, Nat.mul_zero, BitVec.add_zero]
  rw [show 2 * Spec.Rsa.modulusWords g.length * 8 = 16 * Spec.Rsa.modulusWords g.length by omega,
    show g.scratchLength * 8 = 8 * g.scratchLength from Nat.mul_comm _ _]
  have preSub : (⟨byteAddr g.precomputation, 16 * Spec.Rsa.modulusWords g.length⟩ : Region).Sub g.innerRegion := by
    rw [PrivGeometry.precomputation, h.valid.offsetAddr (by decide)]
    exact Offset.sub_base _ (by have := h.valid.maxLength; simp only [precomputeOffset, VG.Impl.Rsa.X86.PrivChecked.frameBytes, Spec.Rsa.modulusWords]; omega)
  have preStack : (⟨byteAddr g.precomputation, 16 * Spec.Rsa.modulusWords g.length⟩ : Region).Sub g.wholeStack :=
    fun x hx => h.valid.innerSub x (preSub x hx)
  have argSub : (⟨byteAddr g.stack, 24⟩ : Region).Sub g.innerRegion := Region.sub_prefix (by decide)
  have preArgs : (⟨byteAddr g.precomputation, 16 * Spec.Rsa.modulusWords g.length⟩ : Region).Disjoint ⟨byteAddr g.stack, 24⟩ := by
    rw [PrivGeometry.precomputation, h.valid.offsetAddr (by decide)]
    exact Offset.disjoint_base _ (by decide : 24 ≤ precomputeOffset)
      (by have := h.valid.maxLength; simp only [precomputeOffset, Spec.Rsa.modulusWords]; omega)
  have low : (g.stack - 4).toNat = g.stack.toNat - 4 := sub_toNat (k := 4) (by have := h.valid.stackLow; omega)
  have retSub : (⟨(g.stack - 4).setWidth 64, 4⟩ : Region).Sub g.calleeRegion :=
    VG.X86.below_sub (by decide : 4 ≤ 100) h.valid.stackLow
  have belowSub : (⟨(g.stack - 4).setWidth 64 - 96#64, 96⟩ : Region).Sub g.calleeRegion := by
    rw [← VG.X86.Taint.sub_setWidth (by rw [low]; have := h.valid.stackLow; omega : 96 ≤ (g.stack - 4).toNat)]
    exact VG.X86.below_inner (by decide : 96 + 4 ≤ 100) h.valid.stackLow
  have calleeSource := (h.valid.stackSources 0).sub_left h.valid.calleeSub
  have calleeWorkspace := h.valid.stackWorkspace.sub_left h.valid.calleeSub
  have calleePre := h.valid.calleeInner.sub_right preSub
  have calleeArgs := h.valid.calleeInner.sub_right argSub
  rw [low]
  exact ⟨by have := h.valid.stackLow; omega, by have := h.valid.stackHigh; omega, rfl, rfl,
    (h.valid.stackSources 0).sub_left preStack, h.valid.stackWorkspace.sub_left preStack, preArgs,
    h.valid.sourcesWorkspace 0,
    ((h.valid.stackSources 0).sub_left (fun x hx => h.valid.innerSub x (argSub x hx))).symm,
    (h.valid.stackWorkspace.sub_left (fun x hx => h.valid.innerSub x (argSub x hx))).symm,
    calleePre.sub_left retSub, calleeSource.sub_left retSub, calleeWorkspace.sub_left retSub, calleeArgs.sub_left retSub,
    calleePre.sub_left belowSub, calleeSource.sub_left belowSub, calleeWorkspace.sub_left belowSub, calleeArgs.sub_left belowSub,
    h.valid.precomputationFit, h.valid.sourceFits 0, h.valid.workspaceFit,
    ⟨h.valid.minLength, h.valid.maxLength⟩, rfl, publicScratch_le ⟨h.valid.minLength, h.valid.maxLength⟩ h.valid.space⟩

end VG.Proof.Rsa.X86.PrivChecked
