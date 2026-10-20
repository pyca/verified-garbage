module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignCallArgs
public import VerifiedGarbage.Proof.Rsa.X86.PrivImpl
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignEncoding
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignPrivateRegions
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignStackWord
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignRegions
import VerifiedGarbage.Proof.Framework.Sig

/-! # The signing call satisfies the checked RSA contract -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Sgn
open VG VG.X86 VG.Proof.Bignum.X86 VG.Proof.Rsa.X86.PrivChecked

def privateRd (g : Geometry) : List Region :=
  [g.sourceRegion 0, g.sourceRegion 1, ⟨byteAddr g.temporary, g.length⟩,
    g.sourceRegion 3, g.sourceRegion 4, g.sourceRegion 5, g.sourceRegion 6, g.sourceRegion 7]
def privateWr (g : Geometry) : List Region :=
  [g.outputRegion, g.workspaceRegion, ⟨byteAddr g.stack, 80⟩]

theorem privateArgs_values {g : Geometry} {bs : Fin 8 → List Byte} {s : State}
    (h : Context g bs s) (a : PrivateArgs g s) {j : Nat} (hj : j < 20) :
    arg (s.callEntry.withRegions (privateRd g) (privateWr g)) j = privateArgument g j := by
  rw [arg_withRegions, arg_callEntry (by rw [h.sp]; have := h.valid.stackLow; simp only [calleeBytes] at this; omega)
    (by rw [h.sp]; have := h.valid.stackHigh; omega)]
  change s.mem.readW (addr (s.gpr .esp) (4 * j)) 32 = _
  rw [h.address (by omega)]
  exact a j hj

theorem privateCall_pre {g : Geometry} {bs : Fin 8 → List Byte} {s : State}
    (h : Context g bs s) (a : PrivateArgs g s) :
    (Spec.Rsa.privateCheckedContract abi stackBytes).pre (s.callEntry.withRegions (privateRd g) (privateWr g)) := by
  have sa := fun {j} (hj : j < 20) => privateArgs_values h a hj
  have kfit : g.length < 2 ^ 32 := by have := h.valid.maxLength; omega
  have efit : g.exponentLength < 2 ^ 32 := by have := h.valid.exponentFits; omega
  have pfit : g.pLength < 2 ^ 32 := by have := h.valid.pFits; omega
  have qfit : g.qLength < 2 ^ 32 := by have := h.valid.qFits; omega
  have wfit : g.scratchLength < 2 ^ 32 := by have := h.valid.workspaceFit; omega
  sig_pre [Spec.Rsa.privateCheckedContract, Spec.Rsa.privateCheckedSig, abi, argSlots, argVal, argBytes, stackBelow]
  simp only [sa (by decide : 0 < 20), sa (by decide : 1 < 20), sa (by decide : 2 < 20),
    sa (by decide : 3 < 20), sa (by decide : 4 < 20), sa (by decide : 5 < 20),
    sa (by decide : 6 < 20), sa (by decide : 7 < 20), sa (by decide : 8 < 20),
    sa (by decide : 9 < 20), sa (by decide : 10 < 20), sa (by decide : 11 < 20),
    sa (by decide : 12 < 20), sa (by decide : 13 < 20), sa (by decide : 14 < 20),
    sa (by decide : 15 < 20), sa (by decide : 16 < 20), sa (by decide : 17 < 20),
    sa (by decide : 18 < 20), sa (by decide : 19 < 20),
    privateArgument, Geometry.argument, Nat.reduceAdd, Nat.reduceLT, Nat.reduceEqDiff, ite_true, ite_false,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt kfit, Nat.mod_eq_of_lt efit, Nat.mod_eq_of_lt pfit,
    Nat.mod_eq_of_lt qfit, Nat.mod_eq_of_lt wfit,
    argAddr_withRegions, argAddr_callEntry, h.sp,
    Nat.mul_zero, BitVec.add_zero]

  rw [show g.scratchLength * 8 = 8 * g.scratchLength from Nat.mul_comm _ _]
  have tempStack := fun x hx => h.valid.innerSub x (h.temporarySub x hx)
  have argStack := fun x hx => h.valid.innerSub x (h.outgoingSub x hx)
  have cOut := h.valid.stackOutput.sub_left h.valid.calleeSub
  have cSource := fun i => (h.valid.stackSources i).sub_left h.valid.calleeSub
  have cTemp := h.valid.calleeInner.sub_right h.temporarySub
  have cWork := h.valid.stackWorkspace.sub_left h.valid.calleeSub
  have cArgs := h.valid.calleeInner.sub_right h.outgoingSub
  have sourceArgs := fun i => ((h.valid.stackSources i).sub_left argStack).symm
  have low : (g.stack - 4).toNat = g.stack.toNat - 4 :=
    sub_toNat (k := 4) (by have := h.valid.stackLow; simp only [calleeBytes] at this; omega)
  rw [low]
  exact ⟨by have := h.valid.stackLow; simp only [calleeBytes, stackBytes] at *; omega,
    by have := h.valid.stackHigh; omega,
    rfl,
    rfl,
    h.valid.outputSources 0,
    h.valid.outputSources 1,
    (h.valid.stackOutput.sub_left tempStack).symm,
    h.valid.outputSources 3,
    h.valid.outputSources 4,
    h.valid.outputSources 5,
    h.valid.outputSources 6,
    h.valid.outputSources 7,
    h.valid.outputWorkspace,
    (h.valid.stackOutput.sub_left argStack).symm,
    h.valid.sourcesWorkspace 0,
    sourceArgs 0,
    h.valid.sourcesWorkspace 1,
    sourceArgs 1,
    h.valid.stackWorkspace.sub_left tempStack,
    h.temporaryArgs,
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
    (h.valid.stackWorkspace.sub_left argStack).symm,
    cOut.sub_left h.retSub,
    (cSource 0).sub_left h.retSub,
    (cSource 1).sub_left h.retSub,
    cTemp.sub_left h.retSub,
    (cSource 3).sub_left h.retSub,
    (cSource 4).sub_left h.retSub,
    (cSource 5).sub_left h.retSub,
    (cSource 6).sub_left h.retSub,
    (cSource 7).sub_left h.retSub,
    cWork.sub_left h.retSub,
    cArgs.sub_left h.retSub,
    cOut.sub_left h.belowSub,
    (cSource 0).sub_left h.belowSub,
    (cSource 1).sub_left h.belowSub,
    cTemp.sub_left h.belowSub,
    (cSource 3).sub_left h.belowSub,
    (cSource 4).sub_left h.belowSub,
    (cSource 5).sub_left h.belowSub,
    (cSource 6).sub_left h.belowSub,
    (cSource 7).sub_left h.belowSub,
    cWork.sub_left h.belowSub,
    cArgs.sub_left h.belowSub,
    h.valid.outputFit,
    h.valid.sourceFits 0,
    h.valid.sourceFits 1,
    h.valid.temporaryFit,
    h.valid.sourceFits 3,
    h.valid.sourceFits 4,
    h.valid.sourceFits 5,
    h.valid.sourceFits 6,
    h.valid.sourceFits 7,
    h.valid.workspaceFit,
    ⟨h.valid.minLength, h.valid.maxLength⟩,
    trivial,
    trivial,
    h.valid.exponentPositive,
    h.valid.exponentFits,
    h.valid.pPositive,
    h.valid.pFits,
    h.valid.qPositive,
    h.valid.qFits,
    trivial,
    trivial,
    trivial,
    h.valid.space⟩

end VG.Proof.RsaPkcs1Sig.X86.Sgn
