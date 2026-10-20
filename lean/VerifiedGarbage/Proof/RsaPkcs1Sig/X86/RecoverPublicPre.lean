module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverCallArgs
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverLocal

/-! # The precomputed public call is safe after the signature-length check -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Rcv
open VG VG.X86 VG.Proof.Bignum.X86

def publicRd (g : Geometry) : List Region := [g.sourceRegion 3, g.sourceRegion 1, g.sourceRegion 2]
def publicWr (g : Geometry) : List Region :=
  [⟨byteAddr g.em1, g.length⟩, g.workspaceRegion, ⟨byteAddr g.stack, 40⟩]

theorem publicArgs_values {g : Geometry} {bs : Fin 4 → List Byte} {s : State}
    (h : Context g bs s) (a : Arguments g (publicArgument g) 10 s) {j : Nat} (hj : j < 10) :
    arg (s.callEntry.withRegions (publicRd g) (publicWr g)) j = publicArgument g j := by
  rw [arg_withRegions, arg_callEntry (by rw [h.sp]; have := h.valid.stackLow; omega)
    (by rw [h.sp]; have := h.valid.stackHigh; omega)]
  change s.mem.readW (addr (s.gpr .esp) (4 * j)) 32 = _
  rw [h.address (by omega)]
  exact a j hj

theorem publicCall_pre {g : Geometry} {bs : Fin 4 → List Byte} {s : State}
    (h : Context g bs s) (a : Arguments g (publicArgument g) 10 s) (siglen : g.signatureLength = g.length) :
    (Spec.Rsa.publicPrecomputedCheckedContract abi 40).pre (s.callEntry.withRegions (publicRd g) (publicWr g)) := by
  have sa := fun {j} (hj : j < 10) => publicArgs_values h a hj
  have kfit : g.length < 2 ^ 32 := by have := h.valid.maxLength; omega
  have efit : g.exponentLength < 2 ^ 32 := by have := h.valid.exponentFits; omega
  have wfit : g.scratchLength < 2 ^ 32 := by have := h.valid.workspaceFit; omega
  have pfit : g.preLength < 2 ^ 32 := by have := h.valid.sourceFits 3; change (g.sources 3).toNat + 8 * g.preLength ≤ 2 ^ 32 at this; omega
  sig_pre [Spec.Rsa.publicPrecomputedCheckedContract, Spec.Rsa.publicPrecomputedSig, abi, argSlots, argVal, argBytes, stackBelow]
  simp only [sa (by decide : 0 < 10), sa (by decide : 1 < 10), sa (by decide : 2 < 10),
    sa (by decide : 3 < 10), sa (by decide : 4 < 10), sa (by decide : 5 < 10),
    sa (by decide : 6 < 10), sa (by decide : 7 < 10), sa (by decide : 8 < 10), sa (by decide : 9 < 10),
    publicArgument, BitVec.toNat_ofNat, Nat.mod_eq_of_lt kfit, Nat.mod_eq_of_lt efit,
    Nat.mod_eq_of_lt wfit, Nat.mod_eq_of_lt pfit,
    argAddr_withRegions, argAddr_callEntry, h.sp, Nat.mul_zero, BitVec.add_zero]
  rw [show g.preLength * 8 = 8 * g.preLength from Nat.mul_comm _ _,
    show g.scratchLength * 8 = 8 * g.scratchLength from Nat.mul_comm _ _]
  have tempStack := fun x hx => h.valid.innerSub x (h.em1Sub x hx)
  have argsSub : (⟨byteAddr g.stack, 40⟩ : Region).Sub g.innerRegion := Region.sub_prefix (by decide)
  have argsStack := fun x hx => h.valid.innerSub x (argsSub x hx)
  have tempSource := fun i => (h.valid.stackSources i).sub_left tempStack
  have sourceArgs := fun i => ((h.valid.stackSources i).sub_left argsStack).symm
  have cSource := fun i => (h.valid.stackSources i).sub_left h.valid.calleeSub
  have cTemp := h.valid.calleeInner.sub_right h.em1Sub
  have cWork := h.valid.stackWorkspace.sub_left h.valid.calleeSub
  have cArgs := h.valid.calleeInner.sub_right argsSub
  have low : (g.stack - 4).toNat = g.stack.toNat - 4 := sub_toNat (k := 4) (by have := h.valid.stackLow; omega)
  have retSub : (⟨(g.stack - 4).setWidth 64, 4⟩ : Region).Sub g.calleeRegion :=
    VG.X86.below_sub (by decide : 4 ≤ 44) h.valid.stackLow
  have belowSub : (⟨(g.stack - 4).setWidth 64 - 40#64, 40⟩ : Region).Sub g.calleeRegion := by
    rw [← VG.X86.Taint.sub_setWidth (by rw [low]; have := h.valid.stackLow; omega : 40 ≤ (g.stack - 4).toNat)]
    exact VG.X86.below_inner (by decide : 40 + 4 ≤ 44) h.valid.stackLow
  rw [low]
  have sourceSig : g.sourceRegion 2 = ⟨(g.sources 2).setWidth 64, g.length⟩ := by
    change (⟨byteAddr (g.sources 2), g.signatureLength⟩ : Region) = _
    rw [siglen]
    rfl
  have sourcePre : g.sourceRegion 3 = ⟨(g.sources 3).setWidth 64, 8 * g.preLength⟩ := rfl
  have sfSig : (g.sources 2).toNat + g.length ≤ 2 ^ 32 := by
    have fit := h.valid.sourceFits 2
    change (g.sources 2).toNat + g.signatureLength ≤ 2 ^ 32 at fit
    rw [siglen] at fit
    exact fit
  have emFit := h.valid.encodingFit (d := VG.Impl.RsaPkcs1Sig.X86.Verify.em1Offset)
    (by have := h.valid.maxLength; simp only [VG.Impl.RsaPkcs1Sig.X86.Verify.em1Offset, VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes]; omega)
  exact ⟨by have := h.valid.stackLow; omega, by have := h.valid.stackHigh; omega,
    by unfold publicRd; rw [sourcePre, sourceSig]; rfl, rfl,
    tempSource 3, tempSource 1, by rw [← sourceSig]; exact tempSource 2,
    h.valid.stackWorkspace.sub_left tempStack, h.em1Args,
    h.valid.sourcesWorkspace 3, sourceArgs 3,
    h.valid.sourcesWorkspace 1, sourceArgs 1,
    by rw [← sourceSig]; exact h.valid.sourcesWorkspace 2,
    by rw [← sourceSig]; exact sourceArgs 2,
    (h.valid.stackWorkspace.sub_left argsStack).symm,
    cTemp.sub_left retSub, (cSource 3).sub_left retSub, (cSource 1).sub_left retSub,
    by rw [← sourceSig]; exact (cSource 2).sub_left retSub,
    cWork.sub_left retSub, cArgs.sub_left retSub,
    cTemp.sub_left belowSub, (cSource 3).sub_left belowSub, (cSource 1).sub_left belowSub,
    by rw [← sourceSig]; exact (cSource 2).sub_left belowSub,
    cWork.sub_left belowSub, cArgs.sub_left belowSub,
    emFit, h.valid.sourceFits 3, h.valid.sourceFits 1, sfSig, h.valid.workspaceFit,
    ⟨h.valid.minLength, h.valid.maxLength⟩, h.valid.precomputed, trivial,
    h.valid.exponentPositive, h.valid.exponentFits, h.valid.space⟩

end VG.Proof.RsaPkcs1Sig.X86.Rcv
