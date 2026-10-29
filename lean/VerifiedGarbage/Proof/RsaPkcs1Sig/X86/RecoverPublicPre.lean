module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverContext
public import VerifiedGarbage.Impl.RsaPkcs1Sig.X86.Recover

import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverLocal
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverStackWord
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverRegions
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverLocalArgument
import VerifiedGarbage.Proof.Framework.Offset
/-! # The precomputed public call is safe after the signature-length check -/

-- Formerly `VerifiedGarbage/Proof/RsaPkcs1Sig/X86/RecoverArguments.lean`, which only this module imported.
section

/-! # Installing successive cdecl arguments preserves every earlier word -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Rcv
open VG VG.X86 VG.Proof.Bignum.X86 VG.Proof.Mont.X86

def Arguments (g : Geometry) (values : Nat → BitVec 32) (n : Nat) (s : State) : Prop :=
  ∀ j < n, s.mem.readW (byteAddr g.stack + BitVec.ofNat 64 (4 * j)) 32 = values j

theorem Arguments.append {g : Geometry} {values : Nat → BitVec 32} {n : Nat} {s t : State}
    (h : Arguments g values n s) (hn : n < 10)
    (M : t.mem = s.mem.writeW (byteAddr g.stack + BitVec.ofNat 64 (4 * n)) (values n))
    (F : Frame [⟨byteAddr g.stack + BitVec.ofNat 64 (4 * n), 4⟩] s.mem t.mem) :
    Arguments g values (n + 1) t := by
  intro j hj
  by_cases same : j = n
  · subst j; rw [M, Mem.readW_writeW_self32]
  · rw [outgoing_word_preserved (by omega) hn same F]
    exact h j (by omega)

theorem slotFrame_outgoing {g : Geometry} {s t : State} {j : Nat} (hj : j < 10)
    (F : Frame [⟨byteAddr g.stack + BitVec.ofNat 64 (4 * j), 4⟩] s.mem t.mem) :
    Frame [⟨byteAddr g.stack, 40⟩] s.mem t.mem := F.sub (by
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  exact ⟨_, List.mem_singleton_self _, Offset.sub_base _ (by omega)⟩)

theorem prepareArgument_ok {g : Geometry} {bs : Fin 4 → List Byte} {s : State}
    {values : Nat → BitVec 32} {n : Nat} {code : List Instr}
    (a : Arguments g values n s) (hn : n < 10)
    (w : WP isa (.block code) s fun t => Context g bs t ∧
      t.mem = s.mem.writeW (byteAddr g.stack + BitVec.ofNat 64 (4 * n)) (values n) ∧
      Frame [⟨byteAddr g.stack + BitVec.ofNat 64 (4 * n), 4⟩] s.mem t.mem ∧ Keeps [.eax] s t) :
    WP isa (.block code) s fun t => Context g bs t ∧ Arguments g values (n + 1) t ∧
      Frame [⟨byteAddr g.stack, 40⟩] s.mem t.mem ∧ Keeps [.eax] s t := by
  refine WP.mono w ?_
  rintro t ⟨h, M, F, K⟩
  exact ⟨h, a.append hn M F, slotFrame_outgoing hn F, K⟩

end VG.Proof.RsaPkcs1Sig.X86.Rcv
end

end

-- Formerly `VerifiedGarbage/Proof/RsaPkcs1Sig/X86/RecoverCallArgs.lean`, which only this module imported.
section

/-! # All ten arguments of precomputed public RSA verification -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Rcv
open VG VG.X86 VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Sig.X86.Verify (em1Offset copyArgument localArgument)
open VG.Impl.RsaPkcs1Sig.X86.Recover (pubArgs)

def publicArgument (g : Geometry) (j : Nat) : BitVec 32 :=
  match j with
  | 0 => g.em1 | 1 => BitVec.ofNat 32 g.length
  | 2 => g.sources 3 | 3 => BitVec.ofNat 32 g.preLength
  | 4 => g.sources 1 | 5 => BitVec.ofNat 32 g.exponentLength
  | 6 => g.sources 2 | 7 => BitVec.ofNat 32 g.length
  | 8 => g.workspace | _ => BitVec.ofNat 32 g.scratchLength

private def inputSlot (j : Nat) : Nat :=
  match j with
  | 1 => 3 | 2 => 11 | 3 => 12 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 3 | 8 => 9 | _ => 10

theorem pubArgs_ok {g : Geometry} {bs : Fin 4 → List Byte} {s : State}
    (h : Context g bs s) :
    WP isa (.block pubArgs) s fun t => Context g bs t ∧ Arguments g (publicArgument g) 10 t ∧
      Frame [⟨byteAddr g.stack, 40⟩] s.mem t.mem ∧ Keeps [.eax] s t := by
  have first : WP isa (.block (localArgument em1Offset 0)) s fun t =>
      Context g bs t ∧ Arguments g (publicArgument g) 1 t ∧
      Frame [⟨byteAddr g.stack, 40⟩] s.mem t.mem ∧ Keeps [.eax] s t := by
    apply prepareArgument_ok (bs := bs) (n := 0) (by intro j hj; omega) (by decide)
    exact localArgument_ok s h em1Offset (by decide)
  have next {u : State} (hu : Context g bs u) {j : Nat} (hj : 1 ≤ j) (hj' : j < 10)
      (a : Arguments g (publicArgument g) j u) :
      WP isa (.block (copyArgument (inputSlot j) j)) u fun t =>
        Context g bs t ∧ Arguments g (publicArgument g) (j + 1) t ∧
        Frame [⟨byteAddr g.stack, 40⟩] u.mem t.mem ∧ Keeps [.eax] u t := by
    have inputBound : inputSlot j < 13 := by
      rcases (show j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 by omega) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have value : g.argument (inputSlot j) = publicArgument g j := by
      rcases (show j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 by omega) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    apply prepareArgument_ok (bs := bs) a hj'
    refine WP.mono (copyArgument_ok u hu inputBound hj') ?_
    rintro t ⟨ht, M, F, K⟩
    exact ⟨ht, by rw [value] at M; exact M, F, K⟩
  have copyMany (n : Nat) (hn : n ≤ 9) {u : State} (hu : Context g bs u)
      (a : Arguments g (publicArgument g) 1 u) :
      WP isa (.block ((List.range n).flatMap fun j => copyArgument (inputSlot (j + 1)) (j + 1))) u
        fun t => Context g bs t ∧ Arguments g (publicArgument g) (n + 1) t ∧
          Frame [⟨byteAddr g.stack, 40⟩] u.mem t.mem ∧ Keeps [.eax] u t := by
    induction n generalizing u with
    | zero => exact WP.block_nil ⟨hu, a, Frame.refl _ _, Keeps.refl _ _⟩
    | succ n ih =>
      rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
      refine WP.mono (ih (by omega) hu a) ?_
      rintro v ⟨hv, av, F, K⟩
      refine WP.mono (next hv (by omega) (by omega) av) ?_
      rintro t ⟨ht, args, Ft, Kt⟩
      exact ⟨ht, args, F.trans Ft, K.trans Kt⟩
  have code : pubArgs = localArgument em1Offset 0 ++
      (List.range 9).flatMap (fun j => copyArgument (inputSlot (j + 1)) (j + 1)) := rfl
  rw [code, WP.block_append_iff]
  refine WP.mono first ?_
  rintro u ⟨hu, args, F, K⟩
  refine WP.mono (copyMany 9 (by decide) hu args) ?_
  rintro t ⟨ht, argsT, Ft, Kt⟩
  exact ⟨ht, argsT, F.trans Ft, K.trans Kt⟩

end VG.Proof.RsaPkcs1Sig.X86.Rcv
end

end

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
    (Spec.Rsa.publicPrecomputedCheckedContract abi 96).pre (s.callEntry.withRegions (publicRd g) (publicWr g)) := by
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
    VG.X86.below_sub (by decide : 4 ≤ 100) h.valid.stackLow
  have belowSub : (⟨(g.stack - 4).setWidth 64 - 96#64, 96⟩ : Region).Sub g.calleeRegion := by
    rw [← VG.X86.Taint.sub_setWidth (by rw [low]; have := h.valid.stackLow; omega : 96 ≤ (g.stack - 4).toNat)]
    exact VG.X86.below_inner (by decide : 96 + 4 ≤ 100) h.valid.stackLow
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
