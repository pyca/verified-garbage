module

public import VerifiedGarbage.Proof.Rsa.X86.PrivSaveStatus
import VerifiedGarbage.Proof.Rsa.Scratch
import VerifiedGarbage.Proof.Rsa.X86.PrivStackWord
import VerifiedGarbage.Proof.Rsa.X86.PrivRegions
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Rsa.X86.PrivPrecomputeLength
import VerifiedGarbage.Proof.Rsa.X86.PrivLocalArgument
public import VerifiedGarbage.Proof.Rsa.Contract

/-! ### `Rsa.X86.PrivPublicPre`, which the modules that import this one used -/

section

/-! ### `Rsa.X86.PrivPublicArgs`, which this module and modules that import it used -/

section

/-! # Preparing public re-exponentiation while retaining both prior call results -/

@[expose] public section
namespace VG.Proof.Rsa.X86.PrivChecked
open VG VG.X86 VG.Impl.Rsa.X86.PrivChecked VG.Proof.Bignum.X86 VG.Proof.Mont.X86

def pdArgument (g : PrivGeometry) (j : Nat) : BitVec 32 :=
  match j with
  | 0 => g.output | 1 => BitVec.ofNat 32 g.length
  | 2 => g.precomputation | 3 => BitVec.ofNat 32 (2 * Spec.Rsa.modulusWords g.length)
  | 4 => g.sources 1 | 5 => BitVec.ofNat 32 g.exponentLength
  | 6 => g.temporary | 7 => BitVec.ofNat 32 g.length
  | 8 => g.workspace | _ => BitVec.ofNat 32 g.scratchLength

theorem publicSetup_ok (s : State) {g : PrivGeometry} {bs : Fin 8 → List Byte}
    (h : PrivContext g bs s) :
    WP isa (.block (copyArgument 0 0 ++ copyArgument 1 1 ++ localArgument precomputeOffset 2 ++ precomputeLength 3 ++
      copyArgument 4 4 ++ copyArgument 5 5 ++ localArgument candidateOffset 6 ++ copyArgument 7 7 ++
      copyArgument 18 8 ++ copyArgument 19 9)) s fun t =>
      PrivContext g bs t ∧ Arguments g (pdArgument g) 10 t ∧
      Frame [⟨byteAddr g.stack, 72⟩] s.mem t.mem ∧ Keeps [.eax] s t := by
  simp only [List.append_assoc]
  have A0 : Arguments g (pdArgument g) 0 s := by intro j hj; omega
  rw [WP.block_append_iff]
  refine WP.mono (prepareArgument_ok A0 (by decide : 0 < 18) (copyArgument_ok s h (by decide : 0 < 20) (by decide : 0 < 18))) ?_
  rintro s1 ⟨h1, A1, F1, K1⟩
  rw [WP.block_append_iff]
  refine WP.mono (prepareArgument_ok A1 (by decide : 1 < 18) (copyArgument_ok s1 h1 (by decide : 1 < 20) (by decide : 1 < 18))) ?_
  rintro s2 ⟨h2, A2, F2, K2⟩
  rw [WP.block_append_iff]
  refine WP.mono (prepareArgument_ok A2 (by decide : 2 < 18) (localArgument_ok s2 h2 precomputeOffset (by decide : 2 < 18))) ?_
  rintro s3 ⟨h3, A3, F3, K3⟩
  rw [WP.block_append_iff]
  refine WP.mono (prepareArgument_ok A3 (by decide : 3 < 18) (precomputeLength_ok s3 h3 (by decide : 3 < 18))) ?_
  rintro s4 ⟨h4, A4, F4, K4⟩
  rw [WP.block_append_iff]
  refine WP.mono (prepareArgument_ok A4 (by decide : 4 < 18) (copyArgument_ok s4 h4 (by decide : 4 < 20) (by decide : 4 < 18))) ?_
  rintro s5 ⟨h5, A5, F5, K5⟩
  rw [WP.block_append_iff]
  refine WP.mono (prepareArgument_ok A5 (by decide : 5 < 18) (copyArgument_ok s5 h5 (by decide : 5 < 20) (by decide : 5 < 18))) ?_
  rintro s6 ⟨h6, A6, F6, K6⟩
  rw [WP.block_append_iff]
  refine WP.mono (prepareArgument_ok A6 (by decide : 6 < 18) (localArgument_ok s6 h6 candidateOffset (by decide : 6 < 18))) ?_
  rintro s7 ⟨h7, A7, F7, K7⟩
  rw [WP.block_append_iff]
  refine WP.mono (prepareArgument_ok A7 (by decide : 7 < 18) (copyArgument_ok s7 h7 (by decide : 7 < 20) (by decide : 7 < 18))) ?_
  rintro s8 ⟨h8, A8, F8, K8⟩
  rw [WP.block_append_iff]
  refine WP.mono (prepareArgument_ok A8 (by decide : 8 < 18) (copyArgument_ok s8 h8 (by decide : 18 < 20) (by decide : 8 < 18))) ?_
  rintro s9 ⟨h9, A9, F9, K9⟩
  refine WP.mono (prepareArgument_ok A9 (by decide : 9 < 18) (copyArgument_ok s9 h9 (by decide : 19 < 20) (by decide : 9 < 18))) ?_
  rintro s10 ⟨h10, A10, F10, K10⟩
  exact ⟨h10, A10, F1.trans (F2.trans (F3.trans (F4.trans (F5.trans (F6.trans (F7.trans (F8.trans (F9.trans (F10))))))))), K1.trans (K2.trans (K3.trans (K4.trans (K5.trans (K6.trans (K7.trans (K8.trans (K9.trans (K10)))))))))⟩

theorem publicArgs_ok (s : State) {g : PrivGeometry} {bs : Fin 8 → List Byte}
    (h : PrivContext g bs s) :
    WP isa (.block publicArgs) s fun t => PrivContext g bs t ∧ Arguments g (pdArgument g) 10 t ∧
      t.mem.readW (byteAddr g.stack + BitVec.ofNat 64 precomputeStatusOffset) 32 = s.gpr .eax ∧
      t.mem.readW (byteAddr g.stack + BitVec.ofNat 64 crtStatusOffset) 32 =
        s.mem.readW (byteAddr g.stack + BitVec.ofNat 64 crtStatusOffset) 32 ∧
      Frame [⟨byteAddr g.stack, 88⟩] s.mem t.mem ∧ Keeps [.eax] s t := by
  unfold publicArgs
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (saveStatus_ok s h (by decide : precomputeStatusOffset + 4 ≤ 88)) ?_
  rintro u ⟨hu, M, F, K⟩
  have setup := publicSetup_ok u hu
  simp only [List.append_assoc] at setup
  refine WP.mono setup ?_
  rintro t ⟨ht, A, F', K'⟩
  refine ⟨ht, A, ?_, ?_, (F.sub ?_).trans (F'.sub ?_), (K.mono (by simp)).trans K'⟩
  · rw [status_preserved (by decide : 72 ≤ precomputeStatusOffset)
      (by decide : precomputeStatusOffset + 4 ≤ 88) F', M, Mem.readW_writeW_self32]
  · rw [status_preserved (by decide : 72 ≤ crtStatusOffset) (by decide : crtStatusOffset + 4 ≤ 88) F']
    apply F.readW (r := ⟨byteAddr g.stack + BitVec.ofNat 64 crtStatusOffset, 4⟩) (Region.contains_self _ _) ?_ (by decide)
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact Offset.disjoint _ (Or.inl (by decide : crtStatusOffset + 4 ≤ precomputeStatusOffset)) (by decide) (by decide)
  · intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨_, List.mem_singleton_self _, Offset.sub_base _ (by decide : precomputeStatusOffset + 4 ≤ 88)⟩
  · intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by decide : 72 ≤ 88)⟩

end VG.Proof.Rsa.X86.PrivChecked

end

end

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
  rw [arg_withRegions, arg_callEntry (by rw [h.sp]; have := h.valid.stackLow; omega_using [this])
    (by rw [h.sp]; have := h.valid.stackHigh; omega_using [hj, this])]
  change s.mem.readW (addr (s.gpr .esp) (4 * j)) 32 = _
  rw [h.address (by omega_using [hj])]
  exact a j hj

theorem pdCall_pre {g : PrivGeometry} {bs : Fin 8 → List Byte} {s : State}
    (h : PrivContext g bs s) (a : Arguments g (pdArgument g) 10 s) :
    (Proof.Rsa.publicPrecomputedCheckedContract abi 96).pre (s.callEntry.withRegions (pdRd g) (pdWr g)) := by
  have sa := fun {j} (hj : j < 10) => pdArgs_values h a hj
  have kfit : g.length < 2 ^ 32 := by have := h.valid.maxLength; omega_using [this]
  have efit : g.exponentLength < 2 ^ 32 := by have := h.valid.exponentFits; omega_using [kfit, this]
  have wfit : g.scratchLength < 2 ^ 32 := by have := h.valid.workspaceFit; omega_using [this]
  have pfit : 2 * Spec.Rsa.modulusWords g.length < 2 ^ 32 := by
    have := h.valid.maxLength; simp only [Spec.Rsa.modulusWords]; omega_using [kfit]
  sig_pre [Proof.Rsa.publicPrecomputedCheckedContract, Proof.Rsa.publicPrecomputedSig, abi, argSlots, argVal, argBytes, stackBelow]
  simp only [sa (by decide : 0 < 10), sa (by decide : 1 < 10), sa (by decide : 2 < 10),
    sa (by decide : 3 < 10), sa (by decide : 4 < 10), sa (by decide : 5 < 10),
    sa (by decide : 6 < 10), sa (by decide : 7 < 10), sa (by decide : 8 < 10),
    sa (by decide : 9 < 10), pdArgument, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt kfit, Nat.mod_eq_of_lt efit, Nat.mod_eq_of_lt wfit, Nat.mod_eq_of_lt pfit,
    argAddr_withRegions, argAddr_callEntry, h.sp, Nat.mul_zero, BitVec.add_zero]
  rw [show 2 * Spec.Rsa.modulusWords g.length * 8 = 16 * Spec.Rsa.modulusWords g.length by omega_using [],
    show g.scratchLength * 8 = 8 * g.scratchLength from Nat.mul_comm _ _]
  have preSub : (⟨byteAddr g.precomputation, 16 * Spec.Rsa.modulusWords g.length⟩ : Region).Sub g.innerRegion := by
    rw [PrivGeometry.precomputation, h.valid.offsetAddr (by decide)]
    exact Offset.sub_base _ (by have := h.valid.maxLength; simp only [precomputeOffset, VG.Impl.Rsa.X86.PrivChecked.frameBytes, Spec.Rsa.modulusWords]; omega_using [this])
  have tempSub : (⟨byteAddr g.temporary, g.length⟩ : Region).Sub g.innerRegion := by
    rw [PrivGeometry.temporary, h.valid.offsetAddr (by decide)]
    exact Offset.sub_base _ (by have := h.valid.maxLength; simp only [candidateOffset, VG.Impl.Rsa.X86.PrivChecked.frameBytes]; omega_using [this])
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
      (by have := h.valid.maxLength; simp only [precomputeOffset, Spec.Rsa.modulusWords]; omega_using [kfit])
  have tempArgs : (⟨byteAddr g.temporary, g.length⟩ : Region).Disjoint ⟨byteAddr g.stack, 40⟩ := by
    rw [PrivGeometry.temporary, h.valid.offsetAddr (by decide)]
    exact Offset.disjoint_base _ (by decide : 40 ≤ candidateOffset)
      (by have := h.valid.maxLength; simp only [candidateOffset]; omega_using [kfit])
  have low : (g.stack - 4).toNat = g.stack.toNat - 4 := sub_toNat (k := 4) (by have := h.valid.stackLow; omega_using [this])
  have retSub : (⟨(g.stack - 4).setWidth 64, 4⟩ : Region).Sub g.calleeRegion :=
    VG.X86.below_sub (by decide : 4 ≤ 100) h.valid.stackLow
  have belowSub : (⟨(g.stack - 4).setWidth 64 - 96#64, 96⟩ : Region).Sub g.calleeRegion := by
    rw [← VG.X86.Taint.sub_setWidth (by rw [low]; have := h.valid.stackLow; omega_using [this] : 96 ≤ (g.stack - 4).toNat)]
    exact VG.X86.below_inner (by decide : 96 + 4 ≤ 100) h.valid.stackLow
  have cOut := h.valid.stackOutput.sub_left h.valid.calleeSub
  have cPre := h.valid.calleeInner.sub_right preSub
  have cExp := (h.valid.stackSources 1).sub_left h.valid.calleeSub
  have cTmp := h.valid.calleeInner.sub_right tempSub
  have cWork := h.valid.stackWorkspace.sub_left h.valid.calleeSub
  have cArgs := h.valid.calleeInner.sub_right argSub
  rw [low]
  exact ⟨by have := h.valid.stackLow; omega_using [this], by have := h.valid.stackHigh; omega_using [this], rfl, rfl,
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

end

end

/-! # Public precomputation's cdecl arguments and disjoint buffer contract -/

-- Formerly `VerifiedGarbage/Proof/Rsa/X86/PrivPrecomputeArgs.lean`, which only this module imported.
section

/-! # Retaining the CRT status and preparing the public-key precomputation call -/

@[expose] public section
namespace VG.Proof.Rsa.X86.PrivChecked
open VG VG.X86 VG.Impl.Rsa.X86.PrivChecked VG.Proof.Bignum.X86 VG.Proof.Mont.X86

def pcArgument (g : PrivGeometry) (j : Nat) : BitVec 32 :=
  match j with
  | 0 => g.precomputation
  | 1 => BitVec.ofNat 32 (2 * Spec.Rsa.modulusWords g.length)
  | 2 => g.sources 0
  | 3 => BitVec.ofNat 32 g.length
  | 4 => g.workspace
  | _ => BitVec.ofNat 32 g.scratchLength

theorem precomputeSetup_ok (s : State) {g : PrivGeometry} {bs : Fin 8 → List Byte}
    (h : PrivContext g bs s) :
    WP isa (.block (localArgument precomputeOffset 0 ++ precomputeLength 1 ++
      copyArgument 2 2 ++ copyArgument 3 3 ++ copyArgument 18 4 ++ copyArgument 19 5)) s fun t =>
      PrivContext g bs t ∧ Arguments g (pcArgument g) 6 t ∧
      Frame [⟨byteAddr g.stack, 72⟩] s.mem t.mem ∧ Keeps [.eax] s t := by
  simp only [List.append_assoc]
  have A0 : Arguments g (pcArgument g) 0 s := by intro j hj; omega
  rw [WP.block_append_iff]
  refine WP.mono (prepareArgument_ok A0 (by decide : 0 < 18) (localArgument_ok s h precomputeOffset (by decide : 0 < 18))) ?_
  rintro s1 ⟨h1, A1, F1, K1⟩
  rw [WP.block_append_iff]
  refine WP.mono (prepareArgument_ok A1 (by decide : 1 < 18) (precomputeLength_ok s1 h1 (by decide : 1 < 18))) ?_
  rintro s2 ⟨h2, A2, F2, K2⟩
  rw [WP.block_append_iff]
  refine WP.mono (prepareArgument_ok A2 (by decide : 2 < 18) (copyArgument_ok s2 h2 (by decide : 2 < 20) (by decide : 2 < 18))) ?_
  rintro s3 ⟨h3, A3, F3, K3⟩
  rw [WP.block_append_iff]
  refine WP.mono (prepareArgument_ok A3 (by decide : 3 < 18) (copyArgument_ok s3 h3 (by decide : 3 < 20) (by decide : 3 < 18))) ?_
  rintro s4 ⟨h4, A4, F4, K4⟩
  rw [WP.block_append_iff]
  refine WP.mono (prepareArgument_ok A4 (by decide : 4 < 18) (copyArgument_ok s4 h4 (by decide : 18 < 20) (by decide : 4 < 18))) ?_
  rintro s5 ⟨h5, A5, F5, K5⟩
  refine WP.mono (prepareArgument_ok A5 (by decide : 5 < 18) (copyArgument_ok s5 h5 (by decide : 19 < 20) (by decide : 5 < 18))) ?_
  rintro s6 ⟨h6, A6, F6, K6⟩
  exact ⟨h6, A6, F1.trans (F2.trans (F3.trans (F4.trans (F5.trans (F6))))), K1.trans (K2.trans (K3.trans (K4.trans (K5.trans (K6)))))⟩

theorem precomputeArgs_ok (s : State) {g : PrivGeometry} {bs : Fin 8 → List Byte}
    (h : PrivContext g bs s) :
    WP isa (.block precomputeArgs) s fun t => PrivContext g bs t ∧ Arguments g (pcArgument g) 6 t ∧
      t.mem.readW (byteAddr g.stack + BitVec.ofNat 64 crtStatusOffset) 32 = s.gpr .eax ∧
      Frame [⟨byteAddr g.stack, 88⟩] s.mem t.mem ∧ Keeps [.eax] s t := by
  unfold precomputeArgs
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (saveStatus_ok s h (by decide : crtStatusOffset + 4 ≤ 88)) ?_
  rintro u ⟨hu, M, F, K⟩
  have setup := precomputeSetup_ok u hu
  simp only [List.append_assoc] at setup
  refine WP.mono setup ?_
  rintro t ⟨ht, A, F', K'⟩
  refine ⟨ht, A, ?_, (F.sub ?_).trans (F'.sub ?_), (K.mono (by simp)).trans K'⟩
  · rw [status_preserved (by decide : 72 ≤ crtStatusOffset) (by decide : crtStatusOffset + 4 ≤ 88) F',
      M, Mem.readW_writeW_self32]
  · intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨_, List.mem_singleton_self _, Offset.sub_base _ (by decide : crtStatusOffset + 4 ≤ 88)⟩
  · intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by decide : 72 ≤ 88)⟩

end VG.Proof.Rsa.X86.PrivChecked
end

end

@[expose] public section
namespace VG.Proof.Rsa.X86.PrivChecked
open VG VG.X86 VG.Impl.Rsa.X86.PrivChecked VG.Proof.Bignum.X86

def pcRd (g : PrivGeometry) : List Region := [g.sourceRegion 0]
def pcWr (g : PrivGeometry) : List Region :=
  [⟨byteAddr g.precomputation, 16 * Spec.Rsa.modulusWords g.length⟩, g.workspaceRegion, ⟨byteAddr g.stack, 24⟩]

theorem pcArgs_values {g : PrivGeometry} {bs : Fin 8 → List Byte} {s : State}
    (h : PrivContext g bs s) (a : Arguments g (pcArgument g) 6 s) {j : Nat} (hj : j < 6) :
    arg (s.callEntry.withRegions (pcRd g) (pcWr g)) j = pcArgument g j := by
  rw [arg_withRegions, arg_callEntry (by rw [h.sp]; have := h.valid.stackLow; omega_using [this])
    (by rw [h.sp]; have := h.valid.stackHigh; omega_using [hj, this])]
  change s.mem.readW (addr (s.gpr .esp) (4 * j)) 32 = _
  rw [h.address (by omega_using [hj])]
  exact a j hj

theorem pcCall_pre {g : PrivGeometry} {bs : Fin 8 → List Byte} {s : State}
    (h : PrivContext g bs s) (a : Arguments g (pcArgument g) 6 s) :
    (Spec.Rsa.publicPrecomputeContract abi 96).pre (s.callEntry.withRegions (pcRd g) (pcWr g)) := by
  have sa := fun {j} (hj : j < 6) => pcArgs_values h a hj
  have kfit : g.length < 2 ^ 32 := by have := h.valid.maxLength; omega_using [this]
  have wfit : g.scratchLength < 2 ^ 32 := by have := h.valid.workspaceFit; omega_using [this]
  have pfit : 2 * Spec.Rsa.modulusWords g.length < 2 ^ 32 := by
    have := h.valid.maxLength; simp only [Spec.Rsa.modulusWords]; omega_using [kfit]
  sig_pre [Spec.Rsa.publicPrecomputeContract, Spec.Rsa.publicPrecomputeSig, abi, argSlots, argVal, argBytes, stackBelow]
  simp only [sa (by decide : 0 < 6), sa (by decide : 1 < 6), sa (by decide : 2 < 6),
    sa (by decide : 3 < 6), sa (by decide : 4 < 6), sa (by decide : 5 < 6), pcArgument,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt kfit, Nat.mod_eq_of_lt wfit, Nat.mod_eq_of_lt pfit,
    argAddr_withRegions, argAddr_callEntry, h.sp, Nat.mul_zero, BitVec.add_zero]
  rw [show 2 * Spec.Rsa.modulusWords g.length * 8 = 16 * Spec.Rsa.modulusWords g.length by omega_using [],
    show g.scratchLength * 8 = 8 * g.scratchLength from Nat.mul_comm _ _]
  have preSub : (⟨byteAddr g.precomputation, 16 * Spec.Rsa.modulusWords g.length⟩ : Region).Sub g.innerRegion := by
    rw [PrivGeometry.precomputation, h.valid.offsetAddr (by decide)]
    exact Offset.sub_base _ (by have := h.valid.maxLength; simp only [precomputeOffset, VG.Impl.Rsa.X86.PrivChecked.frameBytes, Spec.Rsa.modulusWords]; omega_using [this])
  have preStack : (⟨byteAddr g.precomputation, 16 * Spec.Rsa.modulusWords g.length⟩ : Region).Sub g.wholeStack :=
    fun x hx => h.valid.innerSub x (preSub x hx)
  have argSub : (⟨byteAddr g.stack, 24⟩ : Region).Sub g.innerRegion := Region.sub_prefix (by decide)
  have preArgs : (⟨byteAddr g.precomputation, 16 * Spec.Rsa.modulusWords g.length⟩ : Region).Disjoint ⟨byteAddr g.stack, 24⟩ := by
    rw [PrivGeometry.precomputation, h.valid.offsetAddr (by decide)]
    exact Offset.disjoint_base _ (by decide : 24 ≤ precomputeOffset)
      (by have := h.valid.maxLength; simp only [precomputeOffset, Spec.Rsa.modulusWords]; omega_using [kfit])
  have low : (g.stack - 4).toNat = g.stack.toNat - 4 := sub_toNat (k := 4) (by have := h.valid.stackLow; omega_using [this])
  have retSub : (⟨(g.stack - 4).setWidth 64, 4⟩ : Region).Sub g.calleeRegion :=
    VG.X86.below_sub (by decide : 4 ≤ 100) h.valid.stackLow
  have belowSub : (⟨(g.stack - 4).setWidth 64 - 96#64, 96⟩ : Region).Sub g.calleeRegion := by
    rw [← VG.X86.Taint.sub_setWidth (by rw [low]; have := h.valid.stackLow; omega_using [this] : 96 ≤ (g.stack - 4).toNat)]
    exact VG.X86.below_inner (by decide : 96 + 4 ≤ 100) h.valid.stackLow
  have calleeSource := (h.valid.stackSources 0).sub_left h.valid.calleeSub
  have calleeWorkspace := h.valid.stackWorkspace.sub_left h.valid.calleeSub
  have calleePre := h.valid.calleeInner.sub_right preSub
  have calleeArgs := h.valid.calleeInner.sub_right argSub
  rw [low]
  exact ⟨by have := h.valid.stackLow; omega_using [this], by have := h.valid.stackHigh; omega_using [this], rfl, rfl,
    (h.valid.stackSources 0).sub_left preStack, h.valid.stackWorkspace.sub_left preStack, preArgs,
    h.valid.sourcesWorkspace 0,
    ((h.valid.stackSources 0).sub_left (fun x hx => h.valid.innerSub x (argSub x hx))).symm,
    (h.valid.stackWorkspace.sub_left (fun x hx => h.valid.innerSub x (argSub x hx))).symm,
    calleePre.sub_left retSub, calleeSource.sub_left retSub, calleeWorkspace.sub_left retSub, calleeArgs.sub_left retSub,
    calleePre.sub_left belowSub, calleeSource.sub_left belowSub, calleeWorkspace.sub_left belowSub, calleeArgs.sub_left belowSub,
    h.valid.precomputationFit, h.valid.sourceFits 0, h.valid.workspaceFit,
    ⟨h.valid.minLength, h.valid.maxLength⟩, rfl, publicScratch_le ⟨h.valid.minLength, h.valid.maxLength⟩ h.valid.space⟩

end VG.Proof.Rsa.X86.PrivChecked
