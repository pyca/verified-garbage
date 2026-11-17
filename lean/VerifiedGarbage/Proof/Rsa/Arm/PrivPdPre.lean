module

public import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Rsa.Scratch
import VerifiedGarbage.Proof.Rsa.Arm.PrivRegions
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Rsa.Contract
public import VerifiedGarbage.Proof.Rsa.Arm.PrivContext
public import VerifiedGarbage.Proof.Rsa.Arm.PrivSlots
import VerifiedGarbage.Proof.Rsa.Arm.PrivSaveResult
import VerifiedGarbage.Proof.Rsa.Arm.PrivCopyRetained
import VerifiedGarbage.Proof.Rsa.Arm.PrivCopyIncoming
import VerifiedGarbage.Proof.Rsa.Arm.PrivStoreTemporary
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Rsa.Arm.PrivPdSuffix

/-! ### `Rsa.Arm.PrivPdArgs`, which this module and modules that import it used -/

section

/-! ### `Rsa.Arm.PrivPdPrefixMemory`, which only this module used -/

section

/-! ### `Rsa.Arm.PrivPdPrefix`, which only this module used -/

section

/-! # Prepare all six stack arguments for the public re-exponentiation check -/

@[expose] public section
namespace VG.Proof.Rsa.Arm
open VG VG.Arm VG.Impl.Rsa.Arm.PrivChecked VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

def pdPrefixMem (g : PrivGeometry) (s : State) : Mem :=
  ((((((s.mem.writeW (off (State.addr g.stack) oR3) (s.gpr .r0)).writeW
    (off (State.addr g.stack) 0) (g.sources 1)).writeW
    (off (State.addr g.stack) 4) (BitVec.ofNat 32 g.exponentLength)).writeW
    (off (State.addr g.stack) 8) g.temporary).writeW
    (off (State.addr g.stack) 12) (BitVec.ofNat 32 g.length)).writeW
    (off (State.addr g.stack) 16) g.workspace).writeW
    (off (State.addr g.stack) 20) (BitVec.ofNat 32 g.scratchLength)

def pdPrefixWrites (g : PrivGeometry) : List Region :=
  [⟨State.addr g.stack, 24⟩, ⟨off (State.addr g.stack) oR3, 4⟩]

theorem pdPrefix_ok (s : State) {g : PrivGeometry} {bs : Fin 8 → List Byte}
    (h : PrivContext g bs s) (slots : PrivSlots g s.mem) :
    WP isa (.block pdPrefix) s fun t => PrivContext g bs t ∧ PrivSlots g t.mem ∧
      t.mem = pdPrefixMem g s ∧ Frame (pdPrefixWrites g) s.mem t.mem ∧ Rest [.r0, .r12] s t := by
  unfold pdPrefix
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff,
    WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (saveResult_ok s h slots (by decide : 88 ≤ oR3) (by decide : oR3 + 4 ≤ 96)) ?_
  rintro s0 ⟨h0, slots0, ptr0, mem0, frame0, rest0⟩
  refine WP.mono (copyRetained_ok s0 h0 slots0 (by decide : 3 < 6) (by decide : 0 + 4 ≤ 56) ptr0) ?_
  rintro s1 ⟨h1, slots1, mem1, frame1, rest1⟩
  have ptr1 : s1.gpr .r12 = g.stack := (rest1.gpr .r12 (by simp)).trans ptr0
  refine WP.mono (copyRetained_ok s1 h1 slots1 (by decide : 4 < 6) (by decide : 4 + 4 ≤ 56) ptr1) ?_
  rintro s2 ⟨h2, slots2, mem2, frame2, rest2⟩
  have ptr2 : s2.gpr .r12 = g.stack := (rest2.gpr .r12 (by simp)).trans ptr1
  refine WP.mono (storeTemporary_ok s2 h2 slots2 ptr2) ?_
  rintro s3 ⟨h3, slots3, mem3, frame3, rest3⟩
  have ptr3 : s3.gpr .r12 = g.stack := (rest3.gpr .r12 (by simp)).trans ptr2
  refine WP.mono (copyRetained_ok s3 h3 slots3 (by decide : 2 < 6) (by decide : 12 + 4 ≤ 56) ptr3) ?_
  rintro s4 ⟨h4, slots4, mem4, frame4, rest4⟩
  have ptr4 : s4.gpr .r12 = g.stack := (rest4.gpr .r12 (by simp)).trans ptr3
  refine WP.mono (copyIncoming_ok s4 h4 slots4 (by decide : 14 < 16) (by decide : 16 + 4 ≤ 56) ptr4) ?_
  rintro s5 ⟨h5, slots5, mem5, frame5, rest5⟩
  have ptr5 : s5.gpr .r12 = g.stack := (rest5.gpr .r12 (by simp)).trans ptr4
  refine WP.mono (copyIncoming_ok s5 h5 slots5 (by decide : 15 < 16) (by decide : 20 + 4 ≤ 56) ptr5) ?_
  rintro s6 ⟨h6, slots6, mem6, frame6, rest6⟩
  refine ⟨h6, slots6, ?_, ?_, ?_⟩
  · rw [mem6, mem5, mem4, mem3, mem2, mem1, mem0]; rfl
  · have f0 : Frame (pdPrefixWrites g) s.mem s0.mem := frame0.mono (by simp [pdPrefixWrites])
    have f1 : Frame (pdPrefixWrites g) s0.mem s1.mem := frame1.sub (by
      intro r hr
      simp only [List.mem_singleton] at hr
      subst r
      exact ⟨⟨State.addr g.stack, 24⟩, by simp [pdPrefixWrites], Offset.sub_base _ (by decide : 0 + 4 ≤ 24)⟩)
    have f2 : Frame (pdPrefixWrites g) s1.mem s2.mem := frame2.sub (by
      intro r hr
      simp only [List.mem_singleton] at hr
      subst r
      exact ⟨⟨State.addr g.stack, 24⟩, by simp [pdPrefixWrites], Offset.sub_base _ (by decide : 4 + 4 ≤ 24)⟩)
    have f3 : Frame (pdPrefixWrites g) s2.mem s3.mem := frame3.sub (by
      intro r hr
      simp only [List.mem_singleton] at hr
      subst r
      exact ⟨⟨State.addr g.stack, 24⟩, by simp [pdPrefixWrites], Offset.sub_base _ (by decide : 8 + 4 ≤ 24)⟩)
    have f4 : Frame (pdPrefixWrites g) s3.mem s4.mem := frame4.sub (by
      intro r hr
      simp only [List.mem_singleton] at hr
      subst r
      exact ⟨⟨State.addr g.stack, 24⟩, by simp [pdPrefixWrites], Offset.sub_base _ (by decide : 12 + 4 ≤ 24)⟩)
    have f5 : Frame (pdPrefixWrites g) s4.mem s5.mem := frame5.sub (by
      intro r hr
      simp only [List.mem_singleton] at hr
      subst r
      exact ⟨⟨State.addr g.stack, 24⟩, by simp [pdPrefixWrites], Offset.sub_base _ (by decide : 16 + 4 ≤ 24)⟩)
    have f6 : Frame (pdPrefixWrites g) s5.mem s6.mem := frame6.sub (by
      intro r hr
      simp only [List.mem_singleton] at hr
      subst r
      exact ⟨⟨State.addr g.stack, 24⟩, by simp [pdPrefixWrites], Offset.sub_base _ (by decide : 20 + 4 ≤ 24)⟩)
    exact f0.trans (f1.trans (f2.trans (f3.trans (f4.trans (f5.trans f6)))))
  · exact (rest0.mono (by simp)).trans ((rest1.mono (by simp)).trans ((rest2.mono (by simp)).trans ((rest3.mono (by simp)).trans ((rest4.mono (by simp)).trans ((rest5.mono (by simp)).trans ((rest6.mono (by simp))))))))
end VG.Proof.Rsa.Arm

end

end


/-! # Exact public-operation stack arguments and retained status -/

@[expose] public section
namespace VG.Proof.Rsa.Arm
open VG VG.Arm VG.Impl.Rsa.Arm.PrivChecked VG.Proof.Bignum.Arm VG.Proof.Mont

def pdArgument (g : PrivGeometry) (j : Nat) : BitVec 32 :=
  match j with
  | 0 => g.sources 1 | 1 => BitVec.ofNat 32 g.exponentLength
  | 2 => g.temporary | 3 => BitVec.ofNat 32 g.length
  | 4 => g.workspace | _ => BitVec.ofNat 32 g.scratchLength

theorem pdPrefixMem_arguments (g : PrivGeometry) (s : State) (j : Nat) (hj : j < 6) :
    (pdPrefixMem g s).readW (off (State.addr g.stack) (4 * j)) 32 = pdArgument g j := by
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 by omega_using [hj]) with
    rfl | rfl | rfl | rfl | rfl | rfl
  · unfold pdPrefixMem pdArgument
    rw [outside_read32 (writeW32_outside _ _ (d := 20) _ (by decide)) (d := 0) (by decide) (by decide),
      outside_read32 (writeW32_outside _ _ (d := 16) _ (by decide)) (d := 0) (by decide) (by decide),
      outside_read32 (writeW32_outside _ _ (d := 12) _ (by decide)) (d := 0) (by decide) (by decide),
      outside_read32 (writeW32_outside _ _ (d := 8) _ (by decide)) (d := 0) (by decide) (by decide),
      outside_read32 (writeW32_outside _ _ (d := 4) _ (by decide)) (d := 0) (by decide) (by decide),
      Mem.readW_writeW_self32]
    rfl
  · unfold pdPrefixMem pdArgument
    rw [outside_read32 (writeW32_outside _ _ (d := 20) _ (by decide)) (d := 4) (by decide) (by decide),
      outside_read32 (writeW32_outside _ _ (d := 16) _ (by decide)) (d := 4) (by decide) (by decide),
      outside_read32 (writeW32_outside _ _ (d := 12) _ (by decide)) (d := 4) (by decide) (by decide),
      outside_read32 (writeW32_outside _ _ (d := 8) _ (by decide)) (d := 4) (by decide) (by decide),
      Mem.readW_writeW_self32]
    rfl
  · unfold pdPrefixMem pdArgument
    rw [outside_read32 (writeW32_outside _ _ (d := 20) _ (by decide)) (d := 8) (by decide) (by decide),
      outside_read32 (writeW32_outside _ _ (d := 16) _ (by decide)) (d := 8) (by decide) (by decide),
      outside_read32 (writeW32_outside _ _ (d := 12) _ (by decide)) (d := 8) (by decide) (by decide),
      Mem.readW_writeW_self32]
    rfl
  · unfold pdPrefixMem pdArgument
    rw [outside_read32 (writeW32_outside _ _ (d := 20) _ (by decide)) (d := 12) (by decide) (by decide),
      outside_read32 (writeW32_outside _ _ (d := 16) _ (by decide)) (d := 12) (by decide) (by decide),
      Mem.readW_writeW_self32]
    rfl
  · unfold pdPrefixMem pdArgument
    rw [outside_read32 (writeW32_outside _ _ (d := 20) _ (by decide)) (d := 16) (by decide) (by decide),
      Mem.readW_writeW_self32]
    rfl
  · unfold pdPrefixMem pdArgument
    rw [Mem.readW_writeW_self32]
    rfl

theorem pdPrefixMem_status (g : PrivGeometry) (s : State) :
    (pdPrefixMem g s).readW (off (State.addr g.stack) oR3) 32 = s.gpr .r0 := by
  unfold pdPrefixMem
  rw [outside_read32 (writeW32_outside _ _ (d := 20) _ (by decide)) (d := oR3) (by decide) (by decide),
    outside_read32 (writeW32_outside _ _ (d := 16) _ (by decide)) (d := oR3) (by decide) (by decide),
    outside_read32 (writeW32_outside _ _ (d := 12) _ (by decide)) (d := oR3) (by decide) (by decide),
    outside_read32 (writeW32_outside _ _ (d := 8) _ (by decide)) (d := oR3) (by decide) (by decide),
    outside_read32 (writeW32_outside _ _ (d := 4) _ (by decide)) (d := oR3) (by decide) (by decide),
    outside_read32 (writeW32_outside _ _ (d := 0) _ (by decide)) (d := oR3) (by decide) (by decide),
    Mem.readW_writeW_self32]
end VG.Proof.Rsa.Arm

end

end


/-! # All arguments and the saved precomputation status before re-exponentiation -/

@[expose] public section
namespace VG.Proof.Rsa.Arm
open VG VG.Arm VG.Impl.Rsa.Arm.PrivChecked VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

structure PdArgs (g : PrivGeometry) (s : State) : Prop where
  output : s.gpr .r0 = g.output
  outputLength : s.gpr .r1 = BitVec.ofNat 32 g.length
  precomputation : s.gpr .r2 = g.precomputation
  precomputationLength : s.gpr .r3 = BitVec.ofNat 32 (2 * Spec.Rsa.modulusWords g.length)
  arguments : ∀ j < 6, s.mem.readW (off (State.addr g.stack) (4 * j)) 32 = pdArgument g j

theorem pdArgs_ok (s : State) {g : PrivGeometry} {bs : Fin 8 → List Byte}
    (h : PrivContext g bs s) (slots : PrivSlots g s.mem) :
    WP isa (.block pdArgs) s fun t => PrivContext g bs t ∧ PrivSlots g t.mem ∧ PdArgs g t ∧
      t.mem.readW (off (State.addr g.stack) oR3) 32 = s.gpr .r0 ∧
      Frame (pdPrefixWrites g) s.mem t.mem ∧ Rest [.r0, .r1, .r2, .r3, .r12] s t := by
  unfold pdArgs
  rw [WP.block_append_iff]
  refine WP.mono (pdPrefix_ok s h slots) ?_
  rintro u ⟨hu, slotsU, memU, frameU, restU⟩
  refine WP.mono (pdSuffix_ok u hu slotsU) ?_
  rintro t ⟨outT, lenT, preT, preLenT, memT, restT⟩
  have unchanged : Frame (bodyWrites g) u.mem t.mem := by rw [memT]; exact Frame.refl _ _
  refine ⟨hu.after unchanged restT, by rw [memT]; exact slotsU,
    ⟨outT, lenT, preT, preLenT, ?_⟩, ?_, ?_,
    (restU.mono (by simp)).trans (restT.mono (by simp))⟩
  · intro j hj
    rw [memT, memU]; exact pdPrefixMem_arguments g s j hj
  · rw [memT, memU]; exact pdPrefixMem_status g s
  · rw [memT]; exact frameU
end VG.Proof.Rsa.Arm

end

end

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
  rw [addr_add (by have := h.valid.stackHigh; simp only [frameBytes] at this; omega_using [hj, this])]
  exact a.arguments j hj

theorem pdCall_pre {g : PrivGeometry} {bs : Fin 8 → List Byte} {s : State}
    (h : PrivContext g bs s) (a : PdArgs g s) :
    (Proof.Rsa.publicPrecomputedCheckedContract abi 56).pre (s.callEntry.withRegions (pdRd g) (pdWr g)) := by
  have sa := fun {j} (hj : j < 6) => pdArgs_stack h a hj
  have kfit : g.length < 2 ^ 32 := by have := h.valid.maxLength; omega_using [this]
  have efit : g.exponentLength < 2 ^ 32 := by have := h.valid.exponentFits; omega_using [kfit, this]
  have wfit : g.scratchLength < 2 ^ 32 := by have := h.valid.workspaceFit; omega_using [this]
  have pfit : 2 * Spec.Rsa.modulusWords g.length < 2 ^ 32 := by
    have := h.valid.maxLength; simp only [Spec.Rsa.modulusWords]; omega_using [kfit]
  sig_pre [Proof.Rsa.publicPrecomputedCheckedContract, Proof.Rsa.publicPrecomputedSig, abi, argRegs, reduceClassify, Loc.val, State.addr]
  simp only [h.sp, a.output, a.outputLength, a.precomputation, a.precomputationLength,
    sa (by decide : 0 < 6), sa (by decide : 1 < 6), sa (by decide : 2 < 6),
    sa (by decide : 3 < 6), sa (by decide : 4 < 6), sa (by decide : 5 < 6), pdArgument,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt kfit, Nat.mod_eq_of_lt efit,
    Nat.mod_eq_of_lt wfit, Nat.mod_eq_of_lt pfit]
  have argAddr : stackArgAddr (s.callEntry.withRegions (pdRd g) (pdWr g)) 0 = State.addr g.stack := by
    simp [stackArgAddr, h.sp]
  rw [argAddr, show 2 * Spec.Rsa.modulusWords g.length * 8 = 16 * Spec.Rsa.modulusWords g.length by omega_using [],
    show g.scratchLength * 8 = 8 * g.scratchLength from Nat.mul_comm _ _]
  have preSub : (⟨State.addr g.precomputation, 16 * Spec.Rsa.modulusWords g.length⟩ : Region).Sub g.innerRegion := by
    rw [PrivGeometry.precomputation, h.valid.offsetAddr (by decide)]
    exact Offset.sub_base _ (by have := h.valid.maxLength; simp only [oPre, frameBytes, Spec.Rsa.modulusWords]; omega_using [this])
  have tempSub : (⟨State.addr g.temporary, g.length⟩ : Region).Sub g.innerRegion := by
    rw [PrivGeometry.temporary, h.valid.offsetAddr (by decide)]
    exact Offset.sub_base _ (by have := h.valid.maxLength; simp only [oM, frameBytes]; omega_using [this])
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
  refine ⟨h.valid.stackLow, by have := h.valid.stackHigh; omega_using [this], rfl, rfl,
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
