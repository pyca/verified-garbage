module

public import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Rsa.Scratch
import VerifiedGarbage.Proof.Rsa.Arm.PrivRegions
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Rsa.Arm.PrivPcPrefix
import VerifiedGarbage.Proof.Rsa.Arm.PrivPreWords
import VerifiedGarbage.Proof.Bignum.Arm.Stack

/-! ### `Rsa.Arm.PrivPcArgs`, which this module and modules that import it used -/

section

/-! # Register and stack arguments for the public precomputation call -/

@[expose] public section
namespace VG.Proof.Rsa.Arm
open VG VG.Arm VG.Impl.Rsa.Arm.PrivChecked VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem pcSuffix_ok (s : State) {g : PrivGeometry} {bs : Fin 8 → List Byte}
    (h : PrivContext g bs s) (slots : PrivSlots g s.mem) :
    WP isa (.block pcSuffix) s fun t =>
      t.gpr .r2 = g.sources 0 ∧ t.gpr .r3 = BitVec.ofNat 32 g.length ∧
      t.mem = s.mem ∧ Rest [.r2, .r3] s t := by
  unfold pcSuffix
  refine wp_loadStack (a := off (State.addr g.stack) oN) (by decide)
    (by rw [h.sp]; exact addr_add (by have := h.valid.stackHigh; simp only [oN, frameBytes] at *; omega_using [this]))
    (h.inner.read (by decide)) fun u a => ?_
  refine wp_loadStack (a := off (State.addr g.stack) oK) (by decide)
    (by rw [a.sp, h.sp]; exact addr_add (by have := h.valid.stackHigh; simp only [oK, frameBytes] at *; omega_using [this]))
    (by rw [a.rd, a.wr]; exact h.inner.read (by decide)) fun t b => WP.block_nil ?_
  exact ⟨by rw [b.other .r2 (by decide), a.gpr]; exact slots 1 (by decide),
    by rw [b.gpr, a.mem]; exact slots 2 (by decide), b.mem.trans a.mem,
    (a.rest (by simp)).trans (b.rest (by simp))⟩

structure PcArgs (g : PrivGeometry) (s : State) : Prop where
  output : s.gpr .r0 = g.precomputation
  outputLength : s.gpr .r1 = BitVec.ofNat 32 (2 * Spec.Rsa.modulusWords g.length)
  modulus : s.gpr .r2 = g.sources 0
  length : s.gpr .r3 = BitVec.ofNat 32 g.length
  workspace : s.mem.readW (off (State.addr g.stack) 0) 32 = g.workspace
  workspaceLength : s.mem.readW (off (State.addr g.stack) 4) 32 = BitVec.ofNat 32 g.scratchLength

theorem pcArgs_ok (s : State) {g : PrivGeometry} {bs : Fin 8 → List Byte}
    (h : PrivContext g bs s) (slots : PrivSlots g s.mem) :
    WP isa (.block pcArgs) s fun t => PrivContext g bs t ∧ PrivSlots g t.mem ∧ PcArgs g t ∧
      t.mem.readW (off (State.addr g.stack) oR1) 32 = s.gpr .r0 ∧
      Frame (pcPrefixWrites g) s.mem t.mem ∧ Rest [.r0, .r1, .r2, .r3, .r12] s t := by
  unfold pcArgs
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (pcPrefix_ok s h slots) ?_
  rintro u ⟨hu, slotsU, ptrU, memU, frameU, restU⟩
  refine WP.mono (preWords_ok .r1 u hu slotsU) ?_
  rintro v ⟨countV, memV, restV⟩
  have frameUV : Frame (bodyWrites g) u.mem v.mem := by rw [memV]; exact Frame.refl _ _
  have hv := hu.after frameUV restV
  have slotsV : PrivSlots g v.mem := by rw [memV]; exact slotsU
  refine WP.mono (pcSuffix_ok v hv slotsV) ?_
  rintro t ⟨modulusT, countT, memT, restT⟩
  have frameVT : Frame (bodyWrites g) v.mem t.mem := by rw [memT]; exact Frame.refl _ _
  refine ⟨hv.after frameVT restT, by rw [memT]; exact slotsV,
    ⟨(restT.gpr .r0 (by simp)).trans ((restV.gpr .r0 (by simp)).trans ptrU),
      (restT.gpr .r1 (by simp)).trans countV, modulusT, countT, ?_, ?_⟩, ?_, ?_,
    (restU.mono (by simp)).trans ((restV.mono (by simp)).trans (restT.mono (by simp)))⟩
  · rw [memT, memV, memU]; exact pcPrefixMem_scratch g s
  · rw [memT, memV, memU]; exact pcPrefixMem_length g s
  · rw [memT, memV, memU]; exact pcPrefixMem_status g s
  · rw [memT, memV]; exact frameU
end VG.Proof.Rsa.Arm

end

end

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
  · rw [addr_add (by have := h.valid.stackHigh; simp only [frameBytes] at this; omega_using [this])]
    exact a.workspaceLength

theorem pcCall_pre {g : PrivGeometry} {bs : Fin 8 → List Byte} {s : State}
    (h : PrivContext g bs s) (a : PcArgs g s) :
    (Spec.Rsa.publicPrecomputeContract abi 56).pre (s.callEntry.withRegions (pcRd g) (pcWr g)) := by
  have sa := pcArgs_stack h a
  have kfit : g.length < 2 ^ 32 := by have := h.valid.maxLength; omega_using [this]
  have wfit : g.scratchLength < 2 ^ 32 := by have := h.valid.workspaceFit; omega_using [this]
  have pfit : 2 * Spec.Rsa.modulusWords g.length < 2 ^ 32 := by
    have := h.valid.maxLength; simp only [Spec.Rsa.modulusWords]; omega_using [kfit]
  sig_pre [Spec.Rsa.publicPrecomputeContract, Spec.Rsa.publicPrecomputeSig, abi, argRegs, reduceClassify, Loc.val, State.addr]
  simp only [h.sp, a.output, a.outputLength, a.modulus, a.length, sa.1, sa.2,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt kfit, Nat.mod_eq_of_lt wfit, Nat.mod_eq_of_lt pfit]
  have argAddr : stackArgAddr (s.callEntry.withRegions (pcRd g) (pcWr g)) 0 = State.addr g.stack := by
    simp [stackArgAddr, h.sp]
  rw [argAddr, show 2 * Spec.Rsa.modulusWords g.length * 8 = 16 * Spec.Rsa.modulusWords g.length by omega_using [],
    show g.scratchLength * 8 = 8 * g.scratchLength from Nat.mul_comm _ _]
  have preSub : (⟨State.addr g.precomputation, 16 * Spec.Rsa.modulusWords g.length⟩ : Region).Sub g.innerRegion := by
    rw [PrivGeometry.precomputation, h.valid.offsetAddr (by decide)]
    exact Offset.sub_base _ (by have := h.valid.maxLength; simp only [oPre, frameBytes, Spec.Rsa.modulusWords]; omega_using [this])
  have preStack : (⟨State.addr g.precomputation, 16 * Spec.Rsa.modulusWords g.length⟩ : Region).Sub g.wholeStack :=
    fun x hx => h.valid.innerSub x (preSub x hx)
  have argSub : (⟨State.addr g.stack, 8⟩ : Region).Sub g.innerRegion := Region.sub_prefix (by decide)
  have callee : (⟨g.stack.setWidth 64 - BitVec.ofNat 64 56, 56⟩ : Region) = g.calleeRegion := by
    unfold PrivGeometry.calleeRegion FrameStack.belowA
    rw [FrameStack.addr_sub' h.valid.stackLow]; rfl
  refine ⟨h.valid.stackLow, by have := h.valid.stackHigh; omega_using [this], rfl, rfl,
    (h.valid.stackSources 0).sub_left preStack, h.valid.stackWorkspace.sub_left preStack, ?_,
    h.valid.sourcesWorkspace 0, ?_, ?_, ?_, ?_, ?_, h.valid.precomputationFit,
    h.valid.sourceFits 0, h.valid.workspaceFit, ⟨h.valid.minLength, h.valid.maxLength⟩, rfl, publicScratch_le ⟨h.valid.minLength, h.valid.maxLength⟩ h.valid.space⟩
  · change (⟨State.addr g.precomputation, 16 * Spec.Rsa.modulusWords g.length⟩ : Region).Disjoint _
    rw [PrivGeometry.precomputation, h.valid.offsetAddr (by decide)]
    exact Offset.disjoint_base _ (by decide : 8 ≤ oPre)
      (by have := h.valid.maxLength; simp only [oPre, Spec.Rsa.modulusWords]; omega_using [kfit])
  · exact (h.valid.stackWorkspace.sub_left (fun x hx => h.valid.innerSub x (argSub x hx))).symm
  · rw [callee]; exact h.valid.calleeInner.sub_right preSub
  · rw [callee]; exact (h.valid.stackSources 0).sub_left h.valid.calleeSub
  · rw [callee]; exact h.valid.stackWorkspace.sub_left h.valid.calleeSub
  · rw [callee]; exact h.valid.calleeInner.sub_right argSub
end VG.Proof.Rsa.Arm
