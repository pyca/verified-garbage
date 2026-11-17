module

public import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Rsa.Arm.PrivRegions
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Rsa.Contract
public import VerifiedGarbage.Proof.Rsa.Arm.PrivContext
public import VerifiedGarbage.Proof.Rsa.Arm.PrivSlots
import VerifiedGarbage.Proof.Rsa.Arm.PrivSaveIncoming
import VerifiedGarbage.Proof.Rsa.Arm.PrivCopyArgs
import VerifiedGarbage.Proof.Rsa.Arm.PrivSaveRegs
import VerifiedGarbage.Proof.Bignum.Arm.PcEntry
import VerifiedGarbage.Proof.Framework.Block

/-! ### `Rsa.Arm.PrivCrtArgs`, which this module and modules that import it used -/

section

/-! # Prepare all register and stack arguments of the private CRT call -/

@[expose] public section
namespace VG.Proof.Rsa.Arm
open VG VG.Arm VG.Impl.Rsa.Arm.PrivChecked VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_mov op2_reg)

theorem saveSlots_ok (s : State) {g : PrivGeometry} {bs : Fin 8 → List Byte} (h : PrivContext g bs s)
    (output : s.gpr .r0 = g.output) (modulus : s.gpr .r2 = g.sources 0) (count : s.gpr .r3 = BitVec.ofNat 32 g.length) :
    WP isa (.block saveSlots) s fun t => PrivContext g bs t ∧ PrivSlots g t.mem ∧
      t.gpr .r12 = g.stack ∧ Frame [g.innerRegion] s.mem t.mem ∧ Rest [.r0, .r12] s t := by
  unfold saveSlots
  rw [WP.block_append_iff]
  refine WP.mono (saveRegs_ok s h output modulus count) ?_
  rintro u ⟨hu, slots, ptr, frameU, restU⟩
  refine WP.mono (saveIncoming_prefix_ok 3 (by decide) u hu slots ptr) ?_
  rintro t ⟨ht, slotsT, frameT, restT⟩
  exact ⟨ht, slotsT, (restT.gpr .r12 (by simp)).trans ptr, frameU.trans frameT,
    (restU.mono (by simp)).trans (restT.mono (by simp))⟩

structure CrtArgs (g : PrivGeometry) (s : State) : Prop where
  output : s.gpr .r0 = g.temporary
  outputLength : s.gpr .r1 = BitVec.ofNat 32 g.length
  modulus : s.gpr .r2 = g.sources 0
  length : s.gpr .r3 = BitVec.ofNat 32 g.length
  arguments : ∀ j < 14, s.mem.readW (off (State.addr g.stack) (4 * j)) 32 = g.argument (j + 2)

theorem crtRegs_ok (s : State) {g : PrivGeometry} {bs : Fin 8 → List Byte} (h : PrivContext g bs s)
    (modulus : s.gpr .r2 = g.sources 0) (count : s.gpr .r3 = BitVec.ofNat 32 g.length)
    (args : ∀ j < 14, s.mem.readW (off (State.addr g.stack) (4 * j)) 32 = g.argument (j + 2)) :
    WP isa (.block crtRegs) s fun t => CrtArgs g t ∧ t.mem = s.mem ∧ Rest [.r0, .r1] s t := by
  unfold crtRegs
  refine wp_stackAddr (by decide) fun u a => ?_
  refine wp_mov (op2_reg _ _) fun t b => WP.block_nil ?_
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, b.mem.trans a.mem, (a.rest (by simp)).trans (b.rest (by simp))⟩
  · rw [b.other .r0 (by decide), a.gpr, h.sp]; rfl
  · rw [b.gpr, a.other .r3 (by decide), count]
  · rw [b.other .r2 (by decide), a.other .r2 (by decide), modulus]
  · rw [b.other .r3 (by decide), a.other .r3 (by decide), count]
  · simpa only [b.mem, a.mem] using args

theorem crtArgs_ok (s : State) {g : PrivGeometry} {bs : Fin 8 → List Byte} (h : PrivContext g bs s)
    (output : s.gpr .r0 = g.output) (modulus : s.gpr .r2 = g.sources 0) (count : s.gpr .r3 = BitVec.ofNat 32 g.length) :
    WP isa (.block crtArgs) s fun t => PrivContext g bs t ∧ PrivSlots g t.mem ∧ CrtArgs g t ∧
      Frame [g.innerRegion] s.mem t.mem ∧ Rest [.r0, .r1, .r12] s t := by
  unfold crtArgs
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (saveSlots_ok s h output modulus count) ?_
  rintro u ⟨hu, slotsU, ptr, frameU, restU⟩
  refine WP.mono (copyArgs_ok u hu slotsU ptr) ?_
  rintro v ⟨hv, slotsV, args, frameV, restV⟩
  have restUV : Rest [.r0, .r12] s v := restU.trans (restV.mono (by simp))
  refine WP.mono (crtRegs_ok v hv ((restUV.gpr .r2 (by simp)).trans modulus)
    ((restUV.gpr .r3 (by simp)).trans count) args) ?_
  rintro t ⟨argsT, mem, restT⟩
  have frameVT : Frame (bodyWrites g) v.mem t.mem := by rw [mem]; exact Frame.refl _ _
  refine ⟨hv.after frameVT restT, by simpa only [mem] using slotsV, argsT, ?_,
    (restUV.mono (by simp)).trans (restT.mono (by simp))⟩
  rw [mem]
  exact frameU.trans (frameV.sub (by
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact ⟨g.innerRegion, by simp, Region.sub_prefix (by decide : 56 ≤ frameBytes)⟩))
end VG.Proof.Rsa.Arm

end

end

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
  rw [addr_add (by have := h.valid.stackHigh; simp only [frameBytes] at this; omega_using [hj, this])]
  exact a.arguments j hj

theorem crtCall_pre {g : PrivGeometry} {bs : Fin 8 → List Byte} {s : State}
    (h : PrivContext g bs s) (a : CrtArgs g s) :
    (Proof.Rsa.privateCrtContract abi 56).pre (s.callEntry.withRegions (crtRd g) (crtWr g)) := by
  have sa := fun {j} (hj : j < 14) => crtArgs_stack h a hj
  have kfit : g.length < 2 ^ 32 := by have := h.valid.maxLength; omega_using [this]
  have pfit : g.pLength < 2 ^ 32 := by have := h.valid.pFits; omega_using [kfit, this]
  have qfit : g.qLength < 2 ^ 32 := by have := h.valid.qFits; omega_using [kfit, this]
  have wfit : g.scratchLength < 2 ^ 32 := by have := h.valid.workspaceFit; omega_using [this]
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
    exact Offset.sub_base _ (by have := h.valid.maxLength; simp only [oM, frameBytes]; omega_using [this])
  have outgoingSub : (⟨State.addr g.stack, 56⟩ : Region).Sub g.innerRegion :=
    Region.sub_prefix (by decide : 56 ≤ frameBytes)
  have tempSources := fun i => (h.valid.stackSources i).sub_left (fun x hx => h.valid.innerSub x (temporarySub x hx))
  have tempWorkspace := h.valid.stackWorkspace.sub_left (fun x hx => h.valid.innerSub x (temporarySub x hx))
  have tempArgs : (⟨State.addr g.temporary, g.length⟩ : Region).Disjoint ⟨State.addr g.stack, 56⟩ := by
    rw [PrivGeometry.temporary, h.valid.offsetAddr (by decide)]
    exact Offset.disjoint_base _ (by decide : 56 ≤ oM) (by have := h.valid.maxLength; simp only [oM]; omega_using [kfit])
  have callee : (⟨State.addr g.stack - BitVec.ofNat 64 56, 56⟩ : Region) = g.calleeRegion := by
    unfold PrivGeometry.calleeRegion FrameStack.belowA
    rw [FrameStack.addr_sub' h.valid.stackLow]
  simp only [State.addr] at callee
  have calleeSources := fun i => (h.valid.stackSources i).sub_left h.valid.calleeSub
  have calleeWorkspace := h.valid.stackWorkspace.sub_left h.valid.calleeSub
  have argsWorkspace := (h.valid.stackWorkspace.sub_left (fun x hx => h.valid.innerSub x (outgoingSub x hx))).symm
  refine ⟨h.valid.stackLow, by have := h.valid.stackHigh; omega_using [this], rfl, ?_,
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
