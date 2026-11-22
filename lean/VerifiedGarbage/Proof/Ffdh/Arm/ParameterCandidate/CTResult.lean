module

import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.Status
import VerifiedGarbage.Proof.Bignum.Arm.StackOnlyCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateParams
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidatePhaseMath
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTExponentLoop
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidatePhaseFrame
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTBase
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.WitnessState
public import VerifiedGarbage.Proof.MillerRabin.Arm.Backend
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.PhaseInput
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.WitnessStep
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.Draw
import VerifiedGarbage.Proof.Ffdh.Arm.RangeCT
import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTStackBlocks
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.WitnessEnd
public import VerifiedGarbage.Proof.Ffdh.Arm.Prepare
import VerifiedGarbage.Proof.Bignum.Arm.Stack
import VerifiedGarbage.Proof.Ffdh.Arm.Block
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.KeyFrame
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.KeyMemory
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
import VerifiedGarbage.Proof.Bignum.Arm.ImportOperand
import VerifiedGarbage.Proof.Bignum.Arm.ImportOperandCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import Mathlib.Data.Nat.Basic
import Mathlib.Order.RelClasses
public import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
public import VerifiedGarbage.Impl.Bignum.Arm.MontCall
import VerifiedGarbage.Proof.Bignum.Arm.TwoExpShared
import VerifiedGarbage.Proof.Bignum.Arm.TwoExpSharedCT
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateBuffers
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.ResultContext
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Bignum.Arm.PcDimensions
import VerifiedGarbage.Proof.Ffdh.Arm.Output
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.FinishHead
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Rsa.Octets
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Ffdh.Arm.NormalizedPrepareCT
import VerifiedGarbage.Proof.Ffdh.Arm.SharedCheckPublicInstances
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
meta import VerifiedGarbage.Impl.Ffdh.Arm.CandidatePrepare
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Impl.Ffdh.Arm.CandidatePrepare
meta import VerifiedGarbage.Proof.Ffdh.Arm.Prepare
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTPieces
meta import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.MontData
meta import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.MontData
meta import VerifiedGarbage.Spec.Rsa.Contract
meta import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTExponentLoop
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.KeyOps
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Ffdh.Arm.ZeroBuffer

/-! ### `Ffdh.Arm.ParameterCandidate.CTFinish`, which this module and modules that import it used -/

section

/-! ### `Ffdh.Arm.ParameterCandidate.ClearOutput`, which this module and modules that import it used -/

section

/-! Rejected or incomplete candidates use the existing verified FFDH byte-clear loop. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Ffdh.Arm VG.Proof.X25519.Arm

theorem clearHead_ok {s : State} {dst usedPtr : BitVec 32} {n consumed : Nat}
    (h : ResultContext dst usedPtr n consumed s) :
    WP isa (.block [.ldrSp .r0 4, .ldrSp .lr 12, .mov .r2 (.imm 0)]) s fun t =>
      (t.gpr .r0 = dst ∧ t.gpr .lr = BitVec.ofNat 32 n ∧ t.gpr .r2 = 0 ∧ t.mem = s.mem) ∧
        Rest [.r0, .r2, .lr] s t := by
  have out : s.mem.readW (State.addr (s.sp + 4#32)) 32 = dst := by
    simpa only [resultValues] using h.saved.saved 4 (by simp [resultSlots])
  have count : s.mem.readW (State.addr (s.sp + 12#32)) 32 = BitVec.ofNat 32 n := by
    simpa only [resultValues] using h.saved.saved 12 (by simp [resultSlots])
  refine withRest_all [.r0, .r2, .lr] ?_ (by rfl) (by rfl)
  ffrun [BitVec.add_zero, h.saved.read (d := 4) (by decide), h.saved.read (d := 12) (by decide), out, count]

theorem clearOutput_ok {s : State} {dst usedPtr : BitVec 32} {n consumed : Nat}
    (h : ResultContext dst usedPtr n consumed s) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.clearOutput s fun t =>
      ResultContext dst usedPtr n consumed t ∧ Spec.Rsa.bytesAt t.mem (State.addr dst) n = List.replicate n 0 ∧
      Frame [⟨State.addr dst, n⟩] s.mem t.mem ∧ Rest [.r0, .r1, .r2, .lr] s t := by
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.clearOutput VG.Impl.Ffdh.Arm.Domain.GenerateKey.zeros
  refine WP.seq (WP.mono (clearHead_ok h) ?_)
  rintro u ⟨⟨ptr, count, zero, memory⟩, rest⟩
  have ctx := h.after_memory memory rest
  refine WP.mono (zeroBuffer_ok false u h.positive h.countFits h.output.fits ctx.output.writable zero rfl ptr count) ?_
  rintro t ⟨bytes, _, _, changed, restT⟩
  have finalCtx := ctx.after_output changed restT
  rw [memory] at changed
  exact ⟨finalCtx, bytes, changed, (rest.mono (by simp)).trans (restT.mono (by simp))⟩

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end

/-! Final output clearing and u64 consumption stores use only public buffer addresses. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.X25519.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Two two_post two_taint)

structure ResultData where
  dst : BitVec 32
  usedPtr : BitVec 32
  n : Nat

def ResultStart (p : ResultData) (s : State) : Prop := ∃ consumed, ResultContext p.dst p.usedPtr p.n consumed s

theorem ResultStart.after_memory {p : ResultData} {s t : State} {rs : List Reg}
    (h : ResultStart p s) (memory : t.mem = s.mem) (rest : Rest rs s t) : ResultStart p t := by
  obtain ⟨consumed, context⟩ := h
  exact ⟨consumed, context.after_memory memory rest⟩

private def ResultPointer (p : ResultData) (s : State) : Prop := s.gpr .r2 = p.usedPtr
private def ClearPointers (p : ResultData) (s : State) : Prop := s.gpr .r0 = p.dst ∧ s.gpr .lr = BitVec.ofNat 32 p.n

theorem finish_ct (status : Nat) (bound : status ≤ 2) : RelCT isa (Two ResultStart)
    (.block (VG.Impl.Ffdh.Arm.ParameterCandidate.finish status)) (fun _ _ => True) := by
  have head : RelCT isa (Two ResultStart) (.block [.ldrSp .r2 32]) (Two ResultPointer) :=
    two_post ((loadStack_ct .r2 32).mono (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ _ => trivial)) (fun p s ⟨_, h⟩ => by
      refine wp_loadStack (a := State.addr (s.sp + 32#32)) (by decide) rfl (h.saved.read (by decide)) fun t loaded => WP.block_nil ?_
      exact loaded.gpr.trans (h.saved.saved 32 (by decide)))
  obtain ⟨hint, checked⟩ := finishTail_taint status bound
  have tail : RelCT isa (Two ResultPointer) (.block ((VG.Impl.Ffdh.Arm.ParameterCandidate.finish status).drop 1))
      (fun _ _ => True) := by
    refine two_taint [.r2] ?_ checked
    intro p s t a b r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact a.trans b.symm
  exact RelCT.block_append (head.seq tail)

theorem clearOutput_ct : RelCT isa (Two ResultStart) VG.Impl.Ffdh.Arm.ParameterCandidate.clearOutput (Two ResultStart) := by
  have head : RelCT isa (Two ResultStart) (.block [.ldrSp .r0 4, .ldrSp .lr 12, .mov .r2 (.imm 0)]) (Two ClearPointers) :=
    two_post ((stackOnly_ct _ rfl).mono (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ _ => trivial)) (fun _ s ⟨_, h⟩ =>
      WP.mono (clearHead_ok h) (fun _ ⟨⟨ptr, count, _, _⟩, _⟩ => ⟨ptr, count⟩))
  obtain ⟨hint, checked⟩ := clearOutputLoop_taint
  have loop : RelCT isa (Two ClearPointers) VG.Impl.Ffdh.Arm.Domain.GenerateKey.zeros (fun _ _ => True) := by
    refine two_taint [.r0, .lr] ?_ checked
    intro p s t a b r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact a.1.trans b.1.symm
    · exact a.2.trans b.2.symm
  exact two_post (head.seq loop) (fun _ _ ⟨consumed, h⟩ => WP.mono (clearOutput_ok h) (fun _ ⟨context, _, _, _⟩ => ⟨consumed, context⟩))

private theorem loadConsumed_ct : RelCT isa (Two ResultStart) (.block [.ldrSp .r3 40]) (Two ResultStart) :=
  two_post ((loadStack_ct .r3 40).mono (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ _ => trivial)) (fun _ s ⟨consumed, h⟩ => by
    refine wp_loadStack (a := State.addr (s.sp + 40#32)) (by decide) rfl (h.saved.read (by decide)) fun t loaded => WP.block_nil ?_
    exact ⟨consumed, h.after_memory loaded.mem (loaded.rest (by simp : Reg.r3 ∈ [Reg.r3]))⟩)

private theorem zeroConsumed_ct : RelCT isa (Two ResultStart) (.block [.mov .r3 (.imm 0)]) (Two ResultStart) :=
  two_post ((stackOnly_ct _ rfl).mono (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ _ => trivial)) (fun _ _ h => by
    refine wp_mov (op2_imm (by decide)) fun t moved => WP.block_nil ?_
    exact h.after_memory moved.mem (moved.rest (by simp : Reg.r3 ∈ [Reg.r3])))

theorem finAccepted_ct : RelCT isa (Two ResultStart) VG.Impl.Ffdh.Arm.ParameterCandidate.finAccepted (fun _ _ => True) :=
  RelCT.block_append (loadConsumed_ct.seq (finish_ct 1 (by decide)))

theorem finRejected_ct : RelCT isa (Two ResultStart) VG.Impl.Ffdh.Arm.ParameterCandidate.finRejected (fun _ _ => True) :=
  clearOutput_ct.seq (RelCT.block_append (loadConsumed_ct.seq (finish_ct 2 (by decide))))

theorem finNone_ct : RelCT isa (Two ResultStart) VG.Impl.Ffdh.Arm.ParameterCandidate.finNone (fun _ _ => True) :=
  clearOutput_ct.seq (RelCT.block_append (zeroConsumed_ct.seq (finish_ct 0 (by decide))))

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end

/-! ### `Ffdh.Arm.ParameterCandidate.CTWitnessMaskStore`, which only this module used -/

section

/-! The witness mask stores through a public workspace-array pointer. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.Ffdh.Arm
open VG.Proof.X25519.Arm (Rest)
open VG.Proof.Ffdh.Arm.KeySearch
open VG.Proof.Rsa.Mont (arrAt)

structure MaskStoreData where
  base : BitVec 32
  capacity : Nat
  words : Nat
  index : Nat

def MaskStoreStart (p : MaskStoreData) (s : State) : Prop :=
  ArithmeticReady p.base p.capacity p.words s ∧ s.gpr .r5 = BitVec.ofNat 32 p.index

private def MaskStoreHead (p : MaskStoreData) (s : State) : Prop :=
  s.gpr .r4 = p.base + BitVec.ofNat 32 (arrAt p.words 1) ∧ s.gpr .r5 = BitVec.ofNat 32 p.index

private theorem loadBase_ok (p : MaskStoreData) (s : State) (h : MaskStoreStart p s) :
    WP isa (.block [.ldrSp .r0 0]) s (MaskStoreStart p) := by
  have raw : WP isa (.block [.ldrSp .r0 0]) s fun t =>
      (t.gpr .r0 = p.base ∧ t.mem = s.mem) ∧ Rest [.r0] s t := by
    refine withRest_all [.r0] ?_ (by rfl) (by rfl)
    ffrun [BitVec.add_zero, h.1.stackRead, h.1.saved]
  exact WP.mono raw (fun _ post => ⟨h.1.of_mem post.1.2 post.2 post.1.1,
    (post.2.gpr .r5 (by simp)).trans h.2⟩)

private theorem loadArray_ok (p : MaskStoreData) (s : State) (h : MaskStoreStart p s) :
    WP isa (.block [.ldr .r4 .r0 72]) s (MaskStoreHead p) := by
  have fits : arrAt p.words 8 ≤ 8 * p.capacity := h.1.width ▸ h.1.layout.2.2.1
  have size : 128 ≤ 8 * p.capacity := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega_using [fits]
  have header := nativeHeader_of_layout s.mem p.base h.1.workspace.nowrap (Nat.le_refl _) h.1.layout
  rw [h.1.width] at header
  have addr72 : State.addr (p.base + 72#32) = off (State.addr p.base) 72 :=
    VG.Arm.addr_add (by have := h.1.workspace.nowrap; omega_using [size, this])
  have raw : WP isa (.block [.ldr .r4 .r0 72]) s fun t =>
      t.gpr .r4 = p.base + BitVec.ofNat 32 (arrAt p.words 1) ∧ Rest [.r4] s t := by
    refine withRest_all [.r4] ?_ (by rfl) (by rfl)
    ffrun [h.1.ptr, addr72, h.1.workspace.read (off := 72) (by omega_using [size]), header.array 1 (by decide)]
  exact WP.mono raw (fun _ post => ⟨post.1, (post.2.gpr .r5 (by simp)).trans h.2⟩)

theorem witnessMaskStore_ct : RelCT isa (Two MaskStoreStart)
    (.block VG.Impl.Ffdh.Arm.ParameterCandidate.witnessMaskStore) (fun _ _ => True) := by
  have base : RelCT isa (Two MaskStoreStart) (.block [.ldrSp .r0 0]) (Two MaskStoreStart) :=
    two_post ((stackOnly_ct _ rfl).mono (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ _ => trivial)) loadBase_ok
  have array : RelCT isa (Two MaskStoreStart) (.block [.ldr .r4 .r0 72]) (Two MaskStoreHead) := by
    refine two_piece [.r0] ?_ (by taint_decide) loadArray_ok
    intro _ _ _ left right r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact left.1.ptr.trans right.1.ptr.symm
  have tail : RelCT isa (Two MaskStoreHead)
      (.block (VG.Impl.Ffdh.Arm.ParameterCandidate.witnessMaskStore.drop 2)) (fun _ _ => True) := by
    refine two_taint [.r4, .r5] ?_ (by taint_decide)
    intro _ _ _ left right r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact left.1.trans right.1.symm
    · exact left.2.trans right.2.symm
  exact RelCT.block_append (base.seq (RelCT.block_append (array.seq tail)))

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end

/-! ### `Ffdh.Arm.ParameterCandidate.CTExponentTail`, which only this module used -/

section

/-! Fixed-step exponent metadata and public-address array storage. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Two)

private theorem powerStore_taint : CandidateCert keyRegs
    (.block VG.Impl.Ffdh.Arm.ParameterCandidate.exponentPowerStore) := ⟨_, by taint_decide⟩

theorem exponentPower_ct : RelCT isa KeyRegEq
    (.seq (.block (([.ldrSp .r1 60] : List Instr) ++ VG.Impl.Bignum.Arm.TwoPower.code))
      (.seq (.block VG.Impl.Ffdh.Arm.ParameterCandidate.exponentPowerStore) (.block [])))
    (fun _ _ => True) := by
  refine (keyRegs_stack_ct (stackOnly_ct _ rfl) (by decide) (by decide)).seq ?_
  obtain ⟨hint, checked⟩ := powerStore_taint
  exact (RelCT.taint (A := taint) (Taint.ofRegs keyRegs)
    (fun _ _ h => Taint.agree_ofRegs h.1) checked).seq (RelCT.block_nil (fun _ _ _ => trivial))

theorem exponentHalfLoop_key_ct : RelCT isa (Two ExponentCountState)
    (.loop VG.Impl.Ffdh.Arm.ParameterCandidate.exponentHalf .ne) KeyRegEq := by
  refine keyRegs_keep_ct exponentHalfLoop_ct ?_ (by decide) (by decide)
  rintro s t ⟨p, left, right, sp⟩
  refine ⟨?_, sp⟩
  intro r hr
  simp only [keyRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact left.ready.r7.trans right.ready.r7.symm
  · exact left.ready.r8.trans right.ready.r8.symm
  · exact left.ready.r9.trans right.ready.r9.symm

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end

/-! ### `Ffdh.Arm.ParameterCandidate.CTExponentCopy`, which only this module used -/

section

/-! Copy the public modulus while retaining the bounded shift counter. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Ffdh.Arm.KeySearch

private theorem copy27_taint : CandidateCert keyRegs (VG.Impl.Rsa.Arm.Keys.copy 27 0) := ⟨_, by taint_decide⟩

private theorem copy27_ok (p : ExponentCountData) (s : State) (h : ExponentCountState p s) :
    WP isa (VG.Impl.Rsa.Arm.Keys.copy 27 0) s (ExponentCountState p) := by
  refine WP.mono (keyCopy_ok h.workspace h.ready (o := 27) (a := 0) (by decide) (by decide) (by decide)) ?_
  rintro t ⟨ready, keep, _, rest⟩
  have frame := key_keep_workspace h.workspace h.ready (by simp) keep
  have saved : t.mem.readW (State.addr (t.sp + 64#32)) 32 = BitVec.ofNat 32 p.count := by
    rw [rest.sp, frame.readW (r := ⟨State.addr (s.sp + 64#32), 4⟩) (Region.contains_self _ _) ?_ (by decide)]
    · exact h.saved
    · intro r hr
      rw [List.mem_singleton] at hr
      subst r
      rw [VG.Arm.addr_add (by have := h.stack.nowrap; omega_using [this])]
      exact h.separate.sub_left (Offset.sub_base _ (by decide : 64 + 4 ≤ 72))
  exact ⟨h.workspace.congr rest.wr, ready,
    (h.data.after_key_keep h.workspace h.ready (by simp) (by simp) keep).1,
    by rw [rest.sp]; exact h.stack.congr rest.wr,
    by rw [rest.sp]; exact h.separate, h.positive, h.bound, saved⟩

theorem exponentCopy_ct : RelCT isa (Two ExponentCountState) (VG.Impl.Rsa.Arm.Keys.copy 27 0)
    (Two ExponentCountState) := by
  refine two_post ?_ copy27_ok
  refine (keyRegs_taint_ct copy27_taint (by decide) (by decide)).mono ?_ (fun _ _ _ => trivial)
  rintro s t ⟨p, left, right, sp⟩
  refine ⟨?_, sp⟩
  intro r hr
  simp only [keyRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact left.ready.r7.trans right.ready.r7.symm
  · exact left.ready.r8.trans right.ready.r8.symm
  · exact left.ready.r9.trans right.ready.r9.symm

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end

/-! ### `Ffdh.Arm.ParameterCandidate.CTCountStep`, which only this module used -/

section

/-! Native decomposition steps expose only fixed stack slots and public RSA array-view addresses. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm

private theorem half29_taint : CandidateCert keyRegs (VG.Impl.Rsa.Arm.Keys.half 29) := ⟨_, by taint_decide⟩
private theorem copy29_taint : CandidateCert keyRegs (VG.Impl.Rsa.Arm.Keys.copy 29 0) := ⟨_, by taint_decide⟩
private theorem clear29_taint : CandidateCert keyRegs (.block (VG.Impl.Rsa.Arm.Keys.clrLow 29)) := ⟨_, by taint_decide⟩
private theorem countTail_taint : CandidateCert keyRegs
    (.block (VG.Impl.Ffdh.Arm.ParameterCandidate.halfCountTail.drop 4)) := ⟨_, by taint_decide⟩

private theorem countTail_ct : RelCT isa KeyRegEq (.block VG.Impl.Ffdh.Arm.ParameterCandidate.halfCountTail) KeyRegEq := by
  have countHead : RelCT isa (fun s t => s.sp = t.sp)
      (.block (([.ldrSp .r1 60, .dp .add .r1 .r1 (.imm 1)] : List Instr) ++ VG.Impl.Ffdh.Arm.ParameterCandidate.save .r1 60))
      (fun s t => s.sp = t.sp) :=
    RelCT.block_append ((stackOnly_ct [.ldrSp .r1 60, .dp .add .r1 .r1 (.imm 1)] rfl).seq (save_ct .r1 60))
  change RelCT isa KeyRegEq (.block (([.ldrSp .r1 60, .dp .add .r1 .r1 (.imm 1)] ++
    VG.Impl.Ffdh.Arm.ParameterCandidate.save .r1 60) ++ VG.Impl.Ffdh.Arm.ParameterCandidate.halfCountTail.drop 4)) KeyRegEq
  exact RelCT.block_append ((keyRegs_stack_ct countHead (by decide) (by decide)).seq
    (keyRegs_taint_ct countTail_taint (by decide) (by decide)))

theorem halfCountStep_ct : RelCT isa KeyRegEq VG.Impl.Ffdh.Arm.ParameterCandidate.halfCountStep KeyRegEq :=
  (keyRegs_stack_ct (stackOnly_ct [.mov .r11 (.imm 0)] rfl) (by decide) (by decide)).seq
    ((keyRegs_taint_ct half29_taint (by decide) (by decide)).seq
      (countTail_ct.seq (RelCT.block_nil (fun _ _ h => h))))

theorem expCountInit_ct : RelCT isa KeyRegEq VG.Impl.Ffdh.Arm.ParameterCandidate.expCountInit KeyRegEq :=
  (keyRegs_taint_ct copy29_taint (by decide) (by decide)).seq
    ((keyRegs_taint_ct clear29_taint (by decide) (by decide)).seq
      ((keyRegs_stack_ct (saveWord_ct .r1 60 0) (by decide) (by decide)).seq
        (RelCT.block_nil (fun _ _ h => h))))

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end

/-! ### `Ffdh.Arm.ParameterCandidate.CTMontKey`, which only this module used -/

section

/-! The compact RSA key-array view and its constants have public preparation traces. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.X25519.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Two two_post two_taint)

def MontKeyStart (p : MontMathData) (s : State) : Prop :=
  Workspace s p.base (8 * p.capacity) ∧ MontData p.base p.capacity p.words s.mem ∧
  (∃ k, p.words = Spec.Rsa.modulusWords k ∧ 64 ≤ k ∧ k ≤ 1024 ∧ Spec.Rsa.scratchWords k ≤ p.capacity) ∧
  InRegions (s.rd ++ s.wr) (State.addr s.sp) 4 ∧ s.mem.readW (State.addr s.sp) 32 = p.base

private def MontBasePointer (p : MontMathData) (s : State) : Prop := s.gpr .r0 = p.base
private def MontKeyReady (p : MontMathData) (s : State) : Prop := KeyReady p.base p.capacity p.words s

private theorem keyHeader_taint : CandidateCert [.r0]
    (.block ((VG.Impl.Ffdh.Arm.ParameterCandidate.keyContext.drop 1) ++ VG.Impl.Ffdh.Arm.ParameterCandidate.keyStride)) :=
  ⟨_, by taint_decide⟩

private theorem keyArrays_taint : CandidateCert [.r7, .r8, .r9]
    VG.Impl.Ffdh.Arm.ParameterCandidate.montKeyArrays := ⟨_, by taint_decide⟩

private theorem keyHeader_ready (p : MontMathData) (s : State) (h : MontKeyStart p s) :
    WP isa (.block (VG.Impl.Ffdh.Arm.ParameterCandidate.keyContext ++ VG.Impl.Ffdh.Arm.ParameterCandidate.keyStride)) s
      (MontKeyReady p) := by
  obtain ⟨k, width, lower, upper, space⟩ := h.2.2.1
  rw [WP.block_append_iff]
  have data : MontData p.base p.capacity (Spec.Rsa.modulusWords k) s.mem := by rw [← width]; exact h.2.1
  refine WP.mono (keyContext_ready s h.1 data lower upper space h.2.2.2.1 h.2.2.2.2) ?_
  rintro u ⟨ready, ptr, _, rest⟩
  refine WP.mono (keyStride_words (h.1.congr rest.wr) ready ptr) ?_
  rintro t ⟨_, restT⟩
  rw [← width] at ready
  exact ready.rest restT (by simp) (by simp) (by simp)

theorem montKeySetup_ct : RelCT isa (Two MontKeyStart) VG.Impl.Ffdh.Arm.ParameterCandidate.montKeySetup (fun _ _ => True) := by
  have load : RelCT isa (Two MontKeyStart) (.block [.ldrSp .r0 0]) (Two MontBasePointer) :=
    two_post ((loadStack_ct .r0 0).mono (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ _ => trivial)) (fun p s h => by
      refine wp_loadStack (a := State.addr s.sp) (by decide) (by simp only [BitVec.add_zero]) h.2.2.2.1 fun t loaded => WP.block_nil ?_
      exact loaded.gpr.trans h.2.2.2.2)
  obtain ⟨headerHint, headerChecked⟩ := keyHeader_taint
  have tail : RelCT isa (Two MontBasePointer)
      (.block ((VG.Impl.Ffdh.Arm.ParameterCandidate.keyContext.drop 1) ++ VG.Impl.Ffdh.Arm.ParameterCandidate.keyStride))
      (fun _ _ => True) := by
    refine two_taint [.r0] ?_ headerChecked
    intro p s t a b r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact a.trans b.symm
  have header := two_post (RelCT.block_append (load.seq tail)) keyHeader_ready
  obtain ⟨arrayHint, arrayChecked⟩ := keyArrays_taint
  have arrays : RelCT isa (Two MontKeyReady) VG.Impl.Ffdh.Arm.ParameterCandidate.montKeyArrays (fun _ _ => True) := by
    refine two_taint [.r7, .r8, .r9] ?_ arrayChecked
    intro p s t a b r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact a.r7.trans b.r7.symm
    · exact a.r8.trans b.r8.symm
    · exact a.r9.trans b.r9.symm
  exact header.seq arrays

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end

/-! ### `Ffdh.Arm.CandidatePrepareCT`, which only this module used -/

section

/-! Fast setup chooses its branch from the public byte count. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

def CandidatePrepareInput (base src : BitVec 32) (len k : Nat) (s : State) : Prop :=
  PrepareInput base src len k s ∧
    (k % 8 = 1 ∨ 2 ^ (64 * (Spec.Rsa.modulusWords k - 1)) ≤
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr src) k))

theorem candidatePrepare_ct {base src : BitVec 32} {len k : Nat}
    {P : State → Prop} {regions : List Region}
    (K : TwoExp.Montgomery base len (Spec.Rsa.modulusWords k) P regions)
    (ct : TwoExp.MontgomeryTiming K) :
    RelCT isa (fun s t => (CandidatePrepareInput base src len k s ∧ P s) ∧
      (CandidatePrepareInput base src len k t ∧ P t) ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.CandidatePrepare.code K.op) (fun _ _ => True) := by
  let E := fun s : State => CandidatePrepareInput base src len k s ∧ P s
  let C := fun s : State => E s ∧ s.z = decide (k % 8 = 1)
  have head : RelCT isa (fun s t => E s ∧ E t ∧ s.sp = t.sp)
      (.block VG.Impl.Ffdh.Arm.CandidatePrepare.choose) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r6]) _ (by taint_decide)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h.1.1.1.count.trans h.2.1.1.1.count.symm
  have post (s : State) (h : E s) :
      WP isa (.block VG.Impl.Ffdh.Arm.CandidatePrepare.choose) s C := by
    refine WP.mono (candidatePrepareChoice_ok s h.1.1 h.1.2) ?_
    rintro t ⟨input,norm,z,memory,rest⟩
    exact ⟨⟨⟨input,norm⟩, K.stable (by rw [memory]; exact Frame.refl _ _)
      (rest.mono (by simp [roundClobbers])) h.2⟩,z⟩
  have countFits (s : State) (h : E s) : 128 * Spec.Rsa.modulusWords k < 2 ^ 32 := by
    have := h.1.1.maxLength
    dsimp only [Spec.Rsa.modulusWords]
    omega_using [this]
  have branch : RelCT isa (fun s t => C s ∧ C t ∧ s.sp = t.sp)
      (.ite .eq (VG.Impl.Ffdh.Arm.SharedPrepare.code K.op)
        (VG.Impl.Ffdh.Arm.NormalizedPrepare.code K.op))
      (fun _ _ => True) := by
    refine RelCT.ite (fun s t h => by change some s.z = some t.z;rw [h.1.2,h.2.1.2]) ?_ ?_
    · intro s t trS trT u v h eS eT
      exact sharedPrepare_ct K ct (countFits s h.1.1.1) _ _ _ _ _ _
        ⟨⟨h.1.1.1.1.1,h.1.1.1.2⟩,⟨h.1.2.1.1.1.1,h.1.2.1.1.2⟩,h.1.2.2⟩ eS eT
    · intro s t trS trT u v h eS eT
      have notBoundary : k % 8 ≠ 1 := by
        have hz : s.z = false := Option.some.inj h.2
        rw [h.1.1.2] at hz
        exact of_decide_eq_false hz
      exact normalizedPrepare_ct K ct (countFits s h.1.1.1) _ _ _ _ _ _
        ⟨⟨h.1.1.1.1.1,h.1.1.1.2,h.1.1.1.1.2.resolve_left notBoundary⟩,
          ⟨h.1.2.1.1.1.1,h.1.2.1.1.2,h.1.2.1.1.1.2.resolve_left notBoundary⟩,h.1.2.2⟩ eS eT
  unfold VG.Impl.Ffdh.Arm.CandidatePrepare.code
  exact relCT_chain head post post branch

end VG.Proof.Ffdh.Arm

end

end

/-! ### `Ffdh.Arm.ParameterCandidate.CandidateReturn`, which the modules that import this one used -/

section

/-! ### `Ffdh.Arm.ParameterCandidate.Finish`, which only this module used -/

section

/-! Final candidate returns preserve an accepted p and clear every failed output. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/FinishWord.lean`, which only this module imported.
section

/-! Return the candidate status and write a complete u64 entropy count. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Ffdh.Arm VG.Proof.X25519.Arm

theorem finish_ok (s : State) (usedPtr : BitVec 32) (status count : Nat)
    (statusBound : status ≤ 2) (countBound : count < 2 ^ 32)
    (read : InRegions (s.rd ++ s.wr) (State.addr (s.sp + 32#32)) 4)
    (pointer : s.mem.readW (State.addr (s.sp + 32#32)) 32 = usedPtr)
    (output : OutputBuffer usedPtr 8 s) (value : s.gpr .r3 = BitVec.ofNat 32 count) :
    WP isa (.block (VG.Impl.Ffdh.Arm.ParameterCandidate.finish status)) s fun t =>
      t.gpr .r0 = BitVec.ofNat 32 status ∧
      Spec.Rsa.wordsAt t.mem (State.addr usedPtr) 1 = [BitVec.ofNat 64 count] ∧
      Frame [⟨State.addr usedPtr, 8⟩] s.mem t.mem ∧ Rest [.r0, .r1, .r2] s t := by
  have write0 : InRegions s.wr (State.addr usedPtr) 4 := by
    simpa only [BitVec.add_zero] using
      CallLay.inRegions_sub output.writable (off := 0) (by decide : 0 + 4 ≤ 8) (by decide)
  have write4 : InRegions s.wr (off (State.addr usedPtr) 4) 4 :=
    CallLay.inRegions_sub output.writable (by decide : 4 + 4 ≤ 8) (by decide)
  have addr4 : State.addr (usedPtr + 4#32) = off (State.addr usedPtr) 4 :=
    VG.Arm.addr_add (by have := output.fits; omega)
  have enc : encodable (BitVec.ofNat 32 status) = true := encodable_byte (by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : status < 2 ^ 32)]
    omega)
  have run : WP isa (.block (VG.Impl.Ffdh.Arm.ParameterCandidate.finish status)) s fun t =>
      (t.gpr .r0 = BitVec.ofNat 32 status ∧
        t.mem = (s.mem.writeW (State.addr usedPtr) (BitVec.ofNat 32 count)).writeW
          (off (State.addr usedPtr) 4) (0 : BitVec 32)) ∧ Rest [.r0, .r1, .r2] s t := by
    refine withRest_all [.r0, .r1, .r2] ?_ (by rfl) (by rfl)
    unfold VG.Impl.Ffdh.Arm.ParameterCandidate.finish
    ffrun [BitVec.add_zero, read, pointer, write0, write4, addr4, value, enc]
  refine WP.mono run ?_
  rintro t ⟨⟨result, memory⟩, rest⟩
  refine ⟨result, ?_, ?_, rest⟩
  · rw [memory]
    exact VG.Proof.Ffdh.Arm.KeySearch.usedMem_words s.mem usedPtr count countBound
  · rw [memory]
    exact VG.Proof.Ffdh.Arm.KeySearch.usedMem_frame s.mem usedPtr (BitVec.ofNat 32 count)

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Ffdh.Arm VG.Proof.Bignum.Arm VG.Proof.X25519.Arm

private theorem bytes_after_used {s t : State} {dst usedPtr : BitVec 32} {n consumed : Nat}
    (h : ResultContext dst usedPtr n consumed s) (changed : Frame [⟨State.addr usedPtr, 8⟩] s.mem t.mem) :
    Spec.Rsa.bytesAt t.mem (State.addr dst) n = Spec.Rsa.bytesAt s.mem (State.addr dst) n :=
  rsa_bytes_frame changed (by have := h.countFits; omega_using [this]) (by
    intro r hr
    rw [List.mem_singleton] at hr
    subst r
    exact h.outputUsed)

private theorem finishConsumed_ok {s : State} {dst usedPtr : BitVec 32} {n consumed status : Nat}
    (h : ResultContext dst usedPtr n consumed s) (bound : status ≤ 2) :
    WP isa (.block (([.ldrSp .r3 40] : List Instr) ++ VG.Impl.Ffdh.Arm.ParameterCandidate.finish status)) s fun t =>
      t.gpr .r0 = BitVec.ofNat 32 status ∧
      Spec.Rsa.wordsAt t.mem (State.addr usedPtr) 1 = [BitVec.ofNat 64 consumed] ∧
      Spec.Rsa.bytesAt t.mem (State.addr dst) n = Spec.Rsa.bytesAt s.mem (State.addr dst) n ∧
      Frame [⟨State.addr usedPtr, 8⟩] s.mem t.mem ∧ Rest [.r0, .r1, .r2, .r3] s t := by
  have saved : s.mem.readW (State.addr (s.sp + 40#32)) 32 = BitVec.ofNat 32 consumed := by
    simpa only [resultValues] using h.saved.saved 40 (by simp [resultSlots])
  rw [WP.block_append_iff]
  refine wp_loadStack (a := State.addr (s.sp + 40#32)) (by decide) rfl
    (h.saved.read (by decide)) fun u loaded => WP.block_nil ?_
  have memory := loaded.mem
  have rest : Rest [.r3] s u := loaded.rest (by simp)
  have ctx := h.after_memory memory rest
  have pointer : u.mem.readW (State.addr (u.sp + 32#32)) 32 = usedPtr := by
    simpa only [resultValues] using ctx.saved.saved 32 (by simp [resultSlots])
  refine WP.mono (finish_ok u usedPtr status consumed bound h.consumedFits
    (ctx.saved.read (by decide)) pointer ctx.used (loaded.gpr.trans saved)) ?_
  rintro t ⟨result, words, changed, restT⟩
  rw [memory] at changed
  exact ⟨result, words, bytes_after_used h changed, changed,
    (rest.mono (by simp)).trans (restT.mono (by simp))⟩

theorem finAccepted_ok {s : State} {dst usedPtr : BitVec 32} {n consumed : Nat}
    (h : ResultContext dst usedPtr n consumed s) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.finAccepted s fun t =>
      t.gpr .r0 = BitVec.ofNat 32 1 ∧
      Spec.Rsa.wordsAt t.mem (State.addr usedPtr) 1 = [BitVec.ofNat 64 consumed] ∧
      Spec.Rsa.bytesAt t.mem (State.addr dst) n = Spec.Rsa.bytesAt s.mem (State.addr dst) n ∧
      Frame [⟨State.addr dst, n⟩, ⟨State.addr usedPtr, 8⟩] s.mem t.mem ∧ Rest [.r0, .r1, .r2, .r3, .lr] s t := by
  refine WP.mono (finishConsumed_ok h (status := 1) (by decide)) ?_
  rintro t ⟨result, words, bytes, changed, rest⟩
  exact ⟨result, words, bytes, changed.mono (by simp), rest.mono (by simp)⟩

theorem finRejected_ok {s : State} {dst usedPtr : BitVec 32} {n consumed : Nat}
    (h : ResultContext dst usedPtr n consumed s) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.finRejected s fun t =>
      t.gpr .r0 = BitVec.ofNat 32 2 ∧
      Spec.Rsa.wordsAt t.mem (State.addr usedPtr) 1 = [BitVec.ofNat 64 consumed] ∧
      Spec.Rsa.bytesAt t.mem (State.addr dst) n = List.replicate n 0 ∧
      Frame [⟨State.addr dst, n⟩, ⟨State.addr usedPtr, 8⟩] s.mem t.mem ∧ Rest [.r0, .r1, .r2, .r3, .lr] s t := by
  rw [VG.Impl.Ffdh.Arm.ParameterCandidate.finRejected, WP.seq_iff]
  refine WP.mono (clearOutput_ok h) ?_
  rintro u ⟨ctx, cleared, changed, rest⟩
  refine WP.mono (finishConsumed_ok ctx (status := 2) (by decide)) ?_
  rintro t ⟨result, words, bytes, changedT, restT⟩
  exact ⟨result, words, bytes.trans cleared,
    (changed.mono (by simp)).trans (changedT.mono (by simp)),
    (rest.mono (by simp)).trans (restT.mono (by simp))⟩

private theorem finishZero_ok {s : State} {dst usedPtr : BitVec 32} {n consumed : Nat}
    (h : ResultContext dst usedPtr n consumed s) :
    WP isa (.block (([.mov .r3 (.imm 0)] : List Instr) ++ VG.Impl.Ffdh.Arm.ParameterCandidate.finish 0)) s fun t =>
      t.gpr .r0 = BitVec.ofNat 32 0 ∧
      Spec.Rsa.wordsAt t.mem (State.addr usedPtr) 1 = [BitVec.ofNat 64 0] ∧
      Spec.Rsa.bytesAt t.mem (State.addr dst) n = Spec.Rsa.bytesAt s.mem (State.addr dst) n ∧
      Frame [⟨State.addr usedPtr, 8⟩] s.mem t.mem ∧ Rest [.r0, .r1, .r2, .r3] s t := by
  rw [WP.block_append_iff]
  refine wp_mov (op2_imm (v := (0 : BitVec 32)) (by decide)) fun u moved => WP.block_nil ?_
  have rest : Rest [.r3] s u := moved.rest (by simp)
  have ctx := h.after_memory moved.mem rest
  have pointer : u.mem.readW (State.addr (u.sp + 32#32)) 32 = usedPtr := by
    simpa only [resultValues] using ctx.saved.saved 32 (by simp [resultSlots])
  refine WP.mono (finish_ok u usedPtr 0 0 (by decide) (by decide)
    (ctx.saved.read (by decide)) pointer ctx.used moved.gpr) ?_
  rintro t ⟨result, words, changed, restT⟩
  rw [moved.mem] at changed
  exact ⟨result, words, bytes_after_used h changed, changed,
    (rest.mono (by simp)).trans (restT.mono (by simp))⟩

theorem finNone_ok {s : State} {dst usedPtr : BitVec 32} {n consumed : Nat}
    (h : ResultContext dst usedPtr n consumed s) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.finNone s fun t =>
      t.gpr .r0 = BitVec.ofNat 32 0 ∧
      Spec.Rsa.wordsAt t.mem (State.addr usedPtr) 1 = [BitVec.ofNat 64 0] ∧
      Spec.Rsa.bytesAt t.mem (State.addr dst) n = List.replicate n 0 ∧
      Frame [⟨State.addr dst, n⟩, ⟨State.addr usedPtr, 8⟩] s.mem t.mem ∧ Rest [.r0, .r1, .r2, .r3, .lr] s t := by
  rw [VG.Impl.Ffdh.Arm.ParameterCandidate.finNone, WP.seq_iff]
  refine WP.mono (clearOutput_ok h) ?_
  rintro u ⟨ctx, cleared, changed, rest⟩
  refine WP.mono (finishZero_ok ctx) ?_
  rintro t ⟨result, words, bytes, changedT, restT⟩
  exact ⟨result, words, bytes.trans cleared,
    (changed.mono (by simp)).trans (changedT.mono (by simp)),
    (rest.mono (by simp)).trans (restT.mono (by simp))⟩

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end

/-! Candidate returns use the exact tape suffix, encoded p, and API status. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/Result.lean`, which only this module imported.
section

/-! Interpret the native phase status as the candidate API's output and count. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.X25519.Arm

def ResultPost (s : State) (dst usedPtr : BitVec 32) (n consumed status : Nat) (t : State) : Prop :=
  t.gpr .r0 = BitVec.ofNat 32 status ∧
  Spec.Rsa.wordsAt t.mem (State.addr usedPtr) 1 = [BitVec.ofNat 64 (if status = 0 then 0 else consumed)] ∧
  Spec.Rsa.bytesAt t.mem (State.addr dst) n =
    (if status = 1 then Spec.Rsa.bytesAt s.mem (State.addr dst) n else List.replicate n 0) ∧
  Frame [⟨State.addr dst, n⟩, ⟨State.addr usedPtr, 8⟩] s.mem t.mem ∧ Rest [.r0, .r1, .r2, .r3, .lr] s t

private theorem ResultPost.trans_pre {s u t : State} {dst usedPtr : BitVec 32} {n consumed status : Nat}
    (post : ResultPost u dst usedPtr n consumed status t) (memory : u.mem = s.mem) (rest : Rest [] s u) :
    ResultPost s dst usedPtr n consumed status t := by
  obtain ⟨result, words, bytes, changed, kept⟩ := post
  refine ⟨result, words, ?_, ?_, (rest.mono (by simp)).trans kept⟩
  · simpa only [memory] using bytes
  · simpa only [memory] using changed

private theorem resultTail_ok {s : State} {dst usedPtr : BitVec 32} {n consumed status : Nat}
    (h : ResultContext dst usedPtr n consumed s) (bound : status ≤ 2) (nonzero : status ≠ 0)
    (word : s.gpr .r3 = BitVec.ofNat 32 status) :
    WP isa (VG.Impl.Ffdh.Arm.ParameterCandidate.seqs [
      .block [.cmp .r3 (.imm 1)], .ite .eq VG.Impl.Ffdh.Arm.ParameterCandidate.finAccepted
        VG.Impl.Ffdh.Arm.ParameterCandidate.finRejected]) s (ResultPost s dst usedPtr n consumed status) := by
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.seqs
  refine WP.seq (WP.mono (cmpStatus_ok status 1 (by omega) (by decide) word) ?_)
  rintro u ⟨⟨zero, memory⟩, rest⟩
  have ctx := h.after_memory memory rest
  by_cases one : status = 1
  · refine WP.seq (WP.ite true (by change some u.z = some true; rw [zero, decide_eq_true one]) ?_ (by intro h; cases h))
    intro _
    refine WP.mono (finAccepted_ok ctx) ?_
    intro t returned
    refine WP.block_nil ?_
    rw [one]
    exact (show ResultPost u dst usedPtr n consumed 1 t from returned).trans_pre memory rest
  · have two : status = 2 := by omega
    refine WP.seq (WP.ite false (by change some u.z = some false; rw [zero, decide_eq_false one]) (by intro h; cases h) ?_)
    intro _
    refine WP.mono (finRejected_ok ctx) ?_
    intro t returned
    refine WP.block_nil ?_
    rw [two]
    exact (show ResultPost u dst usedPtr n consumed 2 t from returned).trans_pre memory rest

theorem result_ok {s : State} {dst usedPtr : BitVec 32} {n consumed status : Nat}
    (h : ResultContext dst usedPtr n consumed s) (bound : status ≤ 2)
    (word : s.gpr .r3 = BitVec.ofNat 32 status) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.result s (ResultPost s dst usedPtr n consumed status) := by
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.result VG.Impl.Ffdh.Arm.ParameterCandidate.seqs
  refine WP.seq (WP.mono (cmpStatus_ok status 0 (by omega) (by decide) word) ?_)
  rintro u ⟨⟨zero, memory⟩, rest⟩
  have ctx := h.after_memory memory rest
  by_cases none : status = 0
  · refine WP.seq (WP.ite true (by change some u.z = some true; rw [zero, decide_eq_true none]) ?_ (by intro h; cases h))
    intro _
    refine WP.mono (finNone_ok ctx) ?_
    intro t returned
    refine WP.block_nil ?_
    rw [none]
    exact (show ResultPost u dst usedPtr n consumed 0 t from returned).trans_pre memory rest
  · refine WP.seq (WP.ite false (by change some u.z = some false; rw [zero, decide_eq_false none]) (by intro h; cases h) ?_)
    intro _
    refine WP.mono (resultTail_ok ctx bound none ((rest.gpr .r3 (by simp)).trans word)) ?_
    intro t returned
    refine WP.block_nil ?_
    exact returned.trans_pre memory rest

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.X25519.Arm

def candidateReturnRegions (p : CandidateParams) (sp : BitVec 32) : List Region :=
  ⟨State.addr p.usedPtr, 8⟩ :: candidateRegions p sp

def CandidateReturn (p : CandidateParams) (answer : Option (Bool × List Byte)) (s t : State) : Prop :=
  t.gpr .r0 = BitVec.ofNat 32 (witnessResultStatus answer) ∧
  Spec.Rsa.wordsAt t.mem (State.addr p.usedPtr) 1 =
    [BitVec.ofNat 64 (match answer with | none => 0 | some (_, rest) => p.bytes.length - rest.length)] ∧
  Spec.Rsa.bytesAt t.mem (State.addr p.out) p.length =
    (match answer with | some (true, _) => Spec.Rsa.i2osp p.candidate p.length | _ => List.replicate p.length 0) ∧
  Frame (candidateReturnRegions p s.sp) s.mem t.mem ∧ Rest roundClobbers s t

theorem witnessResultStatus_bound (answer : Option (Bool × List Byte)) : witnessResultStatus answer ≤ 2 := by
  cases answer with
  | none => decide
  | some pair => obtain ⟨pass, rest⟩ := pair; cases pass <;> simp only [witnessResultStatus] <;> omega_using []

theorem CandidateReturn.trans_pre {s u t : State} {p : CandidateParams} {answer : Option (Bool × List Byte)}
    {rs : List Reg} (post : CandidateReturn p answer u t)
    (changed : Frame (candidateRegions p s.sp) s.mem u.mem) (rest : Rest rs s u)
    (clobbers : ∀ r ∈ rs, r ∈ roundClobbers) : CandidateReturn p answer s t := by
  obtain ⟨status, count, bytes, frame, restT⟩ := post
  rw [rest.sp] at frame
  exact ⟨status, count, bytes, (changed.mono (by intro r hr; exact List.mem_cons_of_mem _ hr)).trans frame,
    (rest.mono clobbers).trans restT⟩

private theorem candidateReturn_of_result {s : State} {p : CandidateParams} {used : Nat} {answer : Option (Bool × List Byte)}
    (h : CandidateContext p used s)
    (suffix : ∀ pass rest, answer = some (pass, rest) → rest = p.bytes.drop used)
    (number : ∀ rest, answer = some (true, rest) →
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr p.out) p.length) = p.candidate) :
    ∀ t, ResultPost s p.out p.usedPtr p.length used (witnessResultStatus answer) t → CandidateReturn p answer s t := by
  rintro t ⟨result, words, bytes, changed, rest⟩
  refine ⟨result, ?_, ?_, changed.mono (by simp [candidateReturnRegions, candidateRegions]),
    rest.mono (by simp [roundClobbers])⟩
  · cases ha : answer with
    | none => simpa [ha, witnessResultStatus] using words
    | some pair =>
      obtain ⟨pass, tail⟩ := pair
      have tailEq := suffix pass tail ha
      change Spec.Rsa.wordsAt t.mem (State.addr p.usedPtr) 1 = [BitVec.ofNat 64 (p.bytes.length - tail.length)]
      rw [tailEq, List.length_drop]
      have usedEq : p.bytes.length - (p.bytes.length - used) = used := by have := h.consumedBound; omega_using [this]
      rw [usedEq]
      cases pass <;> simpa [ha, witnessResultStatus] using words
  · cases ha : answer with
    | none => simpa [ha, witnessResultStatus] using bytes
    | some pair =>
      obtain ⟨pass, tail⟩ := pair
      cases pass with
      | false => simpa [ha, witnessResultStatus] using bytes
      | true =>
        have encoded := (VG.Proof.Rsa.i2osp_os2ip (Spec.Rsa.bytesAt s.mem (State.addr p.out) p.length)).symm
        have size : (Spec.Rsa.bytesAt s.mem (State.addr p.out) p.length).length = p.length := by simp [Spec.Rsa.bytesAt]
        rw [size, number tail ha] at encoded
        exact (show Spec.Rsa.bytesAt t.mem (State.addr p.out) p.length =
          Spec.Rsa.bytesAt s.mem (State.addr p.out) p.length from by simpa [ha, witnessResultStatus] using bytes).trans encoded

theorem candidateResult_ok {s : State} {p : CandidateParams} {used : Nat} {answer : Option (Bool × List Byte)}
    (h : CandidateContext p used s)
    (status : s.gpr .r3 = BitVec.ofNat 32 (witnessResultStatus answer))
    (suffix : ∀ pass rest, answer = some (pass, rest) → rest = p.bytes.drop used)
    (number : ∀ rest, answer = some (true, rest) →
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr p.out) p.length) = p.candidate) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.result s (CandidateReturn p answer s) :=
  WP.mono (result_ok h.result_context (witnessResultStatus_bound answer) status)
    (candidateReturn_of_result h suffix number)

theorem candidateRejected_ok {s : State} {p : CandidateParams} {used : Nat}
    (h : CandidateContext p used s) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.finRejected s
      (CandidateReturn p (some (false, p.bytes.drop used)) s) := by
  refine WP.mono (finRejected_ok h.result_context) ?_
  intro t returned
  exact candidateReturn_of_result h (by intro pass tail eq; cases eq; rfl)
    (by intro tail eq; cases eq) t returned

theorem candidateNone_ok {s : State} {p : CandidateParams} {used : Nat}
    (h : CandidateContext p used s) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.finNone s (CandidateReturn p none s) := by
  refine WP.mono (finNone_ok h.result_context) ?_
  intro t returned
  exact candidateReturn_of_result h (by intro pass tail eq; cases eq)
    (by intro tail eq; cases eq) t returned

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end

/-! ### `Ffdh.Arm.ParameterCandidate.CTCandidateTest`, which the modules that import this one used -/

section

/-! ### `Ffdh.Arm.ParameterCandidate.CTPhaseRun`, which this module and modules that import it used -/

section

/-! ### `Ffdh.Arm.ParameterCandidate.CTCountLoop`, which only this module used -/

section

/-! Native factor-of-two decomposition follows the same public modulus in both runs. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Arm.Keys (num)
open VG.Proof.Ffdh.Arm.KeySearch (Two)

structure CountData where
  math : MontMathData
  number : Nat
  count : Nat

structure CountState (p : CountData) (s : State) : Prop where
  workspace : Workspace s p.math.base (8 * p.math.capacity)
  ready : KeyReady p.math.base p.math.capacity p.math.words s
  data : MontData p.math.base p.math.capacity p.math.words s.mem
  stack : Workspace s s.sp 72
  separate : (⟨State.addr s.sp, 72⟩ : Region).Disjoint ⟨State.addr p.math.base, 8 * p.math.capacity⟩
  number : num s.mem (p.math.base + 96#32) (2 * p.math.words + 2) 29 = p.number
  positive : 0 < p.number
  even : p.number % 2 = 0
  saved : s.mem.readW (State.addr (s.sp + 60#32)) 32 = BitVec.ofNat 32 p.count

private structure CountAfter (p : CountData) (s : State) : Prop where
  workspace : Workspace s p.math.base (8 * p.math.capacity)
  ready : KeyReady p.math.base p.math.capacity p.math.words s
  data : MontData p.math.base p.math.capacity p.math.words s.mem
  stack : Workspace s s.sp 72
  separate : (⟨State.addr s.sp, 72⟩ : Region).Disjoint ⟨State.addr p.math.base, 8 * p.math.capacity⟩
  number : num s.mem (p.math.base + 96#32) (2 * p.math.words + 2) 29 = p.number / 2
  saved : s.mem.readW (State.addr (s.sp + 60#32)) 32 = BitVec.ofNat 32 (p.count + 1)
  zero : s.z = decide (p.number / 2 % 2 = 0)

private theorem countAfter_ok (p : CountData) (s : State) (h : CountState p s) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.halfCountStep s (CountAfter p) := by
  refine WP.mono (halfCountStep_ok h.workspace h.ready h.data h.stack h.saved h.separate) ?_
  rintro t ⟨ready, data, number, saved, zero, _, _, _, rest⟩
  rw [h.number] at number zero
  exact ⟨h.workspace.congr rest.wr, ready, data, by rw [rest.sp]; exact h.stack.congr rest.wr,
    by rw [rest.sp]; exact h.separate, number, saved, zero⟩

private theorem countPair_keyRegs {p : CountData} {s t : State}
    (left : CountState p s) (right : CountState p t) (sp : s.sp = t.sp) : KeyRegEq s t := by
  refine ⟨?_, sp⟩
  intro r hr
  simp only [keyRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact left.ready.r7.trans right.ready.r7.symm
  · exact left.ready.r8.trans right.ready.r8.symm
  · exact left.ready.r9.trans right.ready.r9.symm

private theorem countStep_fixed (p : CountData) :
    RelCT isa (fun s t => CountState p s ∧ CountState p t ∧ s.sp = t.sp)
      VG.Impl.Ffdh.Arm.ParameterCandidate.halfCountStep
      (fun s t => CountAfter p s ∧ CountAfter p t ∧ s.sp = t.sp) := by
  intro s t trS trT u v h runS runT
  have leak := (halfCountStep_ct _ _ _ _ _ _ (countPair_keyRegs h.1 h.2.1 h.2.2) runS runT).1
  obtain ⟨_, u', execS, postS⟩ := countAfter_ok p s h.1
  obtain ⟨_, v', execT, postT⟩ := countAfter_ok p t h.2.1
  obtain ⟨_, rfl⟩ := Exec.det runS execS
  obtain ⟨_, rfl⟩ := Exec.det runT execT
  exact ⟨leak, postS, postT, (Exec.rdwr runS).2.2.trans (h.2.2.trans (Exec.rdwr runT).2.2.symm)⟩

private def CountLoopPair (remaining : Nat) (s t : State) : Prop :=
  ∃ p : CountData, p.number = remaining ∧ CountState p s ∧ CountState p t ∧ s.sp = t.sp

private theorem CountAfter.continue {p : CountData} {s : State}
    (h : CountAfter p s) (positive : 0 < p.number) (even : p.number % 2 = 0)
    (go : isa.eval .eq s = some true) : CountState ⟨p.math, p.number / 2, p.count + 1⟩ s := by
  have nextEven : p.number / 2 % 2 = 0 := by
    change some s.z = some true at go
    rw [h.zero] at go
    exact of_decide_eq_true (Option.some.inj go)
  have nextPositive : 0 < p.number / 2 := by omega_using [positive, even]
  exact ⟨h.workspace, h.ready, h.data, h.stack, h.separate, h.number, nextPositive, nextEven, h.saved⟩

theorem halfCountLoop_ct : RelCT isa (Two CountState)
    (.loop VG.Impl.Ffdh.Arm.ParameterCandidate.halfCountStep .eq) (fun _ _ => True) := by
  have step : ∀ n, RelCT isa (CountLoopPair n) VG.Impl.Ffdh.Arm.ParameterCandidate.halfCountStep
      (fun u v => isa.eval .eq u = isa.eval .eq v ∧
        (isa.eval .eq u = some false → True) ∧
        (isa.eval .eq u = some true → ∃ m, m < n ∧ CountLoopPair m u v)) := by
    intro n s t trS trT u v h runS runT
    obtain ⟨p, remaining, left, right, sp⟩ := h
    obtain ⟨leak, postU, postV, spUV⟩ := countStep_fixed p _ _ _ _ _ _ ⟨left, right, sp⟩ runS runT
    refine ⟨leak, ?_, by intro _; trivial, ?_⟩
    · change some u.z = some v.z
      rw [postU.zero, postV.zero]
    · intro go
      have goV : isa.eval .eq v = some true := by change some v.z = some true; change some u.z = some true at go; rw [postV.zero, ← postU.zero]; exact go
      exact ⟨p.number / 2, by rw [← remaining]; exact Nat.div_lt_self left.positive (by decide),
        ⟨p.math, p.number / 2, p.count + 1⟩, rfl, postU.continue left.positive left.even go,
        postV.continue right.positive right.even goV, spUV⟩
  intro s t trS trT u v h runS runT
  obtain ⟨p, left, right, sp⟩ := h
  exact RelCT.loop CountLoopPair step p.number _ _ _ _ _ _ ⟨p, rfl, left, right, sp⟩ runS runT

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end

/-! Both native probable-prime phases prepare and draw solely from public inputs. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/CTWitnessMask.lean`, which only this module imported.
section

/-! Masking a sampled witness reveals only the public phase bit width. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Ffdh.Arm.KeySearch

structure WitnessMaskData where
  base : BitVec 32
  capacity : Nat
  words : Nat
  bits : Nat

structure WitnessMaskStart (p : WitnessMaskData) (s : State) : Prop where
  ready : ArithmeticReady p.base p.capacity p.words s
  stack : Workspace s s.sp 72
  positive : 0 < p.bits
  bound : p.bits ≤ 8192
  saved : s.mem.readW (State.addr (s.sp + 44#32)) 32 = BitVec.ofNat 32 p.bits

private def WitnessMaskHead (p : WitnessMaskData) (s : State) : Prop :=
  ArithmeticReady p.base p.capacity p.words s ∧
  s.gpr .r5 = BitVec.ofNat 32 ((p.bits - 1) / 32) ∧
  s.gpr .r6 = BitVec.ofNat 32 ((p.bits - 1) % 32 + 1)

private theorem maskHead_ok (p : WitnessMaskData) (s : State) (h : WitnessMaskStart p s) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.witnessMaskHead) s (WitnessMaskHead p) := by
  refine WP.mono (witnessMaskHead_ok h.stack h.positive h.bound h.saved) ?_
  rintro t ⟨⟨index, count, mem⟩, rest⟩
  exact ⟨h.ready.of_mem mem rest ((rest.gpr .r0 (by simp)).trans h.ready.ptr), index, count⟩

private def maskStoreData (p : WitnessMaskData) : MaskStoreData :=
  ⟨p.base, p.capacity, p.words, (p.bits - 1) / 32⟩

private theorem maskBits_ok (p : WitnessMaskData) (s : State) (h : WitnessMaskHead p s) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.witnessMaskBits s (MaskStoreStart (maskStoreData p)) := by
  refine WP.mono (witnessMaskBits_ok (by omega : (p.bits - 1) % 32 + 1 ≤ 32) h.2.2) ?_
  rintro t ⟨_, mem, rest⟩
  exact ⟨h.1.of_mem mem rest ((rest.gpr .r0 (by simp)).trans h.1.ptr), (rest.gpr .r5 (by simp)).trans h.2.1⟩

theorem witnessMask_ct : RelCT isa (Two WitnessMaskStart)
    VG.Impl.Ffdh.Arm.ParameterCandidate.witnessMask (fun _ _ => True) := by
  have head : RelCT isa (Two WitnessMaskStart)
      (.block VG.Impl.Ffdh.Arm.ParameterCandidate.witnessMaskHead) (Two WitnessMaskHead) :=
    two_post ((stackOnly_ct _ rfl).mono (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ _ => trivial)) maskHead_ok
  have bitsTrace : RelCT isa (fun s t => s.sp = t.sp)
      VG.Impl.Ffdh.Arm.ParameterCandidate.witnessMaskBits (fun s t => s.sp = t.sp) :=
    (stackOnly_ct _ rfl).seq ((stackOnly_ct _ rfl).seq (stackOnly_ct _ rfl))
  have bits : RelCT isa (Two WitnessMaskHead) VG.Impl.Ffdh.Arm.ParameterCandidate.witnessMaskBits
      (Two MaskStoreStart) :=
    (two_post (bitsTrace.mono (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ _ => trivial)) maskBits_ok).mono
      (fun _ _ h => h) (fun _ _ ⟨p, left, right, sp⟩ => ⟨maskStoreData p, left, right, sp⟩)
  exact head.seq (bits.seq (witnessMaskStore_ct.seq (RelCT.block_nil (fun _ _ _ => trivial))))

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/CTSampleWitness.lean`, which only this module imported.
section

/-! Sample import and truncation reuse RSA's operand import timing proof. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Ffdh.Arm.KeySearch

structure WitnessSampleData where
  mask : WitnessMaskData
  source : BitVec 32

structure WitnessSampleStart (p : WitnessSampleData) (s : State) : Prop where
  mask : WitnessMaskStart p.mask s
  stackSep : (⟨State.addr s.sp, 72⟩ : Region).Disjoint ⟨State.addr p.mask.base, 8 * p.mask.capacity⟩
  bitsFit : p.mask.bits ≤ 64 * p.mask.words
  sourceFit : p.source.toNat + (p.mask.bits + 7) / 8 ≤ 2 ^ 32
  sourceRead : InRegions (s.rd ++ s.wr) (State.addr p.source) ((p.mask.bits + 7) / 8)
  sourceSep : (⟨State.addr p.source, (p.mask.bits + 7) / 8⟩ : Region).Disjoint ⟨State.addr p.mask.base, 8 * p.mask.capacity⟩
  source : s.gpr .r4 = p.source
  count : s.gpr .r6 = BitVec.ofNat 32 ((p.mask.bits + 7) / 8)

private theorem sampleImport_ok (p : WitnessSampleData) (s : State) (h : WitnessSampleStart p s) :
    WP isa (VG.Impl.Bignum.Arm.importOperand 1) s (WitnessMaskStart p.mask) := by
  refine WP.mono (importOperand_ok s h.mask.ready (o := 1) (by decide) (by decide)
    (by have := h.mask.positive; omega) (by have := h.bitsFit; omega) h.sourceFit h.sourceRead h.sourceSep h.source h.count) ?_
  rintro t ⟨ready, _, _, frame, rest⟩
  have saved : t.mem.readW (State.addr (t.sp + 44#32)) 32 = BitVec.ofNat 32 p.mask.bits := by
    rw [rest.sp, frame.readW (r := ⟨State.addr (s.sp + 44#32), 4⟩) (Region.contains_self _ _) ?_ (by decide)]
    · exact h.mask.saved
    · intro r hr
      rw [List.mem_singleton] at hr
      subst r
      rw [VG.Arm.addr_add (by have := h.mask.stack.nowrap; omega)]
      exact h.stackSep.sub_left (Offset.sub_base _ (by decide : 44 + 4 ≤ 72))
  exact ⟨ready, by rw [rest.sp]; exact h.mask.stack.congr rest.wr, h.mask.positive, h.mask.bound, saved⟩

theorem sampleWitness_ct : RelCT isa (Two WitnessSampleStart)
    VG.Impl.Ffdh.Arm.ParameterCandidate.sampleWitness (fun _ _ => True) := by
  have importTrace : RelCT isa (Two WitnessSampleStart) (VG.Impl.Bignum.Arm.importOperand 1) (fun _ _ => True) := by
    intro s t trS trT u v h runS runT
    obtain ⟨p, left, right, sp⟩ := h
    exact importOperand_ct (by decide : 1 < 8) _ _ _ _ _ _
      ⟨left.mask.ready, right.mask.ready, left.source, right.source, left.count, right.count, sp⟩ runS runT
  exact (two_post importTrace sampleImport_ok).seq
    (witnessMask_ct.mono (fun _ _ ⟨p, left, right, sp⟩ => ⟨p.mask, left, right, sp⟩) (fun _ _ h => h))

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/CTDrawSample.lean`, which only this module imported.
section

/-! Public entropy offsets determine the entire native witness import trace. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm
open VG.Proof.Ffdh.Arm.KeySearch

structure DrawPoint where
  params : WitnessParams
  used : Nat
  passed : Nat

def DrawStart (p : DrawPoint) (s : State) : Prop :=
  WitnessState p.params p.used p.passed s ∧ p.used + (p.params.bits + 7) / 8 ≤ p.params.bytes.length

private def drawSampleData (p : DrawPoint) : WitnessSampleData :=
  ⟨⟨p.params.base, p.params.capacity, p.params.words, p.params.bits⟩,
    p.params.tape + BitVec.ofNat 32 p.used⟩

private theorem drawSampleHead_ok (p : DrawPoint) (s : State) (h : DrawStart p s) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.drawHead s (WitnessSampleStart (drawSampleData p)) := by
  refine WP.mono (drawHead_ok h.1 h.2) ?_
  rintro t ⟨ctx, base, source, count, _, _⟩
  exact ⟨⟨ctx.ready base, ctx.saved.space, ctx.bitsPositive, ctx.bitsBound,
    by simpa only [witnessValues, drawSampleData] using ctx.saved.saved 44 (by simp [witnessSlots])⟩,
    ctx.stackScratch, ctx.bitsFit, ctx.source_fits h.2, ctx.source_read h.2, ctx.source_separate h.2,
    source, count⟩

theorem drawSample_ct : RelCT isa (Two DrawStart)
    VG.Impl.Ffdh.Arm.ParameterCandidate.drawSample (fun _ _ => True) := by
  have headTrace : RelCT isa (Two DrawStart) VG.Impl.Ffdh.Arm.ParameterCandidate.drawHead (fun _ _ => True) :=
    (drawArgs_ct.seq (save_ct .r1 40)).mono (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ _ => trivial)
  exact (two_post headTrace drawSampleHead_ok).seq
    (sampleWitness_ct.mono (fun _ _ ⟨p, left, right, sp⟩ => ⟨drawSampleData p, left, right, sp⟩) (fun _ _ h => h))

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/CTRoundCall.lean`, which only this module imported.
section

/-! Call exactly the selected shared RSA primality kernel and reuse its timing proof. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Two)
open VG.Proof.MillerRabin.Arm (RoundImpl LayoutLite PreparedLite roundPre roundPub)
open VG.Proof.Rsa.Mont (wOf)

structure SharedRoundStart (p : MontMathData) (s : State) : Prop where
  workspace : Workspace s p.base (8 * p.capacity)
  ptr : s.gpr .r0 = p.base
  length : s.gpr .r1 = BitVec.ofNat 32 p.capacity
  capacityBound : p.capacity < 2 ^ 32
  width : wOf s.mem (State.addr p.base) = p.words
  layout : LayoutLite s.mem (State.addr p.base) p.capacity
  prepared : PreparedLite s.mem (State.addr p.base)
  stackBelow : 56 ≤ s.sp.toNat
  belowSep : (FrameStack.belowA s.sp 56).Disjoint ⟨State.addr p.base, 8 * p.capacity⟩

private theorem sharedRoundPre {p : MontMathData} {s : State} (h : SharedRoundStart p s) :
    roundPre (s.callEntry.withRegions [] [⟨State.addr p.base, 8 * p.capacity⟩]) := by
  have r0entry : (s.callEntry.withRegions [] [⟨State.addr p.base, 8 * p.capacity⟩]).gpr .r0 = p.base := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), h.ptr]
  have r1entry : (s.callEntry.withRegions [] [⟨State.addr p.base, 8 * p.capacity⟩]).gpr .r1 = BitVec.ofNat 32 p.capacity := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), h.length]
  unfold roundPre
  rw [r0entry, r1entry, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h.capacityBound]
  exact ⟨rfl, rfl, h.workspace.nowrap, h.stackBelow, h.belowSep, h.layout, h.prepared⟩

private theorem sharedRoundCovers {p : MontMathData} {s : State} (h : SharedRoundStart p s) :
    Covers [⟨State.addr p.base, 8 * p.capacity⟩] s.wr := by
  apply Covers.of_sub
  intro r hr
  rw [List.mem_singleton] at hr
  subst r
  exact ⟨_, h.workspace.writable, 0, by simp, by simp⟩

theorem sharedRoundCall_ct (v : RoundImpl) : RelCT isa (Two SharedRoundStart)
    (.call v.name v.code) (fun _ _ => True) := by
  intro s t trS trT u z h runS runT
  obtain ⟨p, left, right, sp⟩ := h
  have call : RelCT isa (fun s t => SharedRoundStart p s ∧ SharedRoundStart p t ∧ s.sp = t.sp)
      (.call v.name v.code) (fun _ _ => True) := by
    refine RelCT.call v.verified.1 v.verified.2.1 [] [⟨State.addr p.base, 8 * p.capacity⟩] ?_
    intro a b h
    have coverA := sharedRoundCovers h.1
    have coverB := sharedRoundCovers h.2.1
    refine ⟨sharedRoundPre h.1, sharedRoundPre h.2.1, ?_, coverA.right, coverA, coverB.right, coverB⟩
    change roundPub _ _
    unfold roundPub
    simp only [State.withRegions_sp, State.callEntry_sp, State.withRegions_gpr,
      State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs),
      State.withRegions_mem, State.callEntry_mem, h.1.ptr, h.2.1.ptr, h.1.length, h.2.1.length,
      h.1.width, h.2.1.width]
    exact ⟨h.2.2, trivial, trivial, trivial⟩
  exact call _ _ _ _ _ _ ⟨left, right, sp⟩ runS runT

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/CTRoundPrepare.lean`, which only this module imported.
section

/-! Prepare the shared RSA primality call with the existing Montgomery encoder. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Ffdh.Arm.KeySearch
open VG.Proof.Rsa.Mont (numAt arrAt Operand)

structure RoundKernelData where
  math : MontMathData
  modulus : Nat

structure RoundKernelStart (p : RoundKernelData) (s : State) : Prop where
  ready : ArithmeticReady p.math.base p.math.capacity p.math.words s
  data : RoundData p.math.base p.math.capacity p.math.words p.modulus s.mem
  stack : Workspace s s.sp 72
  stackSep : (⟨State.addr s.sp, 72⟩ : Region).Disjoint ⟨State.addr p.math.base, 8 * p.math.capacity⟩
  saved : s.mem.readW (State.addr (s.sp + 36#32)) 32 = BitVec.ofNat 32 p.math.capacity
  below : 56 ≤ s.sp.toNat
  belowSep : (FrameStack.belowA s.sp 56).Disjoint ⟨State.addr p.math.base, 8 * p.math.capacity⟩

private structure RoundEncoded (p : RoundKernelData) (s : State) : Prop where
  start : RoundKernelStart p s
  encoded : numAt s.mem (State.addr p.math.base) p.math.words 5 < p.modulus

private theorem encodeReady_ok (b : MontBackend) (p : RoundKernelData) (s : State) (h : RoundKernelStart p s) :
    WP isa (VG.Impl.Bignum.Arm.MontCall.op b.name b.mul 5 1 4) s (RoundEncoded p) := by
  have operand (j : Nat) (member : j = 1 ∨ j = 5) : Operand j := by
    rcases member with rfl | rfl <;> simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  refine WP.mono (montCallEncode_ok b s h.ready (callStack_of_below h.below h.belowSep)
    (operand 5 (by simp)) (operand 1 (by simp)) (by decide) h.data.modulus h.data.odd h.data.r2) ?_
  rintro t ⟨ready, _, _, encoded, keeps, frame, rest⟩
  have saved : t.mem.readW (State.addr (t.sp + 36#32)) 32 = BitVec.ofNat 32 p.math.capacity := by
    rw [rest.sp, frame.readW (r := ⟨State.addr (s.sp + 36#32), 4⟩) (Region.contains_self _ _) ?_ (by decide)]
    · exact h.saved
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [VG.Arm.addr_add (by have := h.stack.nowrap; omega)]
        exact h.stackSep.sub_left (Offset.sub_base _ (by decide : 36 + 4 ≤ 72))
      · change (⟨State.addr (s.sp + BitVec.ofNat 32 36), 4⟩ : Region).Disjoint
          ⟨State.addr (s.sp - BitVec.ofNat 32 48), 48⟩
        rw [VG.Arm.addr_add (by have := h.stack.nowrap; omega),
          FrameStack.addr_sub' (by have := h.below; omega)]
        exact Offset.disjoint_below _ (by omega)
  refine ⟨⟨ready, h.data.after_operand (by decide) (by decide) (by decide) keeps,
    by rw [rest.sp]; exact h.stack.congr rest.wr,
    by rw [rest.sp]; exact h.stackSep, saved,
    by rw [rest.sp]; exact h.below,
    by rw [rest.sp]; exact h.belowSep⟩, ?_⟩
  rw [encoded]
  exact Nat.mod_lt _ (by have := h.data.large; omega)

private theorem encodeReady_ct (b : MontBackend) : RelCT isa (Two RoundKernelStart)
    (VG.Impl.Bignum.Arm.MontCall.op b.name b.mul 5 1 4) (Two RoundEncoded) := by
  refine two_post ?_ (encodeReady_ok b)
  intro s t trS trT u v h runS runT
  obtain ⟨p, left, right, sp⟩ := h
  have op (j : Nat) (member : j = 1 ∨ j = 4 ∨ j = 5) : Operand j := by
    rcases member with rfl | rfl | rfl <;> simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have boundL : numAt s.mem (State.addr p.math.base) p.math.words 4 < numAt s.mem (State.addr p.math.base) p.math.words 0 := by
    rw [left.data.r2, left.data.modulus]
    exact Nat.mod_lt _ (by have := left.data.large; omega)
  have boundR : numAt t.mem (State.addr p.math.base) p.math.words 4 < numAt t.mem (State.addr p.math.base) p.math.words 0 := by
    rw [right.data.r2, right.data.modulus]
    exact Nat.mod_lt _ (by have := right.data.large; omega)
  exact (montCallOp_ct b.name b.mul (b.rawCT (op 5 (by simp)) (op 1 (by simp)) (op 4 (by simp)))
    (op 5 (by simp)) (op 1 (by simp)) (op 4 (by simp))).mono (fun _ _ h => h) (fun _ _ _ => trivial)
    _ _ _ _ _ _ ⟨left.ready, right.ready, callStack_of_below left.below left.belowSep,
      callStack_of_below right.below right.belowSep, boundL, boundR, sp⟩ runS runT

private theorem callReady_ok (p : RoundKernelData) (s : State) (h : RoundEncoded p s) :
    WP isa (.block [.ldrSp .r0 0, .ldrSp .r1 36]) s (SharedRoundStart p.math) := by
  refine WP.mono (roundArgs_ok h.start.ready h.start.stack h.start.saved) ?_
  rintro t ⟨⟨ptr, length, mem⟩, rest⟩
  have data : RoundData p.math.base p.math.capacity p.math.words p.modulus t.mem := mem ▸ h.start.data
  exact ⟨h.start.ready.workspace.congr rest.wr, ptr, length,
    by have := h.start.ready.workspace.nowrap; omega,
    data.data.width, data.layout, data.prepared (by rw [mem]; exact h.encoded),
    by rw [rest.sp]; exact h.start.below,
    by rw [rest.sp]; exact h.start.belowSep⟩

theorem roundPrepared_ct (b : MontBackend) : RelCT isa (Two RoundKernelStart)
    (.seq (VG.Impl.Bignum.Arm.MontCall.op b.name b.mul 5 1 4) (.block [.ldrSp .r0 0, .ldrSp .r1 36]))
    (Two SharedRoundStart) := by
  have args : RelCT isa (Two RoundEncoded) (.block [.ldrSp .r0 0, .ldrSp .r1 36]) (Two SharedRoundStart) :=
    (two_post ((stackOnly_ct _ rfl).mono (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ _ => trivial)) callReady_ok).mono
      (fun _ _ h => h) (fun _ _ ⟨p, left, right, sp⟩ => ⟨p.math, left, right, sp⟩)
  exact (encodeReady_ct b).seq args

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/CTDecompose.lean`, which only this module imported.
section

/-! Decomposing the public modulus minus one has a public trace. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Arm.Keys (num)
open VG.Proof.Ffdh.Arm.KeySearch

structure DecomposeData where
  math : MontMathData
  modulus : Nat

structure DecomposeStart (p : DecomposeData) (s : State) : Prop where
  workspace : Workspace s p.math.base (8 * p.math.capacity)
  ready : KeyReady p.math.base p.math.capacity p.math.words s
  data : MontData p.math.base p.math.capacity p.math.words s.mem
  stack : Workspace s s.sp 72
  separate : (⟨State.addr s.sp, 72⟩ : Region).Disjoint ⟨State.addr p.math.base, 8 * p.math.capacity⟩
  number : num s.mem (p.math.base + 96#32) (2 * p.math.words + 2) 0 = p.modulus
  large : 1 < p.modulus
  odd : p.modulus % 2 = 1

private def decomposeCount (p : DecomposeData) : CountData := ⟨p.math, p.modulus - 1, 0⟩

private theorem decomposeInit_ok (p : DecomposeData) (s : State) (h : DecomposeStart p s) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.expCountInit s (CountState (decomposeCount p)) := by
  refine WP.mono (expCountInit_ok h.workspace h.ready h.data h.stack h.separate h.number h.large h.odd) ?_
  intro t ht
  exact ⟨ht.workspace, ht.ready, ht.data, ht.stack, ht.separate, ht.number, ht.positive, ht.even, ht.saved⟩

private theorem decomposeInit_ct : RelCT isa (Two DecomposeStart)
    VG.Impl.Ffdh.Arm.ParameterCandidate.expCountInit (fun _ _ => True) := by
  refine expCountInit_ct.mono ?_ (fun _ _ _ => trivial)
  rintro s t ⟨p, left, right, sp⟩
  refine ⟨?_, sp⟩
  intro r hr
  simp only [keyRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact left.ready.r7.trans right.ready.r7.symm
  · exact left.ready.r8.trans right.ready.r8.symm
  · exact left.ready.r9.trans right.ready.r9.symm

theorem expDecompose_ct : RelCT isa (Two DecomposeStart)
    VG.Impl.Ffdh.Arm.ParameterCandidate.expDecompose (fun _ _ => True) := by
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.expDecompose
  exact RelCT.seq (two_post decomposeInit_ct decomposeInit_ok)
    (halfCountLoop_ct.mono
      (fun _ _ ⟨p, left, right, sp⟩ => ⟨decomposeCount p, left, right, sp⟩)
      (fun _ _ h => h))

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/CTDrawRange.lean`, which only this module imported.
section

/-! Sampling and the shared full-width witness range check have public traces. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Ffdh.Arm.KeySearch

private def SampleReady (p : DrawPoint) (s : State) : Prop :=
  ArithmeticReady p.params.base p.params.capacity p.params.words s

theorem drawRange_ct : RelCT isa (Two DrawStart)
    VG.Impl.Ffdh.Arm.ParameterCandidate.drawRange (fun _ _ => True) := by
  have sample : RelCT isa (Two DrawStart) VG.Impl.Ffdh.Arm.ParameterCandidate.drawSample (Two SampleReady) :=
    two_post drawSample_ct (fun _ _ h => WP.mono (drawSample_ok h.1 h.2) (fun _ post => post.2.1))
  refine sample.seq ?_
  intro s t trS trT u v h runS runT
  obtain ⟨p, left, right, sp⟩ := h
  exact VG.Proof.Ffdh.Arm.inRange_ct (by simp [Proof.Rsa.Mont.Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp] : Proof.Rsa.Mont.Operand 1) (by decide : 1 ≠ 7)
    _ _ _ _ _ _ ⟨left, right, sp⟩ runS runT

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/CTRoundKernel.lean`, which only this module imported.
section

/-! End-to-end timing for the named shared compact-window primality call. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Two)
open VG.Proof.MillerRabin.Arm (RoundImpl)

theorem roundKernel_ct (b : VG.Proof.Bignum.Arm.MontBackend) (v : RoundImpl) : RelCT isa (Two RoundKernelStart)
    (VG.Impl.Ffdh.Arm.ParameterCandidate.roundKernel (VG.Impl.Bignum.Arm.MontCall.op b.name b.mul) v.name v.code) (fun _ _ => True) :=
  RelCT.assoc ((roundPrepared_ct b).seq ((sharedRoundCall_ct v).seq (RelCT.block_nil (fun _ _ _ => trivial))))

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/CTOnPass.lean`, which only this module imported.
section

/-! The successful-witness countdown follows the public round policy. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Ffdh.Arm.KeySearch

structure PassData where
  passed : Nat
  checks : Nat

structure PassStart (p : PassData) (s : State) : Prop where
  stack : Workspace s s.sp 72
  more : p.passed < p.checks
  bound : p.checks ≤ 128
  passed : s.mem.readW (State.addr (s.sp + 56#32)) 32 = BitVec.ofNat 32 p.passed
  checks : s.mem.readW (State.addr (s.sp + 52#32)) 32 = BitVec.ofNat 32 p.checks

private def PassHead (p : PassData) (s : State) : Prop := s.z = decide (p.passed + 1 = p.checks)

theorem onPass_ct : RelCT isa (Two PassStart) VG.Impl.Ffdh.Arm.ParameterCandidate.onPass (fun _ _ => True) := by
  have head : RelCT isa (Two PassStart)
      (.block VG.Impl.Ffdh.Arm.ParameterCandidate.onPassHead) (Two PassHead) :=
    two_post ((stackOnly_ct _ rfl).mono (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ _ => trivial))
      (fun _ _ h => WP.mono (passHead_ok h.stack h.more h.bound h.passed h.checks) (fun _ post => post.1.2.1))
  have choice : RelCT isa (Two PassHead)
      (.ite .eq (.block [.mov .r3 (.imm 1)]) (.block [.mov .r3 (.imm 4)])) (fun s t => s.sp = t.sp) := by
    refine two_ite (fun _ _ _ left right => ?_) ?_ ?_
    · change some _ = some _
      rw [left, right]
    · exact (stackOnly_ct _ rfl).mono (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ h => h)
    · exact (stackOnly_ct _ rfl).mono (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ h => h)
  have finish : RelCT isa (fun s t => s.sp = t.sp)
      (.block VG.Impl.Ffdh.Arm.ParameterCandidate.onPassFinish) (fun s t => s.sp = t.sp) :=
    RelCT.block_append ((save_ct .r1 56).seq (stackOnly_ct [.cmp .r3 (.imm 4)] rfl))
  exact head.seq (choice.seq (finish.seq (RelCT.block_nil (fun _ _ _ => trivial))))

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/CTRound.lean`, which only this module imported.
section

/-! Public witness values synchronize primality results and native success counters. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Ffdh.Arm.KeySearch
open VG.Proof.MillerRabin.Arm (RoundImpl)
open VG.Proof.Rsa.Mont (numAt)

structure RoundPoint where
  params : WitnessParams
  used : Nat
  passed : Nat
  witness : Nat

structure RoundStart (p : RoundPoint) (s : State) : Prop where
  state : WitnessState p.params p.used p.passed s
  more : p.passed < p.params.checks
  ready : ArithmeticReady p.params.base p.params.capacity p.params.words s
  input : numAt s.mem (State.addr p.params.base) p.params.words 1 = p.witness

private def roundKernelData (p : RoundPoint) : RoundKernelData :=
  ⟨⟨p.params.base, p.params.capacity, p.params.words⟩, p.params.modulus⟩

private theorem roundStart_kernel (p : RoundPoint) (s : State) (h : RoundStart p s) :
    RoundKernelStart (roundKernelData p) s :=
  ⟨h.ready, h.state.data, h.state.saved.space, h.state.stackScratch,
    by simpa only [witnessValues, roundKernelData] using h.state.saved.saved 36 (by simp [witnessSlots]),
    h.state.stackBelow, h.state.belowScratch⟩

private structure RoundReturned (p : RoundPoint) (s : State) : Prop where
  state : WitnessState p.params p.used p.passed s
  more : p.passed < p.params.checks
  result : (s.gpr .r0).toNat = if Proof.MillerRabin.Round.round p.params.modulus p.witness then 1 else 0

private theorem roundReturned_ok (b : VG.Proof.Bignum.Arm.MontBackend) (v : RoundImpl) (p : RoundPoint) (s : State) (h : RoundStart p s) :
    WP isa (VG.Impl.Ffdh.Arm.ParameterCandidate.roundKernel (VG.Impl.Bignum.Arm.MontCall.op b.name b.mul) v.name v.code) s (RoundReturned p) := by
  have saved : s.mem.readW (State.addr (s.sp + 36#32)) 32 = BitVec.ofNat 32 p.params.capacity := by
    simpa only [witnessValues] using h.state.saved.saved 36 (by simp [witnessSlots])
  refine WP.mono (roundKernel_ok b v h.ready h.state.data h.state.saved.space h.state.stackScratch
    saved h.state.stackBelow h.state.belowScratch h.input) ?_
  rintro t ⟨data, result, frame, rest⟩
  exact ⟨h.state.after_round data frame rest, h.more, result⟩

private structure RoundCompared (p : RoundPoint) (s : State) : Prop where
  state : WitnessState p.params p.used p.passed s
  more : p.passed < p.params.checks
  zero : s.z = !(Proof.MillerRabin.Round.round p.params.modulus p.witness)

private theorem roundCompared_ok (p : RoundPoint) (s : State) (h : RoundReturned p s) :
    WP isa (.block [.cmp .r0 (.imm 0)]) s (RoundCompared p) := by
  refine WP.mono (cmpResult_ok h.result) ?_
  rintro t ⟨⟨zero, mem⟩, rest⟩
  exact ⟨h.state.after_memory mem rest, h.more, zero⟩

theorem round_ct (b : VG.Proof.Bignum.Arm.MontBackend) (v : RoundImpl) : RelCT isa (Two RoundStart)
    (VG.Impl.Ffdh.Arm.ParameterCandidate.round (VG.Impl.Bignum.Arm.MontCall.op b.name b.mul) v.name v.code) (fun _ _ => True) := by
  have kernel : RelCT isa (Two RoundStart)
      (VG.Impl.Ffdh.Arm.ParameterCandidate.roundKernel (VG.Impl.Bignum.Arm.MontCall.op b.name b.mul) v.name v.code) (Two RoundReturned) :=
    two_post (two_map roundKernelData roundStart_kernel (roundKernel_ct b v)) (roundReturned_ok b v)
  have compare : RelCT isa (Two RoundReturned) (.block [.cmp .r0 (.imm 0)]) (Two RoundCompared) :=
    two_post ((stackOnly_ct _ rfl).mono (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ _ => trivial)) roundCompared_ok
  have choice : RelCT isa (Two RoundCompared)
      (.ite .eq (.block [.mov .r3 (.imm 2), .cmp .r3 (.imm 4)]) VG.Impl.Ffdh.Arm.ParameterCandidate.onPass)
      (fun _ _ => True) := by
    refine two_ite (fun _ _ _ left right => ?_) ?_ ?_
    · change some _ = some _
      rw [left.zero, right.zero]
    · exact (stackOnly_ct _ rfl).mono (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ _ => trivial)
    · refine two_map (fun p => (⟨p.passed, p.params.checks⟩ : PassData)) ?_ onPass_ct
      intro p s h
      exact ⟨h.1.state.saved.space, h.1.more, h.1.state.checksBound,
        by simpa only [witnessValues] using h.1.state.saved.saved 56 (by simp [witnessSlots]),
        by simpa only [witnessValues] using h.1.state.saved.saved 52 (by simp [witnessSlots])⟩
  exact kernel.seq (compare.seq (choice.seq (RelCT.block_nil (fun _ _ _ => trivial))))

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/CTDraw.lean`, which only this module imported.
section

/-! A public witness prefix determines native range and primality branches. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Ffdh.Arm.KeySearch
open VG.Proof.MillerRabin.Arm (RoundImpl)
open VG.Proof.Rsa.Mont (numAt)

def DrawMore (p : DrawPoint) (s : State) : Prop := DrawStart p s ∧ p.passed < p.params.checks

private structure RangeEnd (p : DrawPoint) (s : State) : Prop where
  state : WitnessState p.params (p.used + (p.params.bits + 7) / 8) p.passed s
  more : p.passed < p.params.checks
  ready : ArithmeticReady p.params.base p.params.capacity p.params.words s
  input : numAt s.mem (State.addr p.params.base) p.params.words 1 = witnessValue p.params p.used
  flag : (s.gpr .r11).toNat = if decide (1 < witnessValue p.params p.used ∧ witnessValue p.params p.used < p.params.modulus - 1) then 1 else 0

private theorem rangeEnd_ok (p : DrawPoint) (s : State) (h : DrawMore p s) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.drawRange s (RangeEnd p) := by
  refine WP.mono (drawRange_ok h.1.1 h.1.2) ?_
  rintro t ⟨state, ready, flag, input, _, _⟩
  refine ⟨state, h.2, ready, input, ?_⟩
  rw [flag]
  by_cases valid : 1 < witnessValue p.params p.used ∧ witnessValue p.params p.used < p.params.modulus - 1
  · simp only [ite_eq_left valid, decide_eq_true valid, ite_true]; rfl
  · simp only [ite_eq_right valid, decide_eq_false valid, Bool.false_eq_true, ite_false]; rfl

private structure DrawCompared (p : DrawPoint) (s : State) : Prop where
  state : WitnessState p.params (p.used + (p.params.bits + 7) / 8) p.passed s
  more : p.passed < p.params.checks
  ready : ArithmeticReady p.params.base p.params.capacity p.params.words s
  input : numAt s.mem (State.addr p.params.base) p.params.words 1 = witnessValue p.params p.used
  zero : s.z = !(decide (1 < witnessValue p.params p.used ∧ witnessValue p.params p.used < p.params.modulus - 1))

private theorem drawCompared_ok (p : DrawPoint) (s : State) (h : RangeEnd p s) :
    WP isa (.block [.cmp .r11 (.imm 0)]) s (DrawCompared p) := by
  refine WP.mono (cmpWord_ok .r11 h.flag) ?_
  rintro t ⟨⟨zero, mem⟩, rest⟩
  exact ⟨h.state.after_memory mem rest, h.more,
    h.ready.of_mem mem rest ((rest.gpr .r0 (by simp)).trans h.ready.ptr), by rw [mem]; exact h.input, zero⟩

theorem draw_ct (b : VG.Proof.Bignum.Arm.MontBackend) (v : RoundImpl) : RelCT isa (Two DrawMore)
    (VG.Impl.Ffdh.Arm.ParameterCandidate.draw (VG.Impl.Bignum.Arm.MontCall.op b.name b.mul) v.name v.code) (fun _ _ => True) := by
  have range : RelCT isa (Two DrawMore) VG.Impl.Ffdh.Arm.ParameterCandidate.drawRange (Two RangeEnd) :=
    two_post (drawRange_ct.mono (fun _ _ h => two_mono (fun _ _ h => h.1) h) (fun _ _ h => h)) rangeEnd_ok
  have compare : RelCT isa (Two RangeEnd) (.block [.cmp .r11 (.imm 0)]) (Two DrawCompared) :=
    two_post ((stackOnly_ct _ rfl).mono (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ _ => trivial)) drawCompared_ok
  have choice : RelCT isa (Two DrawCompared)
      (.ite .eq (.block [.mov .r3 (.imm 4), .cmp .r3 (.imm 4)])
        (VG.Impl.Ffdh.Arm.ParameterCandidate.round (VG.Impl.Bignum.Arm.MontCall.op b.name b.mul) v.name v.code)) (fun _ _ => True) := by
    refine two_ite (fun _ _ _ left right => ?_) ?_ ?_
    · change some _ = some _
      rw [left.zero, right.zero]
    · exact (stackOnly_ct _ rfl).mono (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ _ => trivial)
    · exact two_map (fun p => (⟨p.params, p.used + (p.params.bits + 7) / 8, p.passed, witnessValue p.params p.used⟩ : RoundPoint))
        (fun _ _ h => ⟨h.1.state, h.1.more, h.1.ready, h.1.input⟩) (round_ct b v)
  exact range.seq (compare.seq (choice.seq (RelCT.block_nil (fun _ _ _ => trivial))))

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/CTWitnessStep.lean`, which only this module imported.
section

/-! A witness iteration branches on public entropy availability. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Ffdh.Arm.KeySearch
open VG.Proof.MillerRabin.Arm (RoundImpl)

def WitnessLoopStart (p : DrawPoint) (s : State) : Prop :=
  WitnessState p.params p.used p.passed s ∧ p.passed < p.params.checks

private structure WitnessRoomEnd (p : DrawPoint) (s : State) : Prop where
  state : WitnessState p.params p.used p.passed s
  more : p.passed < p.params.checks
  zero : s.z = decide (p.params.bytes.length - p.used < (p.params.bits + 7) / 8)

private theorem witnessRoomEnd_ok (p : DrawPoint) (s : State) (h : WitnessLoopStart p s) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.witnessRoom) s (WitnessRoomEnd p) := by
  have lengthWord : s.mem.readW (State.addr (s.sp + 20#32)) 32 = BitVec.ofNat 32 p.params.bytes.length := by
    simpa only [witnessValues] using h.1.saved.saved 20 (by simp [witnessSlots])
  have usedWord : s.mem.readW (State.addr (s.sp + 40#32)) 32 = BitVec.ofNat 32 p.used := by
    simpa only [witnessValues] using h.1.saved.saved 40 (by simp [witnessSlots])
  have widthWord : s.mem.readW (State.addr (s.sp + 48#32)) 32 = BitVec.ofNat 32 ((p.params.bits + 7) / 8) := by
    simpa only [witnessValues] using h.1.saved.saved 48 (by simp [witnessSlots])
  refine WP.mono (witnessRoom_ok h.1.saved.space h.1.tapeCount
    (by have := h.1.bitsBound; omega) h.1.usedBound lengthWord usedWord widthWord) ?_
  rintro t ⟨⟨zero, mem⟩, rest⟩
  exact ⟨h.1.after_memory mem rest, h.2, zero⟩

theorem witnessStep_ct (b : VG.Proof.Bignum.Arm.MontBackend) (v : RoundImpl) : RelCT isa (Two WitnessLoopStart)
    (VG.Impl.Ffdh.Arm.ParameterCandidate.witnessStep (VG.Impl.Bignum.Arm.MontCall.op b.name b.mul) v.name v.code) (fun _ _ => True) := by
  have room : RelCT isa (Two WitnessLoopStart)
      (.block VG.Impl.Ffdh.Arm.ParameterCandidate.witnessRoom) (Two WitnessRoomEnd) :=
    two_post (witnessRoom_ct.mono (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ _ => trivial)) witnessRoomEnd_ok
  have choice : RelCT isa (Two WitnessRoomEnd)
      (.ite .eq (.block [.mov .r3 (.imm 0), .cmp .r3 (.imm 4)])
        (VG.Impl.Ffdh.Arm.ParameterCandidate.draw (VG.Impl.Bignum.Arm.MontCall.op b.name b.mul) v.name v.code)) (fun _ _ => True) := by
    refine two_ite (fun _ _ _ left right => ?_) ?_ ?_
    · change some _ = some _
      rw [left.zero, right.zero]
    · exact (stackOnly_ct _ rfl).mono (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ _ => trivial)
    · refine two_map id ?_ (draw_ct b v)
      intro p s h
      have enough : p.used + (p.params.bits + 7) / 8 ≤ p.params.bytes.length := by
        have notShort : ¬ p.params.bytes.length - p.used < (p.params.bits + 7) / 8 := by
          have go := h.2
          change some s.z = some false at go
          rw [h.1.zero] at go
          exact of_decide_eq_false (Option.some.inj go)
        have := h.1.state.usedBound
        omega
      exact ⟨⟨h.1.state, enough⟩, h.1.more⟩
  exact room.seq (choice.seq (RelCT.block_nil (fun _ _ _ => trivial)))

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/CTWitnessLoop.lean`, which only this module imported.
section

/-! The native witness loop follows public tape consumption and primality results. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Two)
open VG.Proof.MillerRabin.Arm (RoundImpl)

private def nextWitness (p : DrawPoint) : DrawPoint :=
  ⟨p.params, witnessNextUsed p.params p.used, witnessNextPassed p.params p.used p.passed⟩

private structure WitnessIterEnd (p : DrawPoint) (s : State) : Prop where
  state : WitnessState p.params (witnessNextUsed p.params p.used) (witnessNextPassed p.params p.used p.passed) s
  zero : s.z = decide (witnessNextStatus p.params p.used p.passed = 4)

private theorem witnessIterEnd_ok (b : VG.Proof.Bignum.Arm.MontBackend) (v : RoundImpl) (p : DrawPoint) (s : State) (h : WitnessLoopStart p s) :
    WP isa (VG.Impl.Ffdh.Arm.ParameterCandidate.witnessStep (VG.Impl.Bignum.Arm.MontCall.op b.name b.mul) v.name v.code) s (WitnessIterEnd p) := by
  refine WP.mono (witnessStep_ok b v h.1 h.2) ?_
  rintro t ⟨state, _, zero, _, _⟩
  exact ⟨state, zero⟩

private theorem witnessStep_fixed (b : VG.Proof.Bignum.Arm.MontBackend) (v : RoundImpl) (p : DrawPoint) :
    RelCT isa (fun s t => WitnessLoopStart p s ∧ WitnessLoopStart p t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.ParameterCandidate.witnessStep (VG.Impl.Bignum.Arm.MontCall.op b.name b.mul) v.name v.code)
      (fun s t => WitnessIterEnd p s ∧ WitnessIterEnd p t ∧ s.sp = t.sp) := by
  intro s t trS trT u z h runS runT
  have leak := ((witnessStep_ct b v) _ _ _ _ _ _ ⟨p, h⟩ runS runT).1
  obtain ⟨_, _, execS, postS⟩ := witnessIterEnd_ok b v p s h.1
  obtain ⟨_, _, execT, postT⟩ := witnessIterEnd_ok b v p t h.2.1
  obtain ⟨_, rfl⟩ := Exec.det runS execS
  obtain ⟨_, rfl⟩ := Exec.det runT execT
  exact ⟨leak, postS, postT, (Exec.rdwr runS).2.2.trans (h.2.2.trans (Exec.rdwr runT).2.2.symm)⟩

private def WitnessLoopPair (remaining : Nat) (s t : State) : Prop :=
  ∃ p : DrawPoint, p.params.bytes.length - p.used + 1 = remaining ∧
    WitnessLoopStart p s ∧ WitnessLoopStart p t ∧ s.sp = t.sp

private theorem witnessContinue {p : DrawPoint} {s u : State} (h : WitnessLoopStart p s)
    (post : WitnessIterEnd p u) (go : isa.eval .eq u = some true) :
    WitnessLoopStart (nextWitness p) u ∧
      p.params.bytes.length - (nextWitness p).used + 1 < p.params.bytes.length - p.used + 1 := by
  have again : witnessNextStatus p.params p.used p.passed = 4 := by
    change some u.z = some true at go
    rw [post.zero] at go
    exact of_decide_eq_true (Option.some.inj go)
  have enough : p.used + (p.params.bits + 7) / 8 ≤ p.params.bytes.length := by
    by_contra short
    simp only [witnessNextStatus, ite_eq_right short] at again
    contradiction
  have drawAgain : drawStatus p.params p.passed p.used = 4 := by
    simpa only [witnessNextStatus, ite_eq_left enough] using again
  have nextMore : witnessNextPassed p.params p.used p.passed < p.params.checks := by
    rw [witnessNextPassed, ite_eq_left enough]
    exact draw_continue h.2 drawAgain
  refine ⟨⟨post.state, nextMore⟩, ?_⟩
  change p.params.bytes.length - witnessNextUsed p.params p.used + 1 < _
  rw [witnessNextUsed, ite_eq_left enough]
  have := h.1.bitsPositive
  omega

theorem millerRabin_ct (b : VG.Proof.Bignum.Arm.MontBackend) (v : RoundImpl) : RelCT isa (Two WitnessLoopStart)
    (VG.Impl.Ffdh.Arm.ParameterCandidate.millerRabin (VG.Impl.Bignum.Arm.MontCall.op b.name b.mul) v.name v.code) (fun _ _ => True) := by
  have step : ∀ n, RelCT isa (WitnessLoopPair n)
      (VG.Impl.Ffdh.Arm.ParameterCandidate.witnessStep (VG.Impl.Bignum.Arm.MontCall.op b.name b.mul) v.name v.code)
      (fun u z => isa.eval .eq u = isa.eval .eq z ∧
        (isa.eval .eq u = some false → True) ∧
        (isa.eval .eq u = some true → ∃ m, m < n ∧ WitnessLoopPair m u z)) := by
    intro n s t trS trT u z h runS runT
    obtain ⟨p, remaining, left, right, sp⟩ := h
    obtain ⟨leak, postU, postZ, spUZ⟩ := witnessStep_fixed b v p _ _ _ _ _ _ ⟨left, right, sp⟩ runS runT
    refine ⟨leak, ?_, by intro _; trivial, ?_⟩
    · change some u.z = some z.z
      rw [postU.zero, postZ.zero]
    · intro go
      have goZ : isa.eval .eq z = some true := by
        change some z.z = some true
        change some u.z = some true at go
        rw [postZ.zero, ← postU.zero]
        exact go
      have nextU := witnessContinue left postU go
      have nextZ := witnessContinue right postZ goZ
      exact ⟨p.params.bytes.length - (nextWitness p).used + 1,
        by rw [← remaining]; exact nextU.2, nextWitness p, rfl, nextU.1, nextZ.1, spUZ⟩
  intro s t trS trT u z h runS runT
  obtain ⟨p, left, right, sp⟩ := h
  exact RelCT.loop WitnessLoopPair step (p.params.bytes.length - p.used + 1)
    _ _ _ _ _ _ ⟨p, rfl, left, right, sp⟩ runS runT

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/MontInputMemory.lean`, which only this module imported.
section

/-! Read-only native argument loads retain the existing Montgomery preparation contract. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Ffdh.Arm VG.Proof.X25519.Arm

theorem MontPrepInput.after_memory {s t : State} {base src : BitVec 32} {capacity k : Nat} {rs : List Reg}
    (h : MontPrepInput base src capacity k s) (memory : t.mem = s.mem) (rest : Rest rs s t) :
    MontPrepInput base src capacity k t := by
  refine ⟨h.workspace.congr rest.wr, ?_, h.minLength, h.maxLength, h.space, h.sourceFits,
    by rw [rest.rd, rest.wr]; exact h.readable, h.separate,
    by rw [memory]; exact h.large, by rw [memory]; exact h.odd, by rw [memory]; exact h.normalized,
    h.calls.of_rest rest⟩
  have frame : Frame [⟨State.addr base, 8 * capacity⟩] s.mem t.mem := by rw [memory]; exact Frame.refl _ _
  simpa only [memory, rest.sp] using h.stack.after_workspace frame rest

theorem MontPrepInput.prepare_input {s : State} {base src : BitVec 32} {capacity k : Nat}
    (h : MontPrepInput base src capacity k s) (ptr : s.gpr .r0 = base) (count : s.gpr .r6 = BitVec.ofNat 32 k) :
    PrepareInput base src capacity k s :=
  ⟨h.workspace, h.stack, ptr, count, h.minLength, h.maxLength, h.space, h.sourceFits, h.readable, h.separate, h.large, h.odd⟩

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/CTMontInput.lean`, which only this module imported.
section

/-! Parameter candidates reuse RSA's public-trace modulus import and precomputation. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Ffdh.Arm VG.Proof.X25519.Arm VG.Proof.Mont
open VG.Proof.Ffdh.Arm.KeySearch (Two two_post)

structure MontInputData where
  base : BitVec 32
  src : BitVec 32
  capacity : Nat
  k : Nat

def MontStart (p : MontInputData) (s : State) : Prop := MontPrepInput p.base p.src p.capacity p.k s
def PreparedInput (p : MontInputData) (s : State) : Prop := CandidatePrepareInput p.base p.src p.capacity p.k s

theorem prepareHeader_ok (p : MontInputData) (s : State) (h : MontStart p s) :
    WP isa (.block [.ldrSp .r0 0, .ldrSp .r6 12]) s fun t =>
      PreparedInput p t ∧ CallStack p.base p.capacity t := by
  have read0 : InRegions (s.rd ++ s.wr) (State.addr s.sp) 4 := by
    simpa only [off, BitVec.add_zero] using h.stack.read (d := 0) (by decide)
  have addr12 : State.addr (s.sp + 12#32) = off (State.addr s.sp) 12 := VG.Arm.addr_add (by have := h.stack.nowrap; omega)
  refine wp_loadStack (a := State.addr s.sp) (by decide) (by simp only [BitVec.add_zero]) read0 fun u first => ?_
  refine wp_loadStack (a := off (State.addr s.sp) 12) (by decide)
    (by rw [first.sp]; exact addr12) (by rw [first.rd, first.wr]; exact h.stack.read (by decide)) fun t second => WP.block_nil ?_
  have memory : t.mem = s.mem := second.mem.trans first.mem
  have rest : Rest [.r0, .r6] s t := (first.rest (by simp)).trans (second.rest (by simp))
  refine ⟨⟨(h.after_memory memory rest).prepare_input
    ((second.other .r0 (by decide)).trans (first.gpr.trans h.stack.savedBase))
    (by rw [second.gpr, first.mem]; exact h.stack.savedCount), ?_⟩, h.calls.of_rest rest⟩
  rw [memory];exact h.normalized

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/CTMontPrepare.lean`, which only this module imported.
section

/-! Complete native Montgomery preparation reuses RSA's constant-time math and array view. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Ffdh.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (numAt)
open VG.Proof.Ffdh.Arm.KeySearch (Two two_post two_map)

def montMath (p : MontInputData) : MontMathData := ⟨p.base, p.capacity, Spec.Rsa.modulusWords p.k⟩

def MontFullStart (p : MontInputData) (s : State) : Prop := MontStart p s ∧ Spec.Rsa.scratchWords p.k ≤ p.capacity

private def MontHeaderStart (p : MontInputData) (s : State) : Prop := (PreparedInput p s ∧
  CallStack p.base p.capacity s) ∧ Spec.Rsa.scratchWords p.k ≤ p.capacity

private def MontLayoutState (p : MontInputData) (s : State) : Prop := MontR2 (montMath p) s ∧
  64 ≤ p.k ∧ p.k ≤ 1024 ∧ Spec.Rsa.scratchWords p.k ≤ p.capacity

private def MontKeyState (p : MontInputData) (s : State) : Prop := MontKeyStart (montMath p) s

theorem montPrep_ct (b : MontBackend) : RelCT isa (Two MontFullStart)
    (VG.Impl.Ffdh.Arm.ParameterCandidate.montPrep (VG.Impl.Bignum.Arm.MontCall.op b.name b.mul))
      (fun _ _ => True) := by
  have head : RelCT isa (Two MontFullStart) (.block [.ldrSp .r0 0, .ldrSp .r6 12]) (Two MontHeaderStart) :=
    two_post ((stackOnly_ct _ rfl).mono (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ _ => trivial)) (fun p s h =>
      WP.mono (prepareHeader_ok p s h.1) (fun _ result => ⟨result, h.2⟩))
  have prepareTrace : RelCT isa (Two MontHeaderStart)
      (VG.Impl.Ffdh.Arm.CandidatePrepare.code (VG.Impl.Bignum.Arm.MontCall.op b.name b.mul))
      (fun _ _ => True) := by
    intro s t trS trT u v h runS runT
    obtain ⟨p, left, right, sp⟩ := h
    let correct := fun o a c ho ha hc v input => b.correct v (base := p.base) (len := p.capacity)
      (w := Spec.Rsa.modulusWords p.k) (o := o) (a := a) (b := c) input ho ha hc
    let K := TwoExp.sharedMontgomery p.base s.sp p.capacity (Spec.Rsa.modulusWords p.k) b.name b.mul
      correct b.stackOk
    have timing : TwoExp.MontgomeryTiming K :=
      TwoExp.sharedMontgomeryTiming p.base s.sp p.capacity (Spec.Rsa.modulusWords p.k) b.name b.mul
        correct b.stackOk (fun _ _ _ ho ha hc => b.rawCT ho ha hc)
    exact candidatePrepare_ct K timing _ _ _ _ _ _
      ⟨⟨left.1.1, left.1.2, rfl⟩, ⟨right.1.1, right.1.2, sp.symm⟩, sp⟩ runS runT
  have prepare : RelCT isa (Two MontHeaderStart)
      (VG.Impl.Ffdh.Arm.CandidatePrepare.code (VG.Impl.Bignum.Arm.MontCall.op b.name b.mul))
      (Two MontLayoutState) :=
    two_post prepareTrace (fun p s h => by
      let K := TwoExp.sharedMontgomery p.base s.sp p.capacity (Spec.Rsa.modulusWords p.k) b.name b.mul
        (fun _ _ _ ho ha hc v input => b.correct v input ho ha hc) b.stackOk
      refine WP.mono (candidatePrepare_ok s K h.1.1.1 ⟨h.1.2, rfl⟩ h.1.1.2) ?_
      rintro t ⟨ready, number, r2, calls, _, _⟩
      refine ⟨⟨ready, ?_, calls.1⟩, h.1.1.1.minLength, h.1.1.1.maxLength, h.2⟩
      change numAt t.mem (State.addr p.base) (Spec.Rsa.modulusWords p.k) 4 < numAt t.mem (State.addr p.base) (Spec.Rsa.modulusWords p.k) 0
      rw [r2, number]
      exact Nat.mod_lt _ (by have := h.1.1.1.large; omega))
  have oneTrace : RelCT isa (Two MontLayoutState)
      (.seq (VG.Impl.Bignum.Arm.smallConst 1 1) (VG.Impl.Bignum.Arm.MontCall.op b.name b.mul 1 1 4))
        (fun _ _ => True) :=
    two_map montMath (fun _ _ h => h.1) (montOne_ct b)
  have one : RelCT isa (Two MontLayoutState)
      (.seq (VG.Impl.Bignum.Arm.smallConst 1 1) (VG.Impl.Bignum.Arm.MontCall.op b.name b.mul 1 1 4))
        (Two MontKeyState) :=
    two_post oneTrace (fun p s h => by
      refine WP.mono (montOne_ready b (montMath p) s h.1) ?_
      intro t ready
      exact ⟨ready.workspace, MontData.of_ready ready, ⟨p.k, rfl, h.2⟩, ready.stackRead, ready.saved⟩)
  have key := two_map montMath (fun _ _ h => h) montKeySetup_ct
  exact head.seq (prepare.seq (one.seq (key.seq (RelCT.block_nil (fun _ _ h => h)))))

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/CTExponentSigma.lean`, which only this module imported.
section

/-! The compact-round shift depends only on the public decomposition count. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Ffdh.Arm.KeySearch

structure SigmaStart (count : Nat) (s : State) : Prop where
  stack : Workspace s s.sp 72
  saved : s.mem.readW (State.addr (s.sp + 60#32)) 32 = BitVec.ofNat 32 count

private def SigmaHead (count : Nat) (s : State) : Prop := s.z = decide (count % 4 = 0)

private theorem sigmaHead_ct : RelCT isa (Two SigmaStart)
    (.block VG.Impl.Ffdh.Arm.ParameterCandidate.exponentSigmaHead) (Two SigmaHead) := by
  refine two_post ((stackOnly_ct _ rfl).mono (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ _ => trivial)) ?_
  intro count s h
  exact WP.mono (sigmaHead_ok h.stack h.saved) (fun _ post => post.1.2.1)

theorem exponentSigma_ct : RelCT isa (Two SigmaStart)
    VG.Impl.Ffdh.Arm.ParameterCandidate.exponentSigma (fun s t => s.sp = t.sp) := by
  have choice : RelCT isa (Two SigmaHead)
      (.ite .eq (.block [.mov .r1 (.imm 4)]) (.block [])) (fun s t => s.sp = t.sp) := by
    refine two_ite (fun _ _ _ left right => ?_) ?_ ?_
    · change some _ = some _
      rw [left, right]
    · exact (stackOnly_ct _ rfl).mono (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ h => h)
    · exact RelCT.block_nil (fun _ _ ⟨_, _, _, sp⟩ => sp)
  exact sigmaHead_ct.seq (choice.seq ((save_ct .r1 64).seq (RelCT.block_nil (fun _ _ h => h))))

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/CTExponentPrepare.lean`, which only this module imported.
section

/-! Carry public decomposition metadata into the bounded exponent shift. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Arm.Keys (num)
open VG.Proof.Ffdh.Arm.KeySearch

structure DecomposeDone (p : DecomposeData) (s : State) : Prop where
  start : DecomposeStart p s
  saved : s.mem.readW (State.addr (s.sp + 60#32)) 32 = BitVec.ofNat 32 (Spec.Rsa.splitTwos (p.modulus - 1)).1

private theorem decomposeDone_ok (p : DecomposeData) (s : State) (h : DecomposeStart p s) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.expDecompose s (DecomposeDone p) := by
  refine WP.mono (expDecompose_ok h.workspace h.ready h.data h.stack h.separate h.number h.large h.odd) ?_
  rintro t ⟨ready, data, _, saved, arrays, _, _, rest⟩
  exact ⟨⟨h.workspace.congr rest.wr, ready, data, by rw [rest.sp]; exact h.stack.congr rest.wr,
    by rw [rest.sp]; exact h.separate, (arrays 0 (by decide) (by decide)).trans h.number, h.large, h.odd⟩, saved⟩

theorem decomposeDone_ct : RelCT isa (Two DecomposeStart)
    VG.Impl.Ffdh.Arm.ParameterCandidate.expDecompose (Two DecomposeDone) :=
  two_post expDecompose_ct decomposeDone_ok

private theorem sigmaReady_ok (p : DecomposeData) (s : State) (h : DecomposeDone p s) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.exponentSigma s
      (ExponentCountState ⟨p.math, countShift (Spec.Rsa.splitTwos (p.modulus - 1)).1⟩) := by
  refine WP.mono (exponentSigma_ok h.start.stack h.saved) ?_
  rintro t ⟨mem, rest⟩
  have eqWork : WorkspaceEq (State.addr p.math.base) (8 * p.math.capacity) s.mem t.mem := by
    rw [mem]
    exact stackWrite_workspaceEq h.start.workspace h.start.stack h.start.separate (by decide) _
  exact ⟨h.start.workspace.congr rest.wr,
    h.start.ready.rest rest (by decide) (by decide) (by decide), h.start.data.after_workspaceEq eqWork,
    by rw [rest.sp]; exact h.start.stack.congr rest.wr,
    by rw [rest.sp]; exact h.start.separate,
    (countShift_bounds _).1, (countShift_bounds _).2, by rw [rest.sp, mem, Mem.readW_writeW_self32]⟩

theorem sigmaReady_ct : RelCT isa (Two DecomposeDone)
    VG.Impl.Ffdh.Arm.ParameterCandidate.exponentSigma (Two ExponentCountState) := by
  have trace : RelCT isa (Two DecomposeDone)
      VG.Impl.Ffdh.Arm.ParameterCandidate.exponentSigma (fun _ _ => True) :=
    (two_map (fun p => (Spec.Rsa.splitTwos (p.modulus - 1)).1)
      (fun _ _ h => ⟨h.start.stack, h.saved⟩) exponentSigma_ct).mono
      (fun _ _ h => h) (fun _ _ _ => trivial)
  exact (two_post trace sigmaReady_ok).mono (fun _ _ h => h)
    (fun _ _ ⟨p, left, right, sp⟩ => ⟨⟨p.math, countShift (Spec.Rsa.splitTwos (p.modulus - 1)).1⟩, left, right, sp⟩)

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/CTExponentSetup.lean`, which only this module imported.
section

/-! The entire native compact Miller–Rabin exponent setup has a public trace. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Two)

theorem expSetup_ct : RelCT isa (Two DecomposeStart)
    VG.Impl.Ffdh.Arm.ParameterCandidate.expSetup (fun _ _ => True) :=
  decomposeDone_ct.seq (sigmaReady_ct.seq
    (exponentCopy_ct.seq (exponentHalfLoop_key_ct.seq exponentPower_ct)))

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/CTPhasePrepared.lean`, which only this module imported.
section

/-! Complete Montgomery and compact-round preparation for a public candidate. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Ffdh.Arm.KeySearch

structure PreparationData where
  input : MontInputData
  modulus : Nat

structure PreparationStart (p : PreparationData) (s : State) : Prop where
  input : MontFullStart p.input s
  stack : Workspace s s.sp 72
  separate : (⟨State.addr s.sp, 72⟩ : Region).Disjoint ⟨State.addr p.input.base, 8 * p.input.capacity⟩
  modulus : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr p.input.src) p.input.k) = p.modulus

private theorem montDecompose_ok (b : MontBackend) (p : PreparationData) (s : State) (h : PreparationStart p s) :
    WP isa (VG.Impl.Ffdh.Arm.ParameterCandidate.montPrep (VG.Impl.Bignum.Arm.MontCall.op b.name b.mul)) s (DecomposeStart ⟨montMath p.input, p.modulus⟩) := by
  refine WP.mono (montPrep_ok b h.input.1 h.input.2) ?_
  rintro t ⟨ready, data, full, _, _, _, _, _, _, rest⟩
  rw [h.modulus] at full
  exact ⟨h.input.1.workspace.congr rest.wr, ready, data,
    by rw [rest.sp]; exact h.stack.congr rest.wr,
    by rw [rest.sp]; exact h.separate, full,
    h.modulus ▸ h.input.1.large, h.modulus ▸ h.input.1.odd⟩

theorem phasePrepared_ct (b : MontBackend) : RelCT isa (Two PreparationStart)
    (VG.Impl.Ffdh.Arm.ParameterCandidate.phasePrepared (VG.Impl.Bignum.Arm.MontCall.op b.name b.mul)) (fun _ _ => True) := by
  have trace : RelCT isa (Two PreparationStart) (VG.Impl.Ffdh.Arm.ParameterCandidate.montPrep (VG.Impl.Bignum.Arm.MontCall.op b.name b.mul)) (fun _ _ => True) :=
    two_map PreparationData.input (fun _ _ h => h.input) (montPrep_ct b)
  exact (two_post trace (montDecompose_ok b)).seq
    (expSetup_ct.mono
      (fun _ _ ⟨p, left, right, sp⟩ => ⟨⟨montMath p.input, p.modulus⟩, left, right, sp⟩)
      (fun _ _ h => h))

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm
open VG.Proof.Ffdh.Arm.KeySearch
open VG.Proof.MillerRabin.Arm (RoundImpl)

structure PhasePoint where
  params : WitnessParams
  source : BitVec 32
  length : Nat
  used : Nat

def PhaseStart (p : PhasePoint) (s : State) : Prop := PhaseInput p.params p.source p.length p.used s

private def preparationData (p : PhasePoint) : PreparationData :=
  ⟨⟨p.params.base, p.source, p.params.capacity, p.length⟩, p.params.modulus⟩

private theorem phasePreparation_start (p : PhasePoint) (s : State) (h : PhaseStart p s) :
    PreparationStart (preparationData p) s :=
  ⟨⟨h.preparation, h.space⟩, h.saved.space, h.stackScratch, h.modulus⟩

theorem phaseRun_ct (b : VG.Proof.Bignum.Arm.MontBackend) (v : RoundImpl) : RelCT isa (Two PhaseStart)
    (VG.Impl.Ffdh.Arm.ParameterCandidate.phaseRun (VG.Impl.Bignum.Arm.MontCall.op b.name b.mul) v.name v.code) (fun _ _ => True) := by
  have prepare : RelCT isa (Two PhaseStart) (VG.Impl.Ffdh.Arm.ParameterCandidate.phasePrepared (VG.Impl.Bignum.Arm.MontCall.op b.name b.mul))
      (Two WitnessLoopStart) := by
    have trace := two_map preparationData phasePreparation_start (phasePrepared_ct b)
    have post (p : PhasePoint) (s : State) (h : PhaseStart p s) :
        WP isa (VG.Impl.Ffdh.Arm.ParameterCandidate.phasePrepared (VG.Impl.Bignum.Arm.MontCall.op b.name b.mul)) s
          (WitnessLoopStart ⟨p.params, p.used, 0⟩) :=
      WP.mono (preparedWitness_ok b h) (fun _ result => ⟨result.1, h.checksPositive⟩)
    exact (two_post trace post).mono (fun _ _ h => h)
      (fun _ _ ⟨p, left, right, sp⟩ => ⟨⟨p.params, p.used, 0⟩, left, right, sp⟩)
  exact prepare.seq (millerRabin_ct b v)

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end

/-! The full q or p candidate test has a public trace. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm
open VG.Proof.Ffdh.Arm.KeySearch
open VG.Proof.MillerRabin.Arm (RoundImpl)

structure CandidatePoint where
  params : CandidateParams
  used : Nat

def CandidateTestStart (q : Bool) (p : CandidatePoint) (s : State) : Prop :=
  CandidateContext p.params p.used s ∧
  Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr p.params.out) p.params.length) = (candidatePhase p.params q).modulus ∧
  (candidatePhase p.params q).modulus % 2 = 1

private def candidatePhasePoint (q : Bool) (p : CandidatePoint) : PhasePoint :=
  ⟨candidatePhase p.params q, p.params.out, p.params.length, p.used⟩

private theorem candidatePhaseStart_ok (q : Bool) (p : CandidatePoint) (s : State) (h : CandidateTestStart q p s) :
    WP isa (.block (VG.Impl.Ffdh.Arm.ParameterCandidate.phaseHead q)) s (PhaseStart (candidatePhasePoint q p)) := by
  refine WP.mono (candidatePhaseHead_ok h.1 q) ?_
  rintro t ⟨context, saved, changed, _⟩
  have phaseFrame := candidate_header_frame (p := p.params) (q := q) h.1.saved.space.nowrap changed
  have bytes := h.1.phase_output phaseFrame
  exact candidatePhaseInput context saved (by rw [bytes]; exact h.2.1) h.2.2

theorem candidateTest_ct (b : VG.Proof.Bignum.Arm.MontBackend) (v : RoundImpl) (q : Bool) : RelCT isa (Two (CandidateTestStart q))
    (VG.Impl.Ffdh.Arm.ParameterCandidate.test q (VG.Impl.Bignum.Arm.MontCall.op b.name b.mul) v.name v.code) (fun _ _ => True) := by
  have head := two_post ((phaseHead_ct q).mono (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ _ => trivial))
    (candidatePhaseStart_ok q)
  exact head.seq ((phaseRun_ct b v).mono
    (fun _ _ ⟨p, left, right, sp⟩ => ⟨candidatePhasePoint q p, left, right, sp⟩) (fun _ _ h => h))

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end

/-! Final status dispatch is public; every selected return has a fixed buffer-address trace. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Two two_post two_ite two_mono)

def ResultState (p : ResultData × Nat) (s : State) : Prop :=
  ResultStart p.1 s ∧ p.2 ≤ 2 ∧ s.gpr .r3 = BitVec.ofNat 32 p.2

private def ResultCompared (compare : Nat) (p : ResultData × Nat) (s : State) : Prop :=
  ResultState p s ∧ s.z = decide (p.2 = compare)

private theorem resultCompare_ct (compare : Nat) (bound : compare ≤ 4) : RelCT isa (Two ResultState)
    (.block [.cmp .r3 (.imm (BitVec.ofNat 32 compare))]) (Two (ResultCompared compare)) :=
  two_post ((stackOnly_ct _ rfl).mono (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ _ => trivial)) (fun p s h => by
    refine WP.mono (cmpStatus_ok p.2 compare (by have := h.2.1; omega_using [this]) bound h.2.2) ?_
    rintro t ⟨⟨zero, memory⟩, rest⟩
    exact ⟨⟨h.1.after_memory memory rest, h.2.1, (rest.gpr .r3 (by simp)).trans h.2.2⟩, zero⟩)

private theorem resultTail_ct : RelCT isa (Two ResultState)
    (VG.Impl.Ffdh.Arm.ParameterCandidate.seqs [
      .block [.cmp .r3 (.imm 1)], .ite .eq VG.Impl.Ffdh.Arm.ParameterCandidate.finAccepted VG.Impl.Ffdh.Arm.ParameterCandidate.finRejected])
    (fun _ _ => True) := by
  have branch : RelCT isa (Two (ResultCompared 1))
      (.ite .eq VG.Impl.Ffdh.Arm.ParameterCandidate.finAccepted VG.Impl.Ffdh.Arm.ParameterCandidate.finRejected) (fun _ _ => True) := by
    refine two_ite (fun p s t a b => by change some s.z = some t.z; rw [a.2, b.2]) ?_ ?_
    · exact finAccepted_ct.mono
        (fun _ _ ⟨p, a, b, sp⟩ => ⟨p.1, a.1.1.1, b.1.1.1, sp⟩) (fun _ _ h => h)
    · exact finRejected_ct.mono
        (fun _ _ ⟨p, a, b, sp⟩ => ⟨p.1, a.1.1.1, b.1.1.1, sp⟩) (fun _ _ h => h)
  exact (resultCompare_ct 1 (by decide)).seq (branch.seq (RelCT.block_nil (fun _ _ h => h)))

theorem result_ct : RelCT isa (Two ResultState) VG.Impl.Ffdh.Arm.ParameterCandidate.result (fun _ _ => True) := by
  have branch : RelCT isa (Two (ResultCompared 0))
      (.ite .eq VG.Impl.Ffdh.Arm.ParameterCandidate.finNone (VG.Impl.Ffdh.Arm.ParameterCandidate.seqs [
        .block [.cmp .r3 (.imm 1)], .ite .eq VG.Impl.Ffdh.Arm.ParameterCandidate.finAccepted VG.Impl.Ffdh.Arm.ParameterCandidate.finRejected]))
      (fun _ _ => True) := by
    refine two_ite (fun p s t a b => by change some s.z = some t.z; rw [a.2, b.2]) ?_ ?_
    · exact finNone_ct.mono
        (fun _ _ ⟨p, a, b, sp⟩ => ⟨p.1, a.1.1.1, b.1.1.1, sp⟩) (fun _ _ h => h)
    · exact resultTail_ct.mono (fun _ _ h => two_mono (fun _ _ h => h.1.1) h) (fun _ _ h => h)
  exact (resultCompare_ct 0 (by decide)).seq (branch.seq (RelCT.block_nil (fun _ _ h => h)))

end VG.Proof.Ffdh.Arm.ParameterCandidate
