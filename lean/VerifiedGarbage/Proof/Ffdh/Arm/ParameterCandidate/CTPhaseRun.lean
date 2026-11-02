module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.PhaseInput
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTBase
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.WitnessState
public import VerifiedGarbage.Proof.MillerRabin.Arm.Backend

import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.PreparedWitness
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.DrawSample
import VerifiedGarbage.Proof.Ffdh.Arm.RangeCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.OnPass
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTPolicy
import VerifiedGarbage.Proof.Bignum.Arm.StackOnlyCT
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.RoundKernel
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.WitnessMemory
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.Status
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.DrawRange
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTStackBlocks
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.Room
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.WitnessStep
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.WitnessProgress
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.MontPrepare
import VerifiedGarbage.Proof.Ffdh.Arm.Prepare
import VerifiedGarbage.Proof.Ffdh.Arm.CandidatePrepareCT
import VerifiedGarbage.Proof.Bignum.Arm.Stack
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTMontOne
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTMontKey
import VerifiedGarbage.Proof.Ffdh.Arm.CandidatePrepare
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTCountLoop
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.ExponentSigma
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTExponentLoop
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.Decompose
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.KeyMemory
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTExponentCopy
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTExponentTail
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTWitnessMaskStore
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.WitnessMaskHead
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.WitnessMaskBits
import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
import VerifiedGarbage.Proof.Bignum.Arm.ImportOperand
import VerifiedGarbage.Proof.Bignum.Arm.ImportOperandCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.DrawHead
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.WitnessTape
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import Mathlib.Data.Nat.Basic
import Mathlib.Order.RelClasses
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.RoundData
import VerifiedGarbage.Proof.Bignum.Arm.MontEncode
import VerifiedGarbage.Proof.Bignum.Arm.MontOpCT
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTCountStep
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CountInit
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.KeyReady
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

private theorem encodeReady_ok (p : RoundKernelData) (s : State) (h : RoundKernelStart p s) :
    WP isa (VG.Impl.Bignum.Arm.montOp 5 1 4) s (RoundEncoded p) := by
  have operand (j : Nat) (member : j = 1 ∨ j = 5) : Operand j := by
    rcases member with rfl | rfl <;> simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  refine WP.mono (montEncode_ok s h.ready (operand 5 (by simp)) (operand 1 (by simp)) (by decide)
    h.data.modulus h.data.odd h.data.r2) ?_
  rintro t ⟨ready, _, encoded, keeps, frame, rest⟩
  have saved : t.mem.readW (State.addr (t.sp + 36#32)) 32 = BitVec.ofNat 32 p.math.capacity := by
    rw [rest.sp, frame.readW (r := ⟨State.addr (s.sp + 36#32), 4⟩) (Region.contains_self _ _) ?_ (by decide)]
    · exact h.saved
    · intro r hr
      rw [List.mem_singleton] at hr
      subst r
      rw [VG.Arm.addr_add (by have := h.stack.nowrap; omega)]
      exact h.stackSep.sub_left (Offset.sub_base _ (by decide : 36 + 4 ≤ 72))
  refine ⟨⟨ready, h.data.after_operand (by decide) (by decide) (by decide) keeps,
    by rw [rest.sp]; exact h.stack.congr rest.wr,
    by rw [rest.sp]; exact h.stackSep, saved,
    by rw [rest.sp]; exact h.below,
    by rw [rest.sp]; exact h.belowSep⟩, ?_⟩
  rw [encoded]
  exact Nat.mod_lt _ (by have := h.data.large; omega)

private theorem encodeReady_ct : RelCT isa (Two RoundKernelStart)
    (VG.Impl.Bignum.Arm.montOp 5 1 4) (Two RoundEncoded) := by
  refine two_post ?_ encodeReady_ok
  intro s t trS trT u v h runS runT
  obtain ⟨p, left, right, sp⟩ := h
  have op (j : Nat) (member : j = 1 ∨ j = 4 ∨ j = 5) : Operand j := by
    rcases member with rfl | rfl | rfl <;> simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have fit : arrAt p.math.words 3 + 32 ≤ 8 * p.math.capacity := by
    have fits : arrAt p.math.words 8 ≤ 8 * p.math.capacity := left.ready.width ▸ left.ready.layout.2.2.1
    simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits ⊢
    omega
  have boundL : numAt s.mem (State.addr p.math.base) p.math.words 4 < numAt s.mem (State.addr p.math.base) p.math.words 0 := by
    rw [left.data.r2, left.data.modulus]
    exact Nat.mod_lt _ (by have := left.data.large; omega)
  have boundR : numAt t.mem (State.addr p.math.base) p.math.words 4 < numAt t.mem (State.addr p.math.base) p.math.words 0 := by
    rw [right.data.r2, right.data.modulus]
    exact Nat.mod_lt _ (by have := right.data.large; omega)
  exact montOp_ct (op 5 (by simp)) (op 1 (by simp)) (op 4 (by simp)) fit
    _ _ _ _ _ _ ⟨⟨left.ready, boundL⟩, ⟨right.ready, boundR⟩, sp⟩ runS runT

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

theorem roundPrepared_ct : RelCT isa (Two RoundKernelStart)
    (.seq (VG.Impl.Bignum.Arm.montOp 5 1 4) (.block [.ldrSp .r0 0, .ldrSp .r1 36]))
    (Two SharedRoundStart) := by
  have args : RelCT isa (Two RoundEncoded) (.block [.ldrSp .r0 0, .ldrSp .r1 36]) (Two SharedRoundStart) :=
    (two_post ((stackOnly_ct _ rfl).mono (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ _ => trivial)) callReady_ok).mono
      (fun _ _ h => h) (fun _ _ ⟨p, left, right, sp⟩ => ⟨p.math, left, right, sp⟩)
  exact encodeReady_ct.seq args

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

theorem roundKernel_ct (v : RoundImpl) : RelCT isa (Two RoundKernelStart)
    (VG.Impl.Ffdh.Arm.ParameterCandidate.roundKernel v.name v.code) (fun _ _ => True) :=
  RelCT.assoc (roundPrepared_ct.seq ((sharedRoundCall_ct v).seq (RelCT.block_nil (fun _ _ _ => trivial))))

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

private theorem roundReturned_ok (v : RoundImpl) (p : RoundPoint) (s : State) (h : RoundStart p s) :
    WP isa (VG.Impl.Ffdh.Arm.ParameterCandidate.roundKernel v.name v.code) s (RoundReturned p) := by
  have saved : s.mem.readW (State.addr (s.sp + 36#32)) 32 = BitVec.ofNat 32 p.params.capacity := by
    simpa only [witnessValues] using h.state.saved.saved 36 (by simp [witnessSlots])
  refine WP.mono (roundKernel_ok v h.ready h.state.data h.state.saved.space h.state.stackScratch
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

theorem round_ct (v : RoundImpl) : RelCT isa (Two RoundStart)
    (VG.Impl.Ffdh.Arm.ParameterCandidate.round v.name v.code) (fun _ _ => True) := by
  have kernel : RelCT isa (Two RoundStart)
      (VG.Impl.Ffdh.Arm.ParameterCandidate.roundKernel v.name v.code) (Two RoundReturned) :=
    two_post (two_map roundKernelData roundStart_kernel (roundKernel_ct v)) (roundReturned_ok v)
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

theorem draw_ct (v : RoundImpl) : RelCT isa (Two DrawMore)
    (VG.Impl.Ffdh.Arm.ParameterCandidate.draw v.name v.code) (fun _ _ => True) := by
  have range : RelCT isa (Two DrawMore) VG.Impl.Ffdh.Arm.ParameterCandidate.drawRange (Two RangeEnd) :=
    two_post (drawRange_ct.mono (fun _ _ h => two_mono (fun _ _ h => h.1) h) (fun _ _ h => h)) rangeEnd_ok
  have compare : RelCT isa (Two RangeEnd) (.block [.cmp .r11 (.imm 0)]) (Two DrawCompared) :=
    two_post ((stackOnly_ct _ rfl).mono (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ _ => trivial)) drawCompared_ok
  have choice : RelCT isa (Two DrawCompared)
      (.ite .eq (.block [.mov .r3 (.imm 4), .cmp .r3 (.imm 4)])
        (VG.Impl.Ffdh.Arm.ParameterCandidate.round v.name v.code)) (fun _ _ => True) := by
    refine two_ite (fun _ _ _ left right => ?_) ?_ ?_
    · change some _ = some _
      rw [left.zero, right.zero]
    · exact (stackOnly_ct _ rfl).mono (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ _ => trivial)
    · exact two_map (fun p => (⟨p.params, p.used + (p.params.bits + 7) / 8, p.passed, witnessValue p.params p.used⟩ : RoundPoint))
        (fun _ _ h => ⟨h.1.state, h.1.more, h.1.ready, h.1.input⟩) (round_ct v)
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

theorem witnessStep_ct (v : RoundImpl) : RelCT isa (Two WitnessLoopStart)
    (VG.Impl.Ffdh.Arm.ParameterCandidate.witnessStep v.name v.code) (fun _ _ => True) := by
  have room : RelCT isa (Two WitnessLoopStart)
      (.block VG.Impl.Ffdh.Arm.ParameterCandidate.witnessRoom) (Two WitnessRoomEnd) :=
    two_post (witnessRoom_ct.mono (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ _ => trivial)) witnessRoomEnd_ok
  have choice : RelCT isa (Two WitnessRoomEnd)
      (.ite .eq (.block [.mov .r3 (.imm 0), .cmp .r3 (.imm 4)])
        (VG.Impl.Ffdh.Arm.ParameterCandidate.draw v.name v.code)) (fun _ _ => True) := by
    refine two_ite (fun _ _ _ left right => ?_) ?_ ?_
    · change some _ = some _
      rw [left.zero, right.zero]
    · exact (stackOnly_ct _ rfl).mono (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ _ => trivial)
    · refine two_map id ?_ (draw_ct v)
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

private theorem witnessIterEnd_ok (v : RoundImpl) (p : DrawPoint) (s : State) (h : WitnessLoopStart p s) :
    WP isa (VG.Impl.Ffdh.Arm.ParameterCandidate.witnessStep v.name v.code) s (WitnessIterEnd p) := by
  refine WP.mono (witnessStep_ok v h.1 h.2) ?_
  rintro t ⟨state, _, zero, _, _⟩
  exact ⟨state, zero⟩

private theorem witnessStep_fixed (v : RoundImpl) (p : DrawPoint) :
    RelCT isa (fun s t => WitnessLoopStart p s ∧ WitnessLoopStart p t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.ParameterCandidate.witnessStep v.name v.code)
      (fun s t => WitnessIterEnd p s ∧ WitnessIterEnd p t ∧ s.sp = t.sp) := by
  intro s t trS trT u z h runS runT
  have leak := ((witnessStep_ct v) _ _ _ _ _ _ ⟨p, h⟩ runS runT).1
  obtain ⟨_, _, execS, postS⟩ := witnessIterEnd_ok v p s h.1
  obtain ⟨_, _, execT, postT⟩ := witnessIterEnd_ok v p t h.2.1
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

theorem millerRabin_ct (v : RoundImpl) : RelCT isa (Two WitnessLoopStart)
    (VG.Impl.Ffdh.Arm.ParameterCandidate.millerRabin v.name v.code) (fun _ _ => True) := by
  have step : ∀ n, RelCT isa (WitnessLoopPair n)
      (VG.Impl.Ffdh.Arm.ParameterCandidate.witnessStep v.name v.code)
      (fun u z => isa.eval .eq u = isa.eval .eq z ∧
        (isa.eval .eq u = some false → True) ∧
        (isa.eval .eq u = some true → ∃ m, m < n ∧ WitnessLoopPair m u z)) := by
    intro n s t trS trT u z h runS runT
    obtain ⟨p, remaining, left, right, sp⟩ := h
    obtain ⟨leak, postU, postZ, spUZ⟩ := witnessStep_fixed v p _ _ _ _ _ _ ⟨left, right, sp⟩ runS runT
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
    by rw [memory]; exact h.large, by rw [memory]; exact h.odd, by rw [memory]; exact h.normalized⟩
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
    WP isa (.block [.ldrSp .r0 0, .ldrSp .r6 12]) s (PreparedInput p) := by
  have read0 : InRegions (s.rd ++ s.wr) (State.addr s.sp) 4 := by
    simpa only [off, BitVec.add_zero] using h.stack.read (d := 0) (by decide)
  have addr12 : State.addr (s.sp + 12#32) = off (State.addr s.sp) 12 := VG.Arm.addr_add (by have := h.stack.nowrap; omega)
  refine wp_loadStack (a := State.addr s.sp) (by decide) (by simp only [BitVec.add_zero]) read0 fun u first => ?_
  refine wp_loadStack (a := off (State.addr s.sp) 12) (by decide)
    (by rw [first.sp]; exact addr12) (by rw [first.rd, first.wr]; exact h.stack.read (by decide)) fun t second => WP.block_nil ?_
  have memory : t.mem = s.mem := second.mem.trans first.mem
  have rest : Rest [.r0, .r6] s t := (first.rest (by simp)).trans (second.rest (by simp))
  refine ⟨(h.after_memory memory rest).prepare_input
    ((second.other .r0 (by decide)).trans (first.gpr.trans h.stack.savedBase))
    (by rw [second.gpr, first.mem]; exact h.stack.savedCount), ?_⟩
  rw [memory];exact h.normalized

theorem montInput_ct : RelCT isa (Two MontStart)
    (.seq (.block [.ldrSp .r0 0, .ldrSp .r6 12]) VG.Impl.Ffdh.Arm.CandidatePrepare.code) (fun _ _ => True) := by
  have head : RelCT isa (Two MontStart) (.block [.ldrSp .r0 0, .ldrSp .r6 12]) (Two PreparedInput) :=
    two_post ((stackOnly_ct _ rfl).mono (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ _ => trivial)) prepareHeader_ok
  have prepare : RelCT isa (Two PreparedInput) VG.Impl.Ffdh.Arm.CandidatePrepare.code (fun _ _ => True) := by
    intro s t trS trT u v h runS runT
    obtain ⟨p, left, right, sp⟩ := h
    exact candidatePrepare_ct _ _ _ _ _ _ ⟨left,right,sp⟩ runS runT
  exact head.seq prepare

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

private def MontHeaderStart (p : MontInputData) (s : State) : Prop := PreparedInput p s ∧ Spec.Rsa.scratchWords p.k ≤ p.capacity

private def MontLayoutState (p : MontInputData) (s : State) : Prop := MontR2 (montMath p) s ∧
  64 ≤ p.k ∧ p.k ≤ 1024 ∧ Spec.Rsa.scratchWords p.k ≤ p.capacity

private def MontKeyState (p : MontInputData) (s : State) : Prop := MontKeyStart (montMath p) s

theorem montPrep_ct : RelCT isa (Two MontFullStart) VG.Impl.Ffdh.Arm.ParameterCandidate.montPrep (fun _ _ => True) := by
  have head : RelCT isa (Two MontFullStart) (.block [.ldrSp .r0 0, .ldrSp .r6 12]) (Two MontHeaderStart) :=
    two_post ((stackOnly_ct _ rfl).mono (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ _ => trivial)) (fun p s h =>
      WP.mono (prepareHeader_ok p s h.1) (fun _ result => ⟨result, h.2⟩))
  have prepareTrace : RelCT isa (Two MontHeaderStart) VG.Impl.Ffdh.Arm.CandidatePrepare.code (fun _ _ => True) := by
    intro s t trS trT u v h runS runT
    obtain ⟨p, left, right, sp⟩ := h
    exact candidatePrepare_ct _ _ _ _ _ _ ⟨left.1,right.1,sp⟩ runS runT
  have prepare : RelCT isa (Two MontHeaderStart) VG.Impl.Ffdh.Arm.CandidatePrepare.code (Two MontLayoutState) :=
    two_post prepareTrace (fun p s h => by
      refine WP.mono (candidatePrepare_ok s h.1.1 h.1.2) ?_
      rintro t ⟨ready, number, r2, _, _⟩
      refine ⟨⟨ready, ?_⟩, h.1.1.minLength, h.1.1.maxLength, h.2⟩
      change numAt t.mem (State.addr p.base) (Spec.Rsa.modulusWords p.k) 4 < numAt t.mem (State.addr p.base) (Spec.Rsa.modulusWords p.k) 0
      rw [r2, number]
      exact Nat.mod_lt _ (by have := h.1.1.large; omega))
  have oneTrace : RelCT isa (Two MontLayoutState)
      (.seq (VG.Impl.Bignum.Arm.smallConst 1 1) (VG.Impl.Bignum.Arm.montOp 1 1 4)) (fun _ _ => True) :=
    two_map montMath (fun _ _ h => h.1) montOne_ct
  have one : RelCT isa (Two MontLayoutState)
      (.seq (VG.Impl.Bignum.Arm.smallConst 1 1) (VG.Impl.Bignum.Arm.montOp 1 1 4)) (Two MontKeyState) :=
    two_post oneTrace (fun p s h => by
      refine WP.mono (montOne_ready (montMath p) s h.1) ?_
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

private theorem montDecompose_ok (p : PreparationData) (s : State) (h : PreparationStart p s) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.montPrep s (DecomposeStart ⟨montMath p.input, p.modulus⟩) := by
  refine WP.mono (montPrep_ok h.input.1 h.input.2) ?_
  rintro t ⟨ready, data, full, _, _, _, _, _, _, rest⟩
  rw [h.modulus] at full
  exact ⟨h.input.1.workspace.congr rest.wr, ready, data,
    by rw [rest.sp]; exact h.stack.congr rest.wr,
    by rw [rest.sp]; exact h.separate, full,
    h.modulus ▸ h.input.1.large, h.modulus ▸ h.input.1.odd⟩

theorem phasePrepared_ct : RelCT isa (Two PreparationStart)
    VG.Impl.Ffdh.Arm.ParameterCandidate.phasePrepared (fun _ _ => True) := by
  have trace : RelCT isa (Two PreparationStart) VG.Impl.Ffdh.Arm.ParameterCandidate.montPrep (fun _ _ => True) :=
    two_map PreparationData.input (fun _ _ h => h.input) montPrep_ct
  exact (two_post trace montDecompose_ok).seq
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

theorem phaseRun_ct (v : RoundImpl) : RelCT isa (Two PhaseStart)
    (VG.Impl.Ffdh.Arm.ParameterCandidate.phaseRun v.name v.code) (fun _ _ => True) := by
  have prepare : RelCT isa (Two PhaseStart) VG.Impl.Ffdh.Arm.ParameterCandidate.phasePrepared
      (Two WitnessLoopStart) := by
    have trace := two_map preparationData phasePreparation_start phasePrepared_ct
    have post (p : PhasePoint) (s : State) (h : PhaseStart p s) :
        WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.phasePrepared s
          (WitnessLoopStart ⟨p.params, p.used, 0⟩) :=
      WP.mono (preparedWitness_ok h) (fun _ result => ⟨result.1, h.checksPositive⟩)
    exact (two_post trace post).mono (fun _ _ h => h)
      (fun _ _ ⟨p, left, right, sp⟩ => ⟨⟨p.params, p.used, 0⟩, left, right, sp⟩)
  exact prepare.seq (millerRabin_ct v)

end VG.Proof.Ffdh.Arm.ParameterCandidate
