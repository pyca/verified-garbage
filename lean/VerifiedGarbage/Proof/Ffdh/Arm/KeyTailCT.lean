module

public import VerifiedGarbage.Impl.Ffdh.Arm.Domain
public import VerifiedGarbage.Proof.Ffdh.Arm.PowerAtCT
public import VerifiedGarbage.Impl.Ffdh.Arm.GenerateKey
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyOutputs
public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.TCB.Arm.Isa
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady

import VerifiedGarbage.Proof.Ffdh.Arm.KeyTail
import VerifiedGarbage.Proof.Ffdh.Arm.RangeCT
import VerifiedGarbage.Proof.Ffdh.Arm.Range
import VerifiedGarbage.Proof.Ffdh.Arm.KeyGeometry
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Ffdh.Arm.ExchangeMain
import VerifiedGarbage.Proof.Ffdh.Arm.PowerAt
import VerifiedGarbage.Proof.Ffdh.Arm.KeyMemory
import VerifiedGarbage.Proof.Ffdh.Arm.KeyArgsCT
import VerifiedGarbage.Proof.Ffdh.Arm.KeyByteCT
import VerifiedGarbage.Proof.Ffdh.Arm.BranchCT
import VerifiedGarbage.Proof.Bignum.Arm.MaskBytesCT
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Ffdh.Arm.KeyClear
import VerifiedGarbage.Proof.Ffdh.Arm.KeyMask
import VerifiedGarbage.Proof.Ffdh.Arm.ExportResult
import VerifiedGarbage.Proof.Ffdh.Arm.ExchangeFinishCT
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Ffdh.Arm.StackCT
import VerifiedGarbage.Proof.Ffdh.Arm.ExportResultCT
/-! Generated-public-value exponentiation, checking, export and masking have
the same trace for different secret scalars of the public significant width. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/KeyOutputsCT.lean`, which only this module imported.
section

/-! Clearing and masking complete key encodings never branches on their contents
or the saved secret result flag. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont

theorem keyMask_ct {p : Inputs} {slots : List Nat} (slot : Nat)
    (fit : slot + 4 ≤ 72) (hs : slot ∈ slots) (hk : 32 ∈ slots) :
    RelCT isa (fun s t => ArgumentMemory p slots s ∧ ArgumentMemory p slots t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.Domain.GenerateKey.maskOutput slot) (fun _ _ => True) := by
  let Q := fun s : State => s.gpr .r0 = p.slotValue slot ∧ s.gpr .lr = BitVec.ofNat 32 p.k
  have args := (keyMaskArgs_ct slot).mono
    (P' := fun (s t : State) => ArgumentMemory p slots s ∧ ArgumentMemory p slots t ∧ s.sp = t.sp)
    (fun _ _ h => h.2.2) (fun _ _ _ => trivial)
  have wp (s : State) (h : ArgumentMemory p slots s) : WP isa
      (.block [.ldrSp .r0 slot, .ldrSp .lr 32, .ldrSp .r3 64, .mov .r2 (.imm 0), .dp .sub .r2 .r2 (.reg .r3)]) s Q :=
    WP.mono (keyMaskArgs_ok s slot h fit hs hk rfl) (fun _ h => ⟨h.1.1, h.1.2.1⟩)
  have loop : RelCT isa (fun s t => Q s ∧ Q t ∧ s.sp = t.sp) VG.Impl.Bignum.Arm.maskBytes (fun _ _ => True) := by
    intro s t tr1 tr2 u v h e1 e2
    exact ⟨maskBytes_ct s t tr1 tr2 u v trivial trivial
      ⟨h.1.1.trans h.2.1.1.symm, h.1.2.trans h.2.1.2.symm⟩ e1 e2, trivial⟩
  unfold VG.Impl.Ffdh.Arm.Domain.GenerateKey.maskOutput
  exact relCT_chain args wp wp loop

theorem keyClear_ct {p : Inputs} {slots : List Nat} (slot : Nat)
    (fit : slot + 4 ≤ 72) (hs : slot ∈ slots) (hk : 32 ∈ slots) :
    RelCT isa (fun s t => ArgumentMemory p slots s ∧ ArgumentMemory p slots t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.Domain.GenerateKey.clearOutput slot) (fun _ _ => True) := by
  let Q := fun s : State => s.gpr .r0 = p.slotValue slot ∧ s.gpr .lr = BitVec.ofNat 32 p.k
  have args := (keyClearArgs_ct slot).mono
    (P' := fun (s t : State) => ArgumentMemory p slots s ∧ ArgumentMemory p slots t ∧ s.sp = t.sp)
    (fun _ _ h => h.2.2) (fun _ _ _ => trivial)
  have wp (s : State) (h : ArgumentMemory p slots s) :
      WP isa (.block [.ldrSp .r0 slot, .ldrSp .lr 32, .mov .r2 (.imm 0)]) s Q :=
    WP.mono (keyClearArgs_ok s slot h fit hs hk) (fun _ h => ⟨h.1.1, h.1.2.1⟩)
  have loop := keyZeros_ct.mono
    (P' := fun (s t : State) => Q s ∧ Q t ∧ s.sp = t.sp) (fun _ _ h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.1.1.trans h.2.1.1.symm
      · exact h.1.2.trans h.2.1.2.symm) (fun _ _ h => h)
  unfold VG.Impl.Ffdh.Arm.Domain.GenerateKey.clearOutput
  exact relCT_chain args wp wp loop

structure KeyOutputState (p : Inputs) (slots : List Nat) (s : State) : Prop where
  context : ArgumentMemory p slots s
  outputs : KeyOutputs p s

theorem keyOutput_mask (s : State) {p : Inputs} {slots : List Nat} (slot : Nat)
    (saved : ∀ d ∈ slots, d + 4 ≤ 72) (hs : slot ∈ slots) (hk : 32 ∈ slots)
    (which : slot = 40 ∨ slot = 36) (h : KeyOutputState p slots s) :
    WP isa (VG.Impl.Ffdh.Arm.Domain.GenerateKey.maskOutput slot) s (KeyOutputState p slots) := by
  rcases which with rfl | rfl
  · refine WP.mono (keyMask_ok s 40 h.context (by decide) hs hk rfl h.outputs.privateBuffer) ?_
    rintro t ⟨_, frame, rest⟩
    exact ⟨h.context.after_output frame rest h.outputs.privateDomain h.outputs.privateStack saved, h.outputs.after rest⟩
  · refine WP.mono (keyMask_ok s 36 h.context (by decide) hs hk rfl h.outputs.publicBuffer) ?_
    rintro t ⟨_, frame, rest⟩
    exact ⟨h.context.after_output frame rest h.outputs.publicDomain h.outputs.publicStack saved, h.outputs.after rest⟩

theorem keyOutput_clear (s : State) {p : Inputs} {slots : List Nat} (slot : Nat)
    (saved : ∀ d ∈ slots, d + 4 ≤ 72) (hs : slot ∈ slots) (hk : 32 ∈ slots)
    (which : slot = 40 ∨ slot = 36) (h : KeyOutputState p slots s) :
    WP isa (VG.Impl.Ffdh.Arm.Domain.GenerateKey.clearOutput slot) s (KeyOutputState p slots) := by
  rcases which with rfl | rfl
  · refine WP.mono (keyClear_ok s 40 h.context (by decide) hs hk h.outputs.privateBuffer) ?_
    rintro t ⟨_, frame, rest⟩
    exact ⟨h.context.after_output frame rest h.outputs.privateDomain h.outputs.privateStack saved, h.outputs.after rest⟩
  · refine WP.mono (keyClear_ok s 36 h.context (by decide) hs hk h.outputs.publicBuffer) ?_
    rintro t ⟨_, frame, rest⟩
    exact ⟨h.context.after_output frame rest h.outputs.publicDomain h.outputs.publicStack saved, h.outputs.after rest⟩

theorem keyFinish_ct {p : Inputs} {slots : List Nat}
    (saved : ∀ d ∈ slots, d + 4 ≤ 72) (h32 : 32 ∈ slots) (h36 : 36 ∈ slots) (h40 : 40 ∈ slots) :
    RelCT isa (fun s t => KeyOutputState p slots s ∧ KeyOutputState p slots t ∧ s.sp = t.sp)
      VG.Impl.Ffdh.Arm.Domain.GenerateKey.finish (fun _ _ => True) := by
  have mask40 := (keyMask_ct 40 (by decide) h40 h32).mono
    (P' := fun (s t : State) => KeyOutputState p slots s ∧ KeyOutputState p slots t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨h.1.context, h.2.1.context, h.2.2⟩) (fun _ _ h => h)
  have mask36 := (keyMask_ct 36 (by decide) h36 h32).mono
    (P' := fun (s t : State) => KeyOutputState p slots s ∧ KeyOutputState p slots t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨h.1.context, h.2.1.context, h.2.2⟩) (fun _ _ h => h)
  unfold VG.Impl.Ffdh.Arm.Domain.GenerateKey.finish
  exact relCT_chain mask40 (keyOutput_mask · 40 saved h40 h32 (.inl rfl)) (keyOutput_mask · 40 saved h40 h32 (.inl rfl))
    ((relCT_keep_sp mask36 (fun _ _ h => h.2.2)).seq keyFinishStatus_ct)

theorem keyFail_ct {p : Inputs} {slots : List Nat}
    (saved : ∀ d ∈ slots, d + 4 ≤ 72) (h32 : 32 ∈ slots) (h36 : 36 ∈ slots) (h40 : 40 ∈ slots) :
    RelCT isa (fun s t => KeyOutputState p slots s ∧ KeyOutputState p slots t ∧ s.sp = t.sp)
      VG.Impl.Ffdh.Arm.Domain.GenerateKey.failScalar (fun _ _ => True) := by
  have clear40 := (keyClear_ct 40 (by decide) h40 h32).mono
    (P' := fun (s t : State) => KeyOutputState p slots s ∧ KeyOutputState p slots t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨h.1.context, h.2.1.context, h.2.2⟩) (fun _ _ h => h)
  have clear36 := (keyClear_ct 36 (by decide) h36 h32).mono
    (P' := fun (s t : State) => KeyOutputState p slots s ∧ KeyOutputState p slots t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨h.1.context, h.2.1.context, h.2.2⟩) (fun _ _ h => h)
  unfold VG.Impl.Ffdh.Arm.Domain.GenerateKey.failScalar
  exact relCT_chain clear40 (keyOutput_clear · 40 saved h40 h32 (.inl rfl)) (keyOutput_clear · 40 saved h40 h32 (.inl rfl))
    (clear36.seq ((ret_ct 2).mono (fun _ _ _ => trivial) (fun _ _ h => h)))

end VG.Proof.Ffdh.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/KeyFinishCT.lean`, which only this module imported.
section

/-! Public-value export and final key masking have a fixed trace for every
secret exponent and result flag. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (numAt)

structure KeyExportInput (p : Inputs) (slots : List Nat) (s : State) : Prop where
  context : Context p slots s
  ready : ArithmeticReady p.base p.len p.w s
  outputs : KeyOutputs p s
  valueFit : numAt s.mem (State.addr p.base) p.w 6 < 2 ^ (8 * p.k)

theorem keySave_next (s : State) {p : Inputs} {slots : List Nat}
    (stable : stableSlots slots = true) (saved : ∀ d ∈ slots, d + 4 ≤ 64 ∨ 68 ≤ d)
    (outputY : p.output = p.publicValue) (h : KeyExportInput p slots s) :
    WP isa (.block VG.Impl.Ffdh.Arm.Domain.Exchange.saveResult) s (KeyExportInput p slots) := by
  have exchange : ExchangeFinishInput p slots s :=
    ⟨h.context, h.ready, by rw [outputY]; exact h.outputs.publicBuffer,
      by rw [outputY]; exact h.outputs.publicWorkspace.symm,
      by rw [outputY]; exact h.outputs.publicStack, h.valueFit⟩
  refine WP.mono (withAllRest (exchangeSave_ready s exchange stable saved)) ?_
  rintro t ⟨result, rest⟩
  exact ⟨result.context, result.ready, h.outputs.after rest, result.valueFit⟩

theorem keyExport_next (s : State) {p : Inputs} {slots : List Nat}
    (saved : ∀ d ∈ slots, d + 4 ≤ 72) (h4 : 4 ∈ slots) (h32 : 32 ∈ slots)
    (outputY : p.output = p.publicValue) (h : KeyExportInput p slots s) :
    WP isa VG.Impl.Ffdh.Arm.Domain.Exchange.exportResult s (KeyOutputState p slots) := by
  refine WP.mono (exportResult_ok s h.context h4 h32 h.ready
    (by rw [outputY]; exact h.outputs.publicBuffer) (by rw [outputY]; exact h.outputs.publicWorkspace.symm) h.valueFit) ?_
  rintro t ⟨_, frame, rest⟩
  rw [outputY] at frame
  exact ⟨h.context.toArgumentMemory.after_output frame rest h.outputs.publicDomain h.outputs.publicStack saved,
    h.outputs.after rest⟩

theorem keyExportFinish_ct {p : Inputs} {slots : List Nat}
    (stable : stableSlots slots = true) (h4 : 4 ∈ slots) (h32 : 32 ∈ slots) (h36 : 36 ∈ slots) (h40 : 40 ∈ slots)
    (saved : ∀ d ∈ slots, d + 4 ≤ 64 ∨ 68 ≤ d) (outputY : p.output = p.publicValue) :
    RelCT isa (fun s t => KeyExportInput p slots s ∧ KeyExportInput p slots t ∧ s.sp = t.sp)
      (.seq (.block VG.Impl.Ffdh.Arm.Domain.Exchange.saveResult)
        (.seq VG.Impl.Ffdh.Arm.Domain.Exchange.exportResult VG.Impl.Ffdh.Arm.Domain.GenerateKey.finish)) (fun _ _ => True) := by
  have bounds (d : Nat) (hd : d ∈ slots) := (stableSlots_at stable hd).1
  have save := (RelCT.block_append (stackAddr_ct.seq (storeLocal_ct .r11 64))).mono
    (P' := fun (s t : State) => KeyExportInput p slots s ∧ KeyExportInput p slots t ∧ s.sp = t.sp)
    (fun _ _ h => h.2.2) (fun _ _ _ => trivial)
  have exportCT := (exportResult_ct h4 h32).mono
    (P' := fun (s t : State) => KeyExportInput p slots s ∧ KeyExportInput p slots t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨⟨h.1.context, h.1.ready⟩, ⟨h.2.1.context, h.2.1.ready⟩, h.2.2⟩) (fun _ _ h => h)
  exact relCT_chain save (keySave_next · stable saved outputY) (keySave_next · stable saved outputY)
    (relCT_chain exportCT (keyExport_next · bounds h4 h32 outputY) (keyExport_next · bounds h4 h32 outputY)
      (keyFinish_ct bounds h32 h36 h40))

end VG.Proof.Ffdh.Arm
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (numAt Operand)

structure KeyPowerInput (p : Inputs) (slots : List Nat) (eb : List Byte) (s : State) : Prop extends
    PowerAtInput p slots 56 16 p.P ((p.dom.drop p.k).take p.k) eb s where
  outputs : KeyOutputs p s

structure KeyRangeInput (p : Inputs) (slots : List Nat) (s : State) : Prop extends KeyExportInput p slots s where
  modulus : numAt s.mem (State.addr p.base) p.w 0 = p.P

theorem keyPower_next (s : State) {p : Inputs} {slots : List Nat} {eb : List Byte}
    (stable : stableSlots slots = true) (h16 : 16 ∈ slots) (h20 : 20 ∈ slots) (h32 : 32 ∈ slots) (h56 : 56 ∈ slots)
    (size : eb.length = p.scalarWidth) (odd : p.P % 2 = 1) (h : KeyPowerInput p slots eb s) :
    WP isa (VG.Impl.Ffdh.Arm.Domain.powerAt 56 16 20) s (KeyRangeInput p slots) := by
  refine WP.mono (powerAt_ok s 56 16 20 h.context stable h56 h16 h20 h32 h.ready h.modulus odd h.r2
    h.source p.gLength h.exponent (by rw [size]; exact p.scalarWidthBounds.1)
    (by rw [size]; have := p.scalarWidthBounds; have := p.maxLength; omega)
    (by change BitVec.ofNat 32 p.scalarWidth = _; rw [size])) ?_
  rintro t ⟨context, ready, power, modulus, _, _, _, rest⟩
  refine ⟨⟨context, ready, h.outputs.after rest, ?_⟩, modulus⟩
  rw [power, VG.Proof.Bignum.powMod_eq]
  have large := h.ready.modulus
  rw [h.modulus] at large
  exact Nat.lt_trans (Nat.mod_lt _ (by omega)) p.modulusBound

theorem keyRange_next (s : State) {p : Inputs} {slots : List Nat}
    (stable : stableSlots slots = true) (odd : p.P % 2 = 1) (h : KeyRangeInput p slots s) :
    WP isa (VG.Impl.Ffdh.Arm.inRange 6) s (KeyExportInput p slots) := by
  refine WP.mono (inRange_ok s h.ready (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp] : Operand 6)
    (by decide) (by rw [h.modulus]; exact odd)) ?_
  rintro t ⟨ready, _, arrays, frame, rest⟩
  exact ⟨h.context.after_workspace frame rest ready.ptr (fun d hd => (stableSlots_at stable hd).1), ready,
    h.outputs.after rest, by rw [arrays 6 (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]) (by decide)]; exact h.valueFit⟩

theorem keyTail_ct {p : Inputs} {slots : List Nat} {eb1 eb2 : List Byte}
    (stable : stableSlots slots = true) (h4 : 4 ∈ slots) (h16 : 16 ∈ slots) (h20 : 20 ∈ slots) (h32 : 32 ∈ slots)
    (h36 : 36 ∈ slots) (h40 : 40 ∈ slots) (h56 : 56 ∈ slots)
    (saved : ∀ d ∈ slots, d + 4 ≤ 64 ∨ 68 ≤ d)
    (size1 : eb1.length = p.scalarWidth) (size2 : eb2.length = p.scalarWidth)
    (odd : p.P % 2 = 1) (outputY : p.output = p.publicValue) :
    RelCT isa (fun s t => KeyPowerInput p slots eb1 s ∧ KeyPowerInput p slots eb2 t ∧ s.sp = t.sp)
      VG.Impl.Ffdh.Arm.Domain.GenerateKey.tail (fun _ _ => True) := by
  have power := (powerAt_ct stable h56 h16 h20 h32 p.gLength
    (by rw [size1]; exact p.scalarWidthBounds.1)
    (by rw [size1]; have := p.scalarWidthBounds; have := p.maxLength; omega)
    (by change BitVec.ofNat 32 p.scalarWidth = _; rw [size1]) (size1.trans size2.symm) odd).mono
    (P' := fun (s t : State) => KeyPowerInput p slots eb1 s ∧ KeyPowerInput p slots eb2 t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨h.1.toPowerAtInput, h.2.1.toPowerAtInput, h.2.2⟩) (fun _ _ h => h)
  have range := (inRange_ct (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp] : Operand 6) (by decide)).mono
    (P' := fun (s t : State) => KeyRangeInput p slots s ∧ KeyRangeInput p slots t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨h.1.ready, h.2.1.ready, h.2.2⟩) (fun _ _ h => h)
  unfold VG.Impl.Ffdh.Arm.Domain.GenerateKey.tail
  exact relCT_chain power (keyPower_next · stable h16 h20 h32 h56 size1 odd) (keyPower_next · stable h16 h20 h32 h56 size2 odd)
    (relCT_chain range (keyRange_next · stable odd) (keyRange_next · stable odd)
      (keyExportFinish_ct stable h4 h32 h36 h40 saved outputY))

end VG.Proof.Ffdh.Arm
