module

import VerifiedGarbage.Proof.Ffdh.Arm.KeyMemory
import VerifiedGarbage.Proof.Ffdh.Arm.KeyFinish
import VerifiedGarbage.Proof.Ffdh.Arm.KeyFail
import VerifiedGarbage.Proof.Ffdh.Arm.KeyArgsCT
import VerifiedGarbage.Proof.Ffdh.Arm.KeyByteCT
import VerifiedGarbage.Proof.Ffdh.Arm.BranchCT
import VerifiedGarbage.Proof.Bignum.Arm.MaskBytesCT
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Impl.Ffdh.Arm.GenerateKey
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyOutputs
import VerifiedGarbage.Proof.Ffdh.Arm.KeyClear
import VerifiedGarbage.Proof.Ffdh.Arm.KeyMask

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
