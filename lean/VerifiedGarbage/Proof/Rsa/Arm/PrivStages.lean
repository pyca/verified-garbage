module
public import VerifiedGarbage.Proof.Rsa.Arm.PrivCrtArgs
public import VerifiedGarbage.Proof.Rsa.Arm.PrivPcCall
public import VerifiedGarbage.Proof.Rsa.Arm.PrivPdArgs

import VerifiedGarbage.Proof.Rsa.Arm.PrivStatusPreserved
import VerifiedGarbage.Proof.Rsa.Arm.PrivPdCall
import VerifiedGarbage.Proof.Rsa.Arm.PrivCrtCall
import VerifiedGarbage.Proof.Rsa.BytesFrame

/-! # Intermediate states for composing independent secret executions -/

@[expose] public section
namespace VG.Proof.Rsa.Arm
open VG VG.Arm VG.Impl.Rsa.Arm.PrivChecked VG.Proof.Bignum.Arm

structure PrivateStart (g : PrivGeometry) (bs : Fin 8 → List Byte) (s : State) : Prop where
  context : PrivContext g bs s
  output : s.gpr .r0 = g.output
  modulus : s.gpr .r2 = g.sources 0
  count : s.gpr .r3 = BitVec.ofNat 32 g.length

structure PrivateState (g : PrivGeometry) (bs : Fin 8 → List Byte) (s : State) : Prop where
  context : PrivContext g bs s
  slots : PrivSlots g s.mem

structure CrtReady (g : PrivGeometry) (bs : Fin 8 → List Byte) (s : State)  : Prop extends PrivateState g bs s where
  args : CrtArgs g s
structure PcReady (g : PrivGeometry) (bs : Fin 8 → List Byte) (s : State)  : Prop extends PrivateState g bs s where
  args : PcArgs g s

def PcPublic (g : PrivGeometry) (nb : List Byte) (s : State) : Prop :=
  Spec.Rsa.wordsAt s.mem (State.addr g.precomputation) (2 * Spec.Rsa.modulusWords g.length) =
    (Spec.Rsa.publicPrecompute nb).getD (List.replicate (2 * Spec.Rsa.modulusWords g.length) 0)

structure PcReturned (g : PrivGeometry) (bs : Fin 8 → List Byte) (s : State)  : Prop extends PrivateState g bs s where
  pre : PcPublic g (bs 0) s
structure PdReady (g : PrivGeometry) (bs : Fin 8 → List Byte) (s : State)  : Prop extends PcReturned g bs s where
  args : PdArgs g s

theorem crtArgs_ready (s : State) {g : PrivGeometry} {bs : Fin 8 → List Byte} (h : PrivateStart g bs s) :
    WP isa (.block crtArgs) s (CrtReady g bs) := by
  refine WP.mono (crtArgs_ok s h.context h.output h.modulus h.count) ?_
  rintro t ⟨ht, slots, args, _, _⟩
  exact ⟨⟨ht, slots⟩, args⟩

theorem crtCall_ready (v : CrtImpl) (s : State) {g : PrivGeometry} {bs : Fin 8 → List Byte} (h : CrtReady g bs s) :
    WP isa (.call v.name v.code) s (PrivateState g bs) := by
  refine WP.mono (crt_call v h.context h.slots h.args) ?_
  rintro t ⟨ht, slots, _, _, _⟩
  exact ⟨ht, slots⟩

theorem pcArgs_ready (s : State) {g : PrivGeometry} {bs : Fin 8 → List Byte} (h : PrivateState g bs s) :
    WP isa (.block pcArgs) s (PcReady g bs) := by
  refine WP.mono (pcArgs_ok s h.context h.slots) ?_
  rintro t ⟨ht, slots, args, _, _, _⟩
  exact ⟨⟨ht, slots⟩, args⟩

theorem pcCall_ready (v : CrtImpl) (s : State) {g : PrivGeometry} {bs : Fin 8 → List Byte} (h : PcReady g bs s) :
    WP isa (.call v.pcName v.pc) s (PcReturned g bs) := by
  refine WP.mono (pc_call v h.context h.slots h.args) ?_
  rintro t ⟨ht, slots, _, _, output⟩
  refine ⟨⟨ht, slots⟩, ?_⟩
  cases hp : Spec.Rsa.publicPrecompute (bs 0) <;> simp only [PcOut, PcPublic, hp, Option.getD] at output ⊢ <;> exact output.2

theorem pdArgs_ready (s : State) {g : PrivGeometry} {bs : Fin 8 → List Byte} (h : PcReturned g bs s) :
    WP isa (.block pdArgs) s (PdReady g bs) := by
  refine WP.mono (pdArgs_ok s h.context h.slots) ?_
  rintro t ⟨ht, slots, args, _, frame, _⟩
  refine ⟨⟨⟨ht, slots⟩, ?_⟩, args⟩
  unfold PcPublic
  rw [wordsAt_frame frame (by have := h.context.valid.maxLength; simp only [Spec.Rsa.modulusWords]; omega)
    (precomputation_pdPrefix h.context.valid)]
  exact h.pre

theorem pdCall_ready (v : CrtImpl) (s : State) {g : PrivGeometry} {bs : Fin 8 → List Byte} (h : PdReady g bs s) :
    WP isa (.call v.pdName v.pd) s (PrivateState g bs) := by
  refine WP.mono (pd_call v h.context h.slots h.args) ?_
  rintro t ⟨ht, slots, _, _, _⟩
  exact ⟨ht, slots⟩
end VG.Proof.Rsa.Arm
