module
public import VerifiedGarbage.Proof.Rsa.X86.PrivCrtArgs
public import VerifiedGarbage.Proof.Rsa.X86.PrivPrecomputeCall
public import VerifiedGarbage.Proof.Rsa.X86.PrivPublicArgs

import VerifiedGarbage.Proof.Rsa.X86.PrivRetained
import VerifiedGarbage.Proof.Rsa.X86.PrivPublicCall
import VerifiedGarbage.Proof.Rsa.X86.PrivCrtCall
import VerifiedGarbage.Proof.Rsa.BytesFrame
import VerifiedGarbage.Proof.Framework.Contract

/-! # Intermediate states for composing independent secret executions -/

@[expose] public section
namespace VG.Proof.Rsa.X86.PrivChecked
open VG VG.X86 VG.Impl.Rsa.X86.PrivChecked VG.Proof.Bignum.X86

structure PrivateState (g : PrivGeometry) (bs : Fin 8 → List Byte) (s : State) : Prop where
  context : PrivContext g bs s

structure CrtReady (g : PrivGeometry) (bs : Fin 8 → List Byte) (s : State)  : Prop extends PrivateState g bs s where
  args : CrtArgs g s
structure PcReady (g : PrivGeometry) (bs : Fin 8 → List Byte) (s : State)  : Prop extends PrivateState g bs s where
  args : Arguments g (pcArgument g) 6 s

def PcPublic (g : PrivGeometry) (nb : List Byte) (s : State) : Prop :=
  Spec.Rsa.wordsAt s.mem (byteAddr g.precomputation) (2 * Spec.Rsa.modulusWords g.length) =
    (Spec.Rsa.publicPrecompute nb).getD (List.replicate (2 * Spec.Rsa.modulusWords g.length) 0)

structure PcReturned (g : PrivGeometry) (bs : Fin 8 → List Byte) (s : State)  : Prop extends PrivateState g bs s where
  pre : PcPublic g (bs 0) s
structure PdReady (g : PrivGeometry) (bs : Fin 8 → List Byte) (s : State)  : Prop extends PcReturned g bs s where
  args : Arguments g (pdArgument g) 10 s

theorem crtArgs_ready (s : State) {g : PrivGeometry} {bs : Fin 8 → List Byte} (h : PrivateState g bs s) :
    WP isa (.block crtArgs) s (CrtReady g bs) := by
  refine WP.mono (crtArgs_ok s h.context) ?_
  rintro t ⟨ht, args, _, _⟩
  exact ⟨⟨ht⟩, args⟩

theorem crtCall_ready (v : CrtImpl) (s : State) {g : PrivGeometry} {bs : Fin 8 → List Byte} (h : CrtReady g bs s) :
    WP isa (.call v.name v.code) s (PrivateState g bs) := by
  refine WP.mono (crt_call v h.context h.args) ?_
  rintro t ⟨ht, _, _, _⟩
  exact ⟨ht⟩

theorem pcArgs_ready (s : State) {g : PrivGeometry} {bs : Fin 8 → List Byte} (h : PrivateState g bs s) :
    WP isa (.block precomputeArgs) s (PcReady g bs) := by
  refine WP.mono (precomputeArgs_ok s h.context) ?_
  rintro t ⟨ht, args, _, _, _⟩
  exact ⟨⟨ht⟩, args⟩

theorem pcCall_ready (v : CrtImpl) (s : State) {g : PrivGeometry} {bs : Fin 8 → List Byte} (h : PcReady g bs s) :
    WP isa (.call v.pcName v.pc) s (PcReturned g bs) := by
  refine WP.mono (pc_call v h.context h.args) ?_
  rintro t ⟨ht, _, _, output⟩
  refine ⟨⟨ht⟩, ?_⟩
  cases hp : Spec.Rsa.publicPrecompute (bs 0) <;> simp only [PcOut, PcPublic, hp, Option.getD] at output ⊢ <;> exact output.2

theorem pdArgs_ready (s : State) {g : PrivGeometry} {bs : Fin 8 → List Byte} (h : PcReturned g bs s) :
    WP isa (.block publicArgs) s (PdReady g bs) := by
  refine WP.mono (publicArgs_ok s h.context) ?_
  rintro t ⟨ht, args, _, _, frame, _⟩
  refine ⟨⟨⟨ht⟩, ?_⟩, args⟩
  unfold PcPublic
  rw [wordsAt_frame frame (by have := h.context.valid.maxLength; simp only [Spec.Rsa.modulusWords]; omega)
    (precomputation_setup h.context.valid)]
  exact h.pre

theorem pdCall_ready (v : CrtImpl) (s : State) {g : PrivGeometry} {bs : Fin 8 → List Byte} (h : PdReady g bs s) :
    WP isa (.call v.pdName v.pd) s (PrivateState g bs) := by
  refine WP.mono (pd_call v h.context h.args) ?_
  rintro t ⟨ht, _, _, _⟩
  exact ⟨ht⟩
end VG.Proof.Rsa.X86.PrivChecked
