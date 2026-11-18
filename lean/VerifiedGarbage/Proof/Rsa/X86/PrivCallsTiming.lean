module

import VerifiedGarbage.Proof.Rsa.X86.PrivCallPublic
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Rsa.X86.PrivPublicCall
import VerifiedGarbage.Proof.Rsa.X86.PrivCrtCall
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Rsa.X86.PrivCrtArgs
public import VerifiedGarbage.Proof.Rsa.X86.PrivPrecomputePre
import VerifiedGarbage.Proof.Rsa.X86.PrivRetained
import VerifiedGarbage.Proof.Rsa.BytesFrame

/-! ### `Rsa.X86.PrivStages`, which this module and modules that import it used -/

section

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
  rw [wordsAt_frame frame (by have := h.context.valid.maxLength; simp only [Spec.Rsa.modulusWords]; omega_using [this])
    (precomputation_setup h.context.valid)]
  exact h.pre

theorem pdCall_ready (v : CrtImpl) (s : State) {g : PrivGeometry} {bs : Fin 8 → List Byte} (h : PdReady g bs s) :
    WP isa (.call v.pdName v.pd) s (PrivateState g bs) := by
  refine WP.mono (pd_call v h.context h.args) ?_
  rintro t ⟨ht, _, _, _⟩
  exact ⟨ht⟩
end VG.Proof.Rsa.X86.PrivChecked

end

end

/-! # Each nested call leaks only the shared public key and layout -/

@[expose] public section
namespace VG.Proof.Rsa.X86.PrivChecked
open VG VG.X86 VG.Impl.Rsa.X86.PrivChecked VG.Proof.Bignum.X86

theorem crtCall_ct (v : CrtImpl) {g : PrivGeometry} {bs1 bs2 : Fin 8 → List Byte} (nb : bs1 0 = bs2 0) :
    RelCT isa (fun s t => CrtReady g bs1 s ∧ CrtReady g bs2 t)
      (.call v.name v.code) (fun _ _ => True) := by
  apply RelCT.call v.verified.1 v.verified.2.1 (crtRd g) (crtWr g)
  intro s t h
  exact ⟨crtCall_pre h.1.context h.1.args, crtCall_pre h.2.context h.2.args,
    crtCall_pub h.1.context h.2.context h.1.args h.2.args nb,
    (crtCovers h.1.context).1, (crtCovers h.1.context).2,
    (crtCovers h.2.context).1, (crtCovers h.2.context).2, h.1.context.sp.trans h.2.context.sp.symm⟩

theorem pcCall_ct (v : CrtImpl) {g : PrivGeometry} {bs1 bs2 : Fin 8 → List Byte} (nb : bs1 0 = bs2 0) :
    RelCT isa (fun s t => PcReady g bs1 s ∧ PcReady g bs2 t)
      (.call v.pcName v.pc) (fun _ _ => True) := by
  apply RelCT.call v.pcVerified.1 v.pcVerified.2.1 (pcRd g) (pcWr g)
  intro s t h
  exact ⟨pcCall_pre h.1.context h.1.args, pcCall_pre h.2.context h.2.args,
    pcCall_pub h.1.context h.2.context h.1.args h.2.args nb,
    (pcCovers h.1.context).1, (pcCovers h.1.context).2,
    (pcCovers h.2.context).1, (pcCovers h.2.context).2, h.1.context.sp.trans h.2.context.sp.symm⟩

theorem pdCall_ct (v : CrtImpl) {g : PrivGeometry} {bs1 bs2 : Fin 8 → List Byte}
    (nb : bs1 0 = bs2 0) (eb : bs1 1 = bs2 1) :
    RelCT isa (fun s t => PdReady g bs1 s ∧ PdReady g bs2 t)
      (.call v.pdName v.pd) (fun _ _ => True) := by
  apply RelCT.call v.pdVerified.1 v.pdVerified.2.1 (pdRd g) (pdWr g)
  intro s t h
  have preS := h.1.pre
  have preT := h.2.pre
  unfold PcPublic at preS preT
  rw [nb] at preS
  exact ⟨pdCall_pre h.1.context h.1.args, pdCall_pre h.2.context h.2.args,
    pdCall_pub h.1.context h.2.context h.1.args h.2.args eb (preS.trans preT.symm),
    (pdCovers h.1.context).1, (pdCovers h.1.context).2,
    (pdCovers h.2.context).1, (pdCovers h.2.context).2, h.1.context.sp.trans h.2.context.sp.symm⟩
end VG.Proof.Rsa.X86.PrivChecked
