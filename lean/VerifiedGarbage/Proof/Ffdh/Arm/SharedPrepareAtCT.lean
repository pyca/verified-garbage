module

public import VerifiedGarbage.Proof.Ffdh.Arm.KeyPrograms
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyPrepareLaw
public import VerifiedGarbage.Impl.Ffdh.Arm.SharedPrepare
public import VerifiedGarbage.Proof.Bignum.Arm.MontBackend

import VerifiedGarbage.Proof.Ffdh.Arm.SharedPrepareCT
import VerifiedGarbage.Proof.Ffdh.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.TwoExpSharedCT
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Ffdh.Arm.SharedPrepare
import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
import VerifiedGarbage.Proof.Bignum.Arm.TwoExpShared
import VerifiedGarbage.Proof.Framework.Block
/-! # The shared native key-preparation boundary hides modulus values -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/SharedPrepareAt.lean`, which only this module imported.
section

/-! # Shared callable modulus preparation within the FFDH argument frame -/

section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)
open VG.Proof.Rsa.Mont (numAt)

theorem sharedPrepareAt24_ok (backend : MontBackend) (s : State) {p : Inputs} {slots : List Nat}
    (h : Context p slots s) (calls : KeyCallMemory p s)
    (stable : stableSlots slots = true) (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h32 : 32 ∈ slots)
    (large : 1 < p.P) (odd : p.P % 2 = 1) :
    WP isa (VG.Impl.Ffdh.Arm.SharedPrepare.prepareAt
      (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul) 24) s fun t =>
      Context p slots t ∧ ArithmeticReady p.base p.len p.w t ∧
      numAt t.mem (State.addr p.base) p.w 0 = p.P ∧
      numAt t.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % p.P ∧
      Frame (keyPrepareWrites p s) s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [VG.Impl.Ffdh.Arm.SharedPrepare.prepareAt, WP.seq_iff]
  refine WP.mono (prepareArgs_ok s 24 h stable h24 h32 h0) ?_
  rintro u ⟨contextU, stack, _, countU, _, frameU, restU⟩
  have sourceU := contextU.pBytes
  have bytes : Spec.Rsa.bytesAt u.mem (State.addr p.domain) p.k = p.dom.take p.k := by
    simpa only [p.pLength] using sourceU.bytes
  have input : PrepareInput p.base p.domain p.len p.k u :=
    ⟨contextU.workspace, by rw [stack.savedOutput]; exact stack, contextU.ptr, countU,
      p.minLength, p.maxLength, p.publicSpace,
      by rw [← p.pLength]; exact sourceU.fits,
      by rw [← p.pLength]; exact sourceU.readable,
      by rw [← p.pLength]; exact sourceU.separate,
      by rw [bytes]; exact large, by rw [bytes]; exact odd⟩
  let K := TwoExp.sharedMontgomery p.base s.sp p.len p.w backend.name backend.mul
    (fun _ _ _ ho ha hb v input => backend.correct v input ho ha hb) backend.stackOk
  have hp : TwoExp.CallReady p.base s.sp p.len u := ⟨(calls.after restU).stack, restU.sp⟩
  refine WP.mono (sharedPrepare_ok u K input hp) ?_
  rintro t ⟨ready, modulus, r2, _, frameT, restT⟩
  rw [bytes] at modulus r2
  have localFrame : Frame [⟨State.addr p.base, 8 * p.len⟩, FrameStack.belowA u.sp 48]
      u.mem t.mem := by simpa only [K, restU.sp] using frameT
  have contextT := contextU.after_call (calls.after restU) localFrame restT ready.ptr
    (fun d hd => (stableSlots_at stable hd).1)
  have frame : Frame (keyPrepareWrites p s) s.mem t.mem :=
    (frameU.mono (by intro r hr; simp only [keyPrepareWrites, prepareAtWrites, List.mem_append,
      List.mem_cons]; exact Or.inl (Or.inr hr))).trans
      (frameT.mono (by
        intro r hr
        simp only [List.mem_cons] at hr
        simp only [keyPrepareWrites, prepareAtWrites, List.mem_append, List.mem_cons]
        rcases hr with hr | hr
        · exact Or.inl (Or.inl hr)
        · exact Or.inr hr))
  exact ⟨contextT, ready, modulus, r2, frame,
    (restU.mono (by simp [roundClobbers])).trans restT⟩

end VG.Proof.Ffdh.Arm
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem sharedPrepareAt24_ct (backend : MontBackend) {p : Inputs} {slots : List Nat}
    (stable : stableSlots slots = true) (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h32 : 32 ∈ slots)
    (large : 1 < p.P) (odd : p.P % 2 = 1) :
    RelCT isa (fun s t => (Context p slots s ∧ KeyCallMemory p s) ∧
      (Context p slots t ∧ KeyCallMemory p t) ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.SharedPrepare.prepareAt
        (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul) 24) (fun _ _ => True) := by
  have family (sp0 : BitVec 32) :
      RelCT isa (fun s t => (Context p slots s ∧ KeyCallMemory p s ∧ s.sp = sp0) ∧
        (Context p slots t ∧ KeyCallMemory p t ∧ t.sp = sp0) ∧ s.sp = t.sp)
        (VG.Impl.Ffdh.Arm.SharedPrepare.prepareAt
          (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul) 24) (fun _ _ => True) := by
    let correct := fun o a b ho ha hb v input => backend.correct v (base := p.base) (len := p.len) (w := p.w) (o := o) (a := a) (b := b) input ho ha hb
    let K := TwoExp.sharedMontgomery p.base sp0 p.len p.w backend.name backend.mul correct backend.stackOk
    have timing : TwoExp.MontgomeryTiming K :=
      TwoExp.sharedMontgomeryTiming p.base sp0 p.len p.w backend.name backend.mul correct backend.stackOk
        (fun _ _ _ ho ha hb => backend.rawCT ho ha hb)
    have argsInput (s : State) (h : Context p slots s ∧ KeyCallMemory p s ∧ s.sp = sp0) :
        WP isa (.block (VG.Impl.Ffdh.Arm.Domain.prepareArgs 24)) s fun u =>
          PrepareInput p.base p.domain p.len p.k u ∧ TwoExp.CallReady p.base sp0 p.len u := by
      refine WP.mono (prepareArgs_ok s 24 h.1 stable h24 h32 h0) ?_
      rintro u ⟨contextU, stack, _, countU, _, _, restU⟩
      have sourceU := contextU.pBytes
      have bytes : Spec.Rsa.bytesAt u.mem (State.addr p.domain) p.k = p.dom.take p.k := by
        simpa only [p.pLength] using sourceU.bytes
      refine ⟨?_, (h.2.1.after restU).stack, restU.sp.trans h.2.2⟩
      exact ⟨contextU.workspace, by rw [stack.savedOutput]; exact stack, contextU.ptr, countU,
        p.minLength, p.maxLength, p.publicSpace,
        by rw [← p.pLength]; exact sourceU.fits,
        by rw [← p.pLength]; exact sourceU.readable,
        by rw [← p.pLength]; exact sourceU.separate,
        by rw [bytes]; exact large, by rw [bytes]; exact odd⟩
    unfold VG.Impl.Ffdh.Arm.SharedPrepare.prepareAt
    exact relCT_chain ((prepareArgs_ct 24).mono (fun _ _ h => h.2.2) (fun _ _ h => h))
      argsInput argsInput (sharedPrepare_ct K timing p.width.2.2.2.2)
  intro s t tr1 tr2 u v h e1 e2
  exact family s.sp s t tr1 tr2 u v
    ⟨⟨h.1.1, h.1.2, rfl⟩, ⟨h.2.1.1, h.2.1.2, h.2.2.symm⟩, h.2.2⟩ e1 e2

theorem sharedPrepareLaw (backend : MontBackend) :
    KeyPrepareLaw (VG.Impl.Ffdh.Arm.SharedPrepare.prepareAt
      (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul) 24) :=
  { correct := by
      intro s p slots h calls stable h0 h24 h32 large odd _normalized
      exact sharedPrepareAt24_ok backend s h calls stable h0 h24 h32 large odd
    ct := by
      intro p slots stable h0 h24 h32 large odd _normalized
      exact sharedPrepareAt24_ct backend stable h0 h24 h32 large odd }

end VG.Proof.Ffdh.Arm
