module

public import VerifiedGarbage.Proof.Ffdh.Arm.DomainSharedPrepareAt
import VerifiedGarbage.Proof.Ffdh.Arm.NormalizedPrepare
public import VerifiedGarbage.Impl.Ffdh.Arm.NormalizedPrepare
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
public import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
import VerifiedGarbage.Proof.Bignum.Arm.TwoExpShared
import VerifiedGarbage.Proof.Framework.Block

/-! # Normalized callable modulus preparation within the FFDH argument frame -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)
open VG.Proof.Rsa.Mont (numAt)

theorem domainNormalizedPrepareAt24_ok (backend : MontBackend) (s : State) {p : Inputs} {slots : List Nat}
    (h : Context p slots s) (calls : DomainCallMemory p s)
    (stable : stableSlots slots = true) (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h32 : 32 ∈ slots)
    (large : 1 < p.P) (odd : p.P % 2 = 1)
    (normalized : 2 ^ (64 * (p.w - 1)) ≤ p.P) :
    WP isa (VG.Impl.Ffdh.Arm.NormalizedPrepare.prepareAt
      (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul) 24) s fun t =>
      Context p slots t ∧ ArithmeticReady p.base p.len p.w t ∧
      numAt t.mem (State.addr p.base) p.w 0 = p.P ∧
      numAt t.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % p.P ∧
      Frame (domainPrepareWrites p s) s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [VG.Impl.Ffdh.Arm.NormalizedPrepare.prepareAt, WP.seq_iff]
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
  refine WP.mono (normalizedPrepare_ok u K input hp (by rw [bytes]; exact normalized)) ?_
  rintro t ⟨ready, modulus, r2, _, frameT, restT⟩
  rw [bytes] at modulus r2
  have localFrame : Frame [⟨State.addr p.base, 8 * p.len⟩, FrameStack.belowA u.sp 48]
      u.mem t.mem := by simpa only [K, restU.sp] using frameT
  have contextT := contextU.after_arithmetic (calls.after restU) localFrame restT ready.ptr
    (fun d hd => (stableSlots_at stable hd).1)
  have frame : Frame (domainPrepareWrites p s) s.mem t.mem :=
    (frameU.mono (by intro r hr; simp only [domainPrepareWrites, prepareAtWrites, List.mem_append,
      List.mem_cons]; exact Or.inl (Or.inr hr))).trans
      (frameT.mono (by
        intro r hr
        simp only [List.mem_cons] at hr
        simp only [domainPrepareWrites, prepareAtWrites, List.mem_append, List.mem_cons]
        rcases hr with hr | hr
        · exact Or.inl (Or.inl hr)
        · exact Or.inr hr))
  exact ⟨contextT, ready, modulus, r2, frame,
    (restU.mono (by simp [roundClobbers])).trans restT⟩

end VG.Proof.Ffdh.Arm
