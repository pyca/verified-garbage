module

public import VerifiedGarbage.Impl.Ffdh.Arm.SampleScalar
public import VerifiedGarbage.Proof.Ffdh.Arm.EnvironmentBoundLaw
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyScalar
import VerifiedGarbage.Proof.Ffdh.Arm.SampleScalarArgs
import VerifiedGarbage.Proof.Ffdh.Arm.SampleCut
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Ffdh.Arm.ScalarLayout

/-! A public sampling bound drives the existing fixed byte-cutting instructions. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem environmentScalar_ok (env : SampleEnvironment) (layout : (p : Inputs) → ScalarLayout p) (bound : Prog isa)
    (law : EnvironmentBoundLaw env layout bound) (s : State) {p : Inputs} {slots : List Nat} {rb : List Byte}
    (h : Context p slots s) (environment : env.holds p s)
    (normalized : 2 ^ (64 * (p.w - 1)) ≤ p.P) (odd : p.P % 2 = 1) (stable : stableSlots slots = true) (special : sampleSlots slots)
    (h52 : 52 ∈ slots) (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h28 : 28 ∈ slots) (h32 : 32 ∈ slots)
    (h40 : 40 ∈ slots) (h48 : 48 ∈ slots) (h60 : 60 ∈ slots)
    (entropy : Octets p.base p.entropy p.len rb s) (size : rb.length = p.k)
    (entropyStack : Region.Disjoint ⟨State.addr p.entropy, p.k⟩ ⟨State.addr s.sp, 72⟩)
    (output : OutputBuffer p.privateValue p.k s)
    (domainSep : Region.Disjoint ⟨State.addr p.domain, p.dom.length⟩ ⟨State.addr p.privateValue, p.k⟩)
    (stackSep : Region.Disjoint ⟨State.addr s.sp, 72⟩ ⟨State.addr p.privateValue, p.k⟩)
    (entropySep : Region.Disjoint ⟨State.addr p.entropy, p.k⟩ ⟨State.addr p.privateValue, p.k⟩) :
    WP isa (VG.Impl.Ffdh.Arm.SampleScalar.code bound) s fun t =>
      SampleContext p (layout p) slots t ∧ Octets p.base p.entropy p.len rb t ∧
      Spec.Rsa.bytesAt t.mem (State.addr p.privateValue) p.k = (layout p).encode rb ∧
      Frame (keyScalarWrites p s) s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [VG.Impl.Ffdh.Arm.SampleScalar.code, WP.seq_iff]
  refine WP.mono (law.correct s h environment normalized odd stable special h52 h24 h28 h32 h60) ?_
  rintro u ⟨contextU, widthU, maskU, frameU, restU⟩
  have entropyU := entropy.after_frame frameU restU (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [size]
    rcases hr with rfl | rfl <;> exact entropyStack.sub_right (Offset.sub_base _ (by decide)))
  rw [WP.seq_iff]
  refine WP.mono (sampleScalarArgs_retained u contextU stable special widthU maskU h32 h40 h48) ?_
  rintro v ⟨contextV, dstV, srcV, countV, zeroV, frameV, restV⟩
  have entropyV := entropyU.after_frame frameV restV (by
    intro r hr
    rw [List.mem_singleton] at hr
    subst r
    rw [size, restU.sp]
    exact entropyStack.sub_right (Offset.sub_base _ (by decide)))
  rw [WP.seq_iff]
  refine WP.mono (sampleCut_ok v contextV (fun d hd => (stableSlots_at stable hd).1)
    entropyV size ((output.after restU).after restV) domainSep (by rw [restV.sp, restU.sp]; exact stackSep)
    entropySep srcV dstV countV zeroV) ?_
  rintro w ⟨contextW, entropyW, bytesW, frameW, restW⟩
  refine WP.mono (localLoad_ok w .r0 contextW.locals (by decide : 0 + 4 ≤ 72)) ?_
  rintro t ⟨loaded, memT, restT⟩
  have ptr : t.gpr .r0 = p.base := loaded.trans (contextW.saved 0 h0)
  have memFrame : Frame [] w.mem t.mem := by rw [memT]; exact Frame.refl _ _
  have args := contextW.toArgumentMemory.after_frame memFrame restT (by simp) (by simp)
  have contextT : SampleContext p (layout p) slots t := by
    refine ⟨⟨args, ptr⟩, ?_, ?_, ?_⟩
    · rw [memT, restT.sp]; exact contextW.scalarStart
    · rw [memT, restT.sp]; exact contextW.scalarWidth
    · rw [memT, restT.sp]; exact contextW.scalarMask
  have entropyT := entropyW.after_frame memFrame restT (by simp)
  have fullU : Frame (keyScalarWrites p s) s.mem u.mem := frameU.mono (by simp [keyScalarWrites])
  have fullV : Frame (keyScalarWrites p s) u.mem v.mem := by
    rw [restU.sp] at frameV
    exact frameV.mono (by simp [keyScalarWrites])
  have fullW : Frame (keyScalarWrites p s) v.mem w.mem := frameW.mono (by simp [keyScalarWrites])
  refine ⟨contextT, entropyT, by rw [memT]; exact bytesW, ?_, ?_⟩
  · rw [memT]
    exact (fullU.trans fullV).trans fullW
  · exact restU.trans ((restV.mono (by simp [roundClobbers])).trans
      ((restW.mono (by simp [roundClobbers])).trans (restT.mono (by simp [roundClobbers]))))

end VG.Proof.Ffdh.Arm
