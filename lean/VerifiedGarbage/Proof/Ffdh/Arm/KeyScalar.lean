module

public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
import VerifiedGarbage.Proof.Ffdh.Arm.KeyBound
import VerifiedGarbage.Proof.Ffdh.Arm.KeyScalarArgs
import VerifiedGarbage.Proof.Ffdh.Arm.KeyCut
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Ffdh.Arm.GenerateKey
public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack
public import VerifiedGarbage.Proof.Ffdh.Arm.Output
public import VerifiedGarbage.TCB.Arm.Isa

/-! The complete native scalar sampler preserves arithmetic storage and the
saved workspace pointer while deriving the shared scalar encoding. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

def keyScalarWrites (p : Inputs) (s : State) : List Region :=
  [⟨off (State.addr s.sp) 20, 4⟩, ⟨off (State.addr s.sp) 68, 4⟩,
    ⟨off (State.addr s.sp) 16, 4⟩, ⟨State.addr p.privateValue, p.k⟩]

theorem keyScalar_ok (s : State) {p : Inputs} {slots : List Nat} {rb : List Byte}
    (h : Context p slots s) (stable : stableSlots slots = true)
    (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h28 : 28 ∈ slots) (h32 : 32 ∈ slots)
    (h40 : 40 ∈ slots) (h48 : 48 ∈ slots) (h60 : 60 ∈ slots)
    (entropy : Octets p.base p.entropy p.len rb s) (size : rb.length = p.k)
    (entropyStack : Region.Disjoint ⟨State.addr p.entropy, p.k⟩ ⟨State.addr s.sp, 72⟩)
    (output : OutputBuffer p.privateValue p.k s)
    (domainSep : Region.Disjoint ⟨State.addr p.domain, p.dom.length⟩ ⟨State.addr p.privateValue, p.k⟩)
    (stackSep : Region.Disjoint ⟨State.addr s.sp, 72⟩ ⟨State.addr p.privateValue, p.k⟩)
    (entropySep : Region.Disjoint ⟨State.addr p.entropy, p.k⟩ ⟨State.addr p.privateValue, p.k⟩) :
    WP isa VG.Impl.Ffdh.Arm.Domain.GenerateKey.scalar s fun t =>
      Context p (16 :: 68 :: 20 :: slots) t ∧ Octets p.base p.entropy p.len rb t ∧
      Spec.Rsa.bytesAt t.mem (State.addr p.privateValue) p.k =
        VG.Proof.Ffdh.KeyScalar.cut rb p.scalarLead (p.scalarMask.setWidth 8) ∧
      Frame (keyScalarWrites p s) s.mem t.mem ∧ Rest VG.Proof.Bignum.Arm.roundClobbers s t := by
  rw [VG.Impl.Ffdh.Arm.Domain.GenerateKey.scalar, WP.seq_iff]
  refine WP.mono (keyBound_ok s h stable h24 h28 h32 h60) ?_
  rintro u ⟨⟨contextU, frameU⟩, restU⟩
  have stableU : stableSlots (68 :: 20 :: slots) = true := by
    change (true && (true && stableSlots slots)) = true
    rw [Bool.true_and, Bool.true_and, stable]
  have entropyU := entropy.after_frame frameU restU (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [size]
    rcases hr with rfl | rfl <;> exact entropyStack.sub_right (Offset.sub_base _ (by decide)))
  rw [WP.seq_iff]
  refine WP.mono (keyScalarArgs_retained u contextU stableU (by simp) (by simp [h32]) (by simp [h40]) (by simp [h48])) ?_
  rintro v ⟨contextV, dstV, srcV, countV, zeroV, frameV, restV⟩
  have stableV : stableSlots (16 :: 68 :: 20 :: slots) = true := by
    change (true && stableSlots (68 :: 20 :: slots)) = true
    rw [Bool.true_and, stableU]
  have entropyV := entropyU.after_frame frameV restV (by
    intro r hr
    rw [List.mem_singleton] at hr
    subst r
    rw [size, restU.sp]
    exact entropyStack.sub_right (Offset.sub_base _ (by decide)))
  rw [WP.seq_iff]
  refine WP.mono (keyCut_ok v contextV (fun d hd => (stableSlots_at stableV hd).1) (by simp) (by simp)
    entropyV size ((output.after restU).after restV) domainSep (by rw [restV.sp, restU.sp]; exact stackSep)
    entropySep srcV dstV countV zeroV) ?_
  rintro w ⟨contextW, entropyW, bytesW, frameW, restW⟩
  refine WP.mono (localLoad_ok w .r0 contextW.locals (by decide : 0 + 4 ≤ 72)) ?_
  rintro t ⟨loaded, memT, restT⟩
  have ptr : t.gpr .r0 = p.base := loaded.trans (contextW.saved 0 (by simp [h0]))
  have memFrame : Frame [] w.mem t.mem := by rw [memT]; exact Frame.refl _ _
  have contextT : Context p (16 :: 68 :: 20 :: slots) t :=
    ⟨contextW.after_frame memFrame restT (by simp) (by simp), ptr⟩
  have entropyT := entropyW.after_frame memFrame restT (by simp)
  have fullU : Frame (keyScalarWrites p s) s.mem u.mem := frameU.mono (by simp [keyScalarWrites])
  have fullV : Frame (keyScalarWrites p s) u.mem v.mem := by
    rw [restU.sp] at frameV
    exact frameV.mono (by simp [keyScalarWrites])
  have fullW : Frame (keyScalarWrites p s) v.mem w.mem := frameW.mono (by simp [keyScalarWrites])
  refine ⟨contextT, entropyT, by rw [memT]; exact bytesW, ?_, ?_⟩
  · rw [memT]
    exact (fullU.trans fullV).trans fullW
  · exact (((restU.mono (by simp [VG.Proof.Bignum.Arm.roundClobbers])).trans
      (restV.mono (by simp [VG.Proof.Bignum.Arm.roundClobbers]))).trans
      (restW.mono (by simp [VG.Proof.Bignum.Arm.roundClobbers]))).trans
      (restT.mono (by simp [VG.Proof.Bignum.Arm.roundClobbers]))

end VG.Proof.Ffdh.Arm
