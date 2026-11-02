module

public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
import VerifiedGarbage.Proof.Ffdh.Arm.ExportResult
import VerifiedGarbage.Proof.Ffdh.Arm.MaskOutput
public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack
import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticExternal
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Ffdh.Arm.Output
public import VerifiedGarbage.Impl.Ffdh.Arm.Domain

/-! Shared-value export and masking keep every status-dependent operation native. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt numAt)
open VG.Proof.X25519.Arm (Rest)

def exchangeWrites (p : Inputs) (s : State) : List Region :=
  [⟨State.addr p.base, 8 * p.len⟩, ⟨State.addr s.sp, 72⟩, ⟨State.addr p.output, p.k⟩]

theorem exchangeFinish_ok (s : State) {p : Inputs} {slots : List Nat} (accepted : Bool)
    (h : Context p slots s) (stable : stableSlots slots = true) (h4 : 4 ∈ slots) (h32 : 32 ∈ slots)
    (saved : ∀ d ∈ slots, d + 4 ≤ 64 ∨ 68 ≤ d)
    (ready : ArithmeticReady p.base p.len p.w s) (output : OutputBuffer p.output p.k s)
    (workspaceSep : Region.Disjoint ⟨State.addr p.base, 8 * p.len⟩ ⟨State.addr p.output, p.k⟩)
    (stackSep : Region.Disjoint ⟨State.addr s.sp, 72⟩ ⟨State.addr p.output, p.k⟩)
    (valueFit : numAt s.mem (State.addr p.base) p.w 6 < 2 ^ (8 * p.k))
    (flag : s.gpr .r11 = if accepted then 1 else 0) :
    WP isa (.seq (.block VG.Impl.Ffdh.Arm.Domain.Exchange.saveResult)
      (.seq VG.Impl.Ffdh.Arm.Domain.Exchange.exportResult VG.Impl.Ffdh.Arm.Domain.Exchange.maskOutput)) s fun t =>
      t.gpr .r0 = (if accepted then 1 else 0) ∧ Spec.Rsa.bytesAt t.mem (State.addr p.output) p.k =
        (if accepted then Spec.Rsa.i2osp (numAt s.mem (State.addr p.base) p.w 6) p.k else List.replicate p.k 0) ∧
      Frame (exchangeWrites p s) s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [WP.seq_iff]
  refine WP.mono (saveResult_ok s h.locals) ?_
  rintro u ⟨⟨_, result, frameU⟩, restU⟩
  have ptrU := (restU.gpr .r0 (by simp)).trans h.ptr
  have contextU := h.after_local (by decide : 64 + 4 ≤ 72) frameU restU ptrU (fun d hd => (stableSlots_at stable hd).1) saved
  have readyU := ready.after_external frameU (by
    intro r hr
    rw [List.mem_singleton] at hr
    subst r
    exact h.locals.separate.symm.sub_right (Offset.sub_base _ (by decide))) (by
    intro r hr
    rw [List.mem_singleton] at hr
    subst r
    simpa only [off, BitVec.add_zero] using
      (Offset.disjoint (State.addr s.sp) (d := 0) (n := 4) (e := 64) (k := 4) (by left; decide) (by decide) (by decide))) restU ptrU
  have fits : arrAt p.w 8 ≤ 8 * p.len := ready.width ▸ ready.layout.2.2.1
  have valueU := readyU.2.number fits (by decide : 6 < 8)
  rw [WP.seq_iff]
  refine WP.mono (exportResult_ok u contextU h4 h32 readyU.1 (output.after restU) workspaceSep
    (by rw [valueU]; exact valueFit)) ?_
  rintro v ⟨bytesV, frameV, restV⟩
  have restUV := (restU.mono (by simp [roundClobbers])).trans restV
  have localsV := h.locals.after restUV
  have word (d : Nat) (hd : d + 4 ≤ 72) :
      v.mem.readW (off (State.addr s.sp) d) 32 = u.mem.readW (off (State.addr s.sp) d) 32 :=
    frameV.readW (w := 32) (r := ⟨off (State.addr s.sp) d, 4⟩) (Region.contains_self _ _) (by
      intro r hr
      rw [List.mem_singleton] at hr
      subst r
      exact stackSep.sub_left (Offset.sub_base _ hd)) (by decide)
  have maskInput : MaskOutputInput p (if accepted then 1 else 0) v := by
    refine ⟨localsV, (output.after restUV), by rw [restUV.sp]; exact stackSep, ?_, ?_, ?_⟩
    · rw [restUV.sp, word 4 (by decide), ← restU.sp]
      exact contextU.saved 4 h4
    · rw [restUV.sp, word 32 (by decide), ← restU.sp]
      exact contextU.saved 32 h32
    · rw [restUV.sp, word 64 (by decide), result, flag]
  refine WP.mono (maskOutput_ok v maskInput) ?_
  rintro t ⟨resultT, bytesT, frameT, restT⟩
  rw [bytesV, valueU] at bytesT
  refine ⟨resultT, ?_, ?_, restUV.trans restT⟩
  · cases accepted
    · change Spec.Rsa.bytesAt t.mem (State.addr p.output) p.k = List.replicate p.k (0#8)
      simpa only [Bool.false_eq_true, ite_false, BitVec.sub_self, BitVec.setWidth_zero, BitVec.and_zero,
        List.map_const', Spec.Rsa.i2osp, List.length_map, List.length_range] using bytesT
    · change Spec.Rsa.bytesAt t.mem (State.addr p.output) p.k =
        Spec.Rsa.i2osp (numAt s.mem (State.addr p.base) p.w 6) p.k
      change Spec.Rsa.bytesAt t.mem (State.addr p.output) p.k =
        (Spec.Rsa.i2osp (numAt s.mem (State.addr p.base) p.w 6) p.k).map (· &&& BitVec.allOnes 8) at bytesT
      simpa only [BitVec.and_allOnes, List.map_id'] using bytesT
  · have entryFrame : Frame (exchangeWrites p s) s.mem u.mem := frameU.sub (by
      intro r hr
      rw [List.mem_singleton] at hr
      subst r
      exact ⟨⟨State.addr s.sp, 72⟩, by simp [exchangeWrites], Offset.sub_base _ (by decide)⟩)
    exact entryFrame.trans ((frameV.trans frameT).mono (by
      intro r hr
      rw [List.mem_singleton] at hr
      subst r
      simp [exchangeWrites]))

end VG.Proof.Ffdh.Arm
