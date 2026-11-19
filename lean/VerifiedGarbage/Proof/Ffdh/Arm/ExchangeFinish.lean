module

public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack
import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticExternal
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Ffdh.Arm.Output
public import VerifiedGarbage.Impl.Ffdh.Arm.Domain
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Bignum.Arm.ExportBE
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Proof.Ffdh.Arm.Context
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
import VerifiedGarbage.Proof.Bignum.Arm.MaskBuffer
import VerifiedGarbage.Proof.Bignum.Arm.Stack

/-! ### `Ffdh.Arm.MaskOutput`, which this module and modules that import it used -/

section

/-! Mask the full shared-value encoding and reload the saved status without branching. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

structure MaskOutputInput (p : Inputs) (flag : BitVec 32) (s : State) : Prop where
  locals : Locals p.base p.len s
  output : OutputBuffer p.output p.k s
  separate : Region.Disjoint ⟨State.addr s.sp, 72⟩ ⟨State.addr p.output, p.k⟩
  dst : s.mem.readW (off (State.addr s.sp) 4) 32 = p.output
  count : s.mem.readW (off (State.addr s.sp) 32) 32 = BitVec.ofNat 32 p.k
  result : s.mem.readW (off (State.addr s.sp) 64) 32 = flag

theorem maskOutputArgs_ok (s : State) {p : Inputs} {flag : BitVec 32} (h : MaskOutputInput p flag s) :
    WP isa (.block [.ldrSp .r0 4, .ldrSp .lr 32, .ldrSp .r2 64,
      .mov .r3 (.imm 0), .dp .sub .r2 .r3 (.reg .r2)]) s fun t =>
      (t.gpr .r0 = p.output ∧ t.gpr .lr = BitVec.ofNat 32 p.k ∧ t.gpr .r2 = 0 - flag ∧ t.mem = s.mem) ∧
      Rest [.r0, .r2, .r3, .lr] s t := by
  have addr (d : Nat) (hd : d + 4 ≤ 72) :
      State.addr (s.sp + BitVec.ofNat 32 d) = off (State.addr s.sp) d :=
    VG.Arm.addr_add (by have := h.locals.space.nowrap; omega_using [hd, this])
  have r4 := h.locals.read (d := 4) (by decide)
  have r32 := h.locals.read (d := 32) (by decide)
  have r64 := h.locals.read (d := 64) (by decide)
  refine withRest_all [.r0, .r2, .r3, .lr] ?_ (by rfl) (by rfl)
  ffrun [addr 4 (by decide), addr 32 (by decide), addr 64 (by decide), r4, r32, r64,
    h.dst, h.count, h.result, off]

theorem maskOutput_ok (s : State) {p : Inputs} {flag : BitVec 32} (h : MaskOutputInput p flag s) :
    WP isa VG.Impl.Ffdh.Arm.Domain.Exchange.maskOutput s fun t =>
      t.gpr .r0 = flag ∧ Spec.Rsa.bytesAt t.mem (State.addr p.output) p.k =
        (Spec.Rsa.bytesAt s.mem (State.addr p.output) p.k).map (· &&& (0 - flag).setWidth 8) ∧
      Frame [⟨State.addr p.output, p.k⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [VG.Impl.Ffdh.Arm.Domain.Exchange.maskOutput, WP.seq_iff]
  refine WP.mono (maskOutputArgs_ok s h) ?_
  rintro u ⟨⟨ptr, count, mask, memU⟩, restU⟩
  rw [WP.seq_iff]
  refine WP.mono (maskBuffer_ok u (by have := p.minLength; omega_using [this]) (by have := p.maxLength; omega_using [this])
    h.output.fits (by rw [restU.wr]; exact h.output.writable) ptr count) ?_
  rintro v ⟨bytes, frameV, restV⟩
  have rest : Rest roundClobbers s v := (restU.mono (by simp [roundClobbers])).trans
    (restV.mono (by simp [roundClobbers]))
  have localV := h.locals.after rest
  have addr : State.addr (v.sp + BitVec.ofNat 32 64) = off (State.addr v.sp) 64 :=
    VG.Arm.addr_add (by have := localV.space.nowrap; omega_using [this])
  have kept := frameV.readW (w := 32) (r := ⟨off (State.addr s.sp) 64, 4⟩) (Region.contains_self _ _) (by
    intro r hr
    rw [List.mem_singleton] at hr
    subst r
    exact h.separate.sub_left (Offset.sub_base _ (by decide))) (by decide)
  refine wp_loadStack (a := off (State.addr v.sp) 64) (by decide) addr (localV.read (d := 64) (by decide)) fun t loaded => WP.block_nil ?_
  have finalRest : Rest roundClobbers s t := (rest.mono (by simp [roundClobbers])).trans
    ((loaded.rest (by simp : Reg.r0 ∈ [.r0])).mono (by simp [roundClobbers]))
  refine ⟨?_, ?_, ?_, finalRest⟩
  · rw [loaded.gpr, rest.sp, kept, memU]
    exact h.result
  · rw [mask, memU] at bytes
    rw [loaded.mem]
    exact bytes
  · rw [memU] at frameV
    rw [loaded.mem]
    exact frameV

end VG.Proof.Ffdh.Arm

end

end

/-! ### `Ffdh.Arm.ExportResult`, which this module and modules that import it used -/

section

/-! Export a shared value through the saved output pointer, at the full modulus width. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

theorem exportResultArgs_ok (s : State) {p : Inputs} {slots : List Nat}
    (h : Context p slots s) (h4 : 4 ∈ slots) (h32 : 32 ∈ slots) :
    WP isa (.block [.mov .r2 (.imm 6), .ldrSp .r4 4, .ldrSp .r6 32]) s fun t =>
      (t.gpr .r2 = 6 ∧ t.gpr .r4 = p.output ∧ t.gpr .r6 = BitVec.ofNat 32 p.k ∧ t.mem = s.mem) ∧
      Rest [.r2, .r4, .r6] s t := by
  have addr (d : Nat) (hd : d + 4 ≤ 72) :
      State.addr (s.sp + BitVec.ofNat 32 d) = off (State.addr s.sp) d :=
    VG.Arm.addr_add (by have := h.locals.space.nowrap; omega_using [hd, this])
  have r4 := h.locals.read (d := 4) (by decide)
  have r32 := h.locals.read (d := 32) (by decide)
  have v4 := h.saved 4 h4
  have v32 := h.saved 32 h32
  refine withRest_all [.r2, .r4, .r6] ?_ (by rfl) (by rfl)
  ffrun [addr 4 (by decide), addr 32 (by decide), r4, r32, v4, v32, Inputs.slotValue, off]

theorem exportResult_ok (s : State) {p : Inputs} {slots : List Nat}
    (h : Context p slots s) (h4 : 4 ∈ slots) (h32 : 32 ∈ slots)
    (ready : ArithmeticReady p.base p.len p.w s)
    (output : OutputBuffer p.output p.k s)
    (separate : Region.Disjoint ⟨State.addr p.base, 8 * p.len⟩ ⟨State.addr p.output, p.k⟩)
    (valueFit : numAt s.mem (State.addr p.base) p.w 6 < 2 ^ (8 * p.k)) :
    WP isa VG.Impl.Ffdh.Arm.Domain.Exchange.exportResult s fun t =>
      Spec.Rsa.bytesAt t.mem (State.addr p.output) p.k =
        Spec.Rsa.i2osp (numAt s.mem (State.addr p.base) p.w 6) p.k ∧
      Frame [⟨State.addr p.output, p.k⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [VG.Impl.Ffdh.Arm.Domain.Exchange.exportResult, WP.seq_iff]
  refine WP.mono (exportResultArgs_ok s h h4 h32) ?_
  rintro u ⟨⟨index, dst, count, mem⟩, rest⟩
  have readyU := ready.of_mem mem rest ((rest.gpr .r0 (by simp)).trans ready.ptr)
  refine WP.mono (exportBE_ok u readyU.workspace readyU.layout readyU.width (by decide : 6 < 8)
    (by have := p.minLength; omega_using [this]) p.width.2.2.2.1 (by rw [mem]; exact valueFit) output.fits
    (by rw [rest.wr]; exact output.writable) separate readyU.ptr index dst count) ?_
  rintro t ⟨value, frame, _, _, restT⟩
  rw [mem] at value frame
  exact ⟨value, frame, (rest.mono (by simp [roundClobbers])).trans (restT.mono (by simp [roundClobbers]))⟩

end VG.Proof.Ffdh.Arm

end

end

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
