module

public import VerifiedGarbage.Proof.Ffdh.Arm.ExchangeMain
public import VerifiedGarbage.Proof.Ffdh.Arm.SharedExchangeMemory
public import VerifiedGarbage.Impl.Ffdh.Arm.SharedDerive
public import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
import VerifiedGarbage.Proof.Ffdh.Arm.SharedCheckPublicPower
import VerifiedGarbage.Proof.Ffdh.Arm.Range
import VerifiedGarbage.Proof.Ffdh.Arm.Branch
import VerifiedGarbage.Proof.Ffdh.Arm.Block
public import VerifiedGarbage.Proof.Ffdh.Arm.MaskOutput
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! The derivation's two paths after the scalar test: `g^x mod p`, its range,
export and `3 − 2 flag`; or zeros and 2. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.SharedDerive
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt Operand)
open VG.Proof.X25519.Arm (Rest)

/-- The generator's octets. -/
def gOctets (p : Inputs) : List Byte := (p.dom.drop p.k).take p.k

theorem status_ok (s : State) (b : Bool) (flag : s.gpr .r0 = if b then 1 else 0) :
    WP isa (.block VG.Impl.Ffdh.Arm.SharedDerive.status) s fun t =>
      (t.gpr .r0 = (if b then 1 else 3) ∧ t.mem = s.mem) ∧ Rest [.r0, .r3] s t := by
  refine withRest_all [.r0, .r3] ?_ (by rfl) (by rfl)
  unfold VG.Impl.Ffdh.Arm.SharedDerive.status
  ffrun [flag]
  cases b <;> rfl

theorem tail_ok (backend : MontBackend) (s : State) {p : Inputs} {slots : List Nat} {xb : List Byte}
    (h : Context p slots s) (calls : SharedExchange.CallMemory p xb.length s) (stable : stableSlots slots = true)
    (h4 : 4 ∈ slots) (h32 : 32 ∈ slots) (h40 : 40 ∈ slots) (h44 : 44 ∈ slots) (h56 : 56 ∈ slots)
    (saved : ∀ d ∈ slots, d + 4 ≤ 64 ∨ 68 ≤ d) (odd : p.P % 2 = 1)
    (ready : ArithmeticReady p.base p.len p.w s)
    (modulus : numAt s.mem (State.addr p.base) p.w 0 = p.P)
    (r2 : numAt s.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % p.P)
    (scalar : Octets p.base p.privateValue p.len xb s) (positive : 0 < xb.length) (scalarFit : xb.length < 2 ^ 32)
    (scalarCount : p.slotValue 44 = BitVec.ofNat 32 xb.length)
    (output : OutputBuffer p.output p.k s)
    (workspaceSep : Region.Disjoint ⟨State.addr p.base, 8 * p.len⟩ ⟨State.addr p.output, p.k⟩)
    (stackSep : Region.Disjoint ⟨State.addr s.sp, 72⟩ ⟨State.addr p.output, p.k⟩) :
    WP isa (VG.Impl.Ffdh.Arm.SharedDerive.tail (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul)) s
      fun t => t.gpr .r0 = (if sharedAccepted p (gOctets p) xb then 1 else 3) ∧
        Spec.Rsa.bytesAt t.mem (State.addr p.output) p.k =
          (if sharedAccepted p (gOctets p) xb then Spec.Rsa.i2osp (sharedValue p (gOctets p) xb) p.k
            else List.replicate p.k 0) ∧
        Frame (SharedExchange.writes p s) s.mem t.mem := by
  have op6 : Operand 6 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  rw [VG.Impl.Ffdh.Arm.SharedDerive.tail, WP.seq_iff]
  refine WP.mono (sharedCheckPublicPower_ok backend s 56 40 44 h calls.toDomainCallMemory stable h56 h40 h44 h32
    ready modulus odd r2 h.gBytes p.gLength scalar positive scalarFit scalarCount calls.scalarBelow) ?_
  rintro v ⟨contextV, readyV, power, modV, _, _, frameV, restV⟩
  rw [WP.seq_iff]
  refine WP.mono (inRange_ok v readyV op6 (by decide) (by rw [modV]; exact odd)) ?_
  rintro w ⟨readyW, flag, arraysW, frameW, restW⟩
  have contextW := contextV.after_workspace frameW restW readyW.ptr (fun d hd => (stableSlots_at stable hd).1)
  have valueW := (arraysW 6 op6 (by decide)).trans power
  have flagW : w.gpr .r11 = if sharedAccepted p (gOctets p) xb then 1 else 0 := by
    rw [power, modV] at flag
    change w.gpr .r11 = if decide (1 < sharedValue p (gOctets p) xb ∧
      sharedValue p (gOctets p) xb < p.P - 1) = true then 1 else 0
    change w.gpr .r11 = (if 1 < sharedValue p (gOctets p) xb ∧
      sharedValue p (gOctets p) xb < p.P - 1 then 1 else 0) at flag
    simpa only [decide_eq_true_eq] using flag
  have valueFit : numAt w.mem (State.addr p.base) p.w 6 < 2 ^ (8 * p.k) := by
    rw [valueW, VG.Proof.Bignum.powMod_eq]
    exact Nat.lt_trans (Nat.mod_lt _ (by omega : 0 < p.P)) p.modulusBound
  rw [WP.seq_iff]
  refine WP.mono (exchangeFinish_ok w (sharedAccepted p (gOctets p) xb) contextW stable h4 h32 saved readyW
    ((output.after restV).after restW) workspaceSep
    (by rw [restW.sp, restV.sp]; exact stackSep) valueFit flagW) ?_
  rintro u ⟨result, bytes, frameU, restU⟩
  rw [valueW] at bytes
  refine WP.mono (status_ok u _ result) ?_
  rintro t ⟨⟨status, memT⟩, _⟩
  refine ⟨status, by rw [memT]; exact bytes, ?_⟩
  have fV : Frame (SharedExchange.writes p s) s.mem v.mem :=
    frameV.mono (by simp [SharedExchange.writes, exchangeWrites])
  have fW : Frame (SharedExchange.writes p s) v.mem w.mem :=
    frameW.mono (by simp [SharedExchange.writes, exchangeWrites])
  have fU : Frame (SharedExchange.writes p s) w.mem u.mem := by
    have localFrame := frameU.mono
      (by simp [SharedExchange.writes, exchangeWrites] : ∀ r ∈ exchangeWrites p w, r ∈ SharedExchange.writes p w)
    simpa only [SharedExchange.writes, exchangeWrites, restW.sp, restV.sp] using localFrame
  rw [memT]
  exact (fV.trans fW).trans fU

/-- The saved flag and the output's arguments, for masking. -/
theorem failSave_ok (s : State) {p : Inputs} {slots : List Nat}
    (h : Context p slots s) (h4 : 4 ∈ slots) (h32 : 32 ∈ slots)
    (output : OutputBuffer p.output p.k s)
    (stackSep : Region.Disjoint ⟨State.addr s.sp, 72⟩ ⟨State.addr p.output, p.k⟩) :
    WP isa (.block VG.Impl.Ffdh.Arm.Domain.Exchange.saveResult) s fun u =>
      MaskOutputInput p (s.gpr .r11) u ∧ Frame [⟨State.addr s.sp, 72⟩] s.mem u.mem := by
  refine WP.mono (saveResult_ok s h.locals) ?_
  rintro u ⟨⟨_, result, frameU⟩, restU⟩
  have word (d : Nat) (hd : d + 4 ≤ 64) :
      u.mem.readW (off (State.addr s.sp) d) 32 = s.mem.readW (off (State.addr s.sp) d) 32 :=
    frameU.readW (w := 32) (r := ⟨off (State.addr s.sp) d, 4⟩) (Region.contains_self _ _) (by
      intro r hr
      rw [List.mem_singleton] at hr
      subst r
      exact Offset.disjoint _ (Or.inl hd) (by have := h.locals.space.nowrap; omega)
        (by have := h.locals.space.nowrap; omega)) (by decide)
  refine ⟨⟨h.locals.after restU, output.after restU, by rw [restU.sp]; exact stackSep, ?_, ?_, ?_⟩, ?_⟩
  · rw [restU.sp, word 4 (by decide)]; exact h.saved 4 h4
  · rw [restU.sp, word 32 (by decide)]; exact h.saved 32 h32
  · rw [restU.sp, result]
  · refine frameU.sub ?_
    intro r hr
    rw [List.mem_singleton] at hr
    subst r
    exact ⟨⟨State.addr s.sp, 72⟩, by simp, Offset.sub_base _ (by decide)⟩

theorem fail_ok (s : State) {p : Inputs} {slots : List Nat}
    (h : Context p slots s) (h4 : 4 ∈ slots) (h32 : 32 ∈ slots) (flag : s.gpr .r11 = 0)
    (output : OutputBuffer p.output p.k s)
    (stackSep : Region.Disjoint ⟨State.addr s.sp, 72⟩ ⟨State.addr p.output, p.k⟩) :
    WP isa VG.Impl.Ffdh.Arm.SharedDerive.fail s fun t => t.gpr .r0 = 2 ∧
      Spec.Rsa.bytesAt t.mem (State.addr p.output) p.k = List.replicate p.k 0 ∧
      Frame [⟨State.addr s.sp, 72⟩, ⟨State.addr p.output, p.k⟩] s.mem t.mem := by
  rw [VG.Impl.Ffdh.Arm.SharedDerive.fail, WP.seq_iff]
  refine WP.mono (failSave_ok s h h4 h32 output stackSep) ?_
  rintro u ⟨input, frameU⟩
  rw [flag] at input
  rw [WP.seq_iff]
  refine WP.mono (maskOutput_ok u input) ?_
  rintro v ⟨_, bytes, frameV, _⟩
  refine WP.mono (ret_ok v 2 (by decide)) ?_
  rintro t ⟨⟨status, memT⟩, _⟩
  refine ⟨status, ?_, ?_⟩
  · rw [memT, bytes]
    change ((Spec.Rsa.bytesAt u.mem (State.addr p.output) p.k).map (· &&& 0#8)) = _
    simp only [BitVec.and_zero, List.map_const', Spec.Rsa.bytesAt, List.length_map, List.length_range]
    rfl
  · rw [memT]
    exact (frameU.mono (by simp)).trans (frameV.mono (by simp))

end VG.Proof.Ffdh.Arm.SharedDerive
