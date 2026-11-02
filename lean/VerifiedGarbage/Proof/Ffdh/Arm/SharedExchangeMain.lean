module

public import VerifiedGarbage.Proof.Ffdh.Arm.ExchangeMain
public import VerifiedGarbage.Proof.Ffdh.Arm.SharedExchangeMemory
public import VerifiedGarbage.Impl.Ffdh.Arm.SharedExchange
import VerifiedGarbage.Proof.Ffdh.Arm.DomainNormalizedPrepareAt
import VerifiedGarbage.Proof.Ffdh.Arm.SharedCheckPublicPower
import VerifiedGarbage.Proof.Ffdh.Arm.PowerAt
import VerifiedGarbage.Proof.Ffdh.Arm.Range
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack
public import VerifiedGarbage.Impl.Ffdh.Arm.Checks
public import VerifiedGarbage.Impl.Ffdh.Arm.NormalizedPrepare
public import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
public import VerifiedGarbage.Proof.Ffdh.Arm.Context
public import VerifiedGarbage.Impl.Ffdh.Arm.Checks
public import VerifiedGarbage.Proof.Ffdh.Arm.Context
public import VerifiedGarbage.Impl.Ffdh.Arm.SharedCheckPublic
public import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
public import VerifiedGarbage.Proof.Ffdh.Arm.Context

/-! Native shared-secret exponentiation, range checking, export, and rejection masking. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.SharedExchange
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt Operand)

theorem main_ok (backend : MontBackend) (s : State) {p : Inputs} {slots : List Nat} {yb xb : List Byte}
    (h : Context p slots s) (calls : CallMemory p xb.length s) (stable : stableSlots slots = true)
    (h0 : 0 ∈ slots) (h4 : 4 ∈ slots) (h24 : 24 ∈ slots) (h32 : 32 ∈ slots)
    (h36 : 36 ∈ slots) (h40 : 40 ∈ slots) (h44 : 44 ∈ slots)
    (saved : ∀ d ∈ slots, d + 4 ≤ 64 ∨ 68 ≤ d)
    (large : 1 < p.P) (odd : p.P % 2 = 1)
    (normalized : 2 ^ (64 * (p.w - 1)) ≤ p.P)
    (peer : Octets p.base p.publicValue p.len yb s) (peerLength : yb.length = p.k)
    (scalar : Octets p.base p.privateValue p.len xb s) (positive : 0 < xb.length) (scalarFit : xb.length < 2 ^ 32)
    (scalarCount : p.slotValue 44 = BitVec.ofNat 32 xb.length)
    (peerStack : Region.Disjoint ⟨State.addr p.publicValue, yb.length⟩ ⟨State.addr s.sp, 72⟩)
    (scalarStack : Region.Disjoint ⟨State.addr p.privateValue, xb.length⟩ ⟨State.addr s.sp, 72⟩)
    (output : OutputBuffer p.output p.k s)
    (workspaceSep : Region.Disjoint ⟨State.addr p.base, 8 * p.len⟩ ⟨State.addr p.output, p.k⟩)
    (stackSep : Region.Disjoint ⟨State.addr s.sp, 72⟩ ⟨State.addr p.output, p.k⟩) :
    WP isa (VG.Impl.Ffdh.Arm.SharedExchange.main (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul)) s fun t =>
      t.gpr .r0 = (if sharedAccepted p yb xb then 1 else 0) ∧
      Spec.Rsa.bytesAt t.mem (State.addr p.output) p.k =
        (if sharedAccepted p yb xb then Spec.Rsa.i2osp (sharedValue p yb xb) p.k else List.replicate p.k 0) ∧
      Frame (writes p s) s.mem t.mem := by
  have op0 : Operand 0 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op6 : Operand 6 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have extend {m m' : Mem} (f : Frame [⟨State.addr p.base, 8 * p.len⟩, FrameStack.belowA s.sp 48] m m') : Frame (writes p s) m m' :=
    f.mono (by simp [writes, exchangeWrites])
  rw [VG.Impl.Ffdh.Arm.SharedExchange.main, WP.seq_iff]
  refine WP.mono (domainNormalizedPrepareAt24_ok backend s h calls.toDomainCallMemory stable h0 h24 h32 large odd normalized) ?_
  rintro u ⟨contextU, readyU, modU, r2U, frameU, restU⟩
  have prepareSeparate {src : BitVec 32} {bs : List Byte}
      (octets : Octets p.base src p.len bs s)
      (stack : Region.Disjoint ⟨State.addr src, bs.length⟩ ⟨State.addr s.sp, 72⟩)
      (ifBelow : Region.Disjoint ⟨State.addr src, bs.length⟩ (FrameStack.belowA s.sp 48))
      (r : Region) (hr : r ∈ domainPrepareWrites p s) : (⟨State.addr src, bs.length⟩ : Region).Disjoint r := by
    simp only [domainPrepareWrites, prepareAtWrites, prepareWrites, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl | rfl) | rfl
    · exact octets.separate
    · exact stack.sub_right (Offset.sub_base _ (by decide))
    · exact stack.sub_right (Offset.sub_base _ (by decide))
    · exact ifBelow
  have peerU := peer.after_frame frameU restU (prepareSeparate peer peerStack (by rw [peerLength]; exact calls.publicValue))
  have scalarU := scalar.after_frame frameU restU (prepareSeparate scalar scalarStack calls.scalarBelow)
  rw [WP.seq_iff]
  refine WP.mono (sharedCheckPublicPower_ok backend u 36 40 44 contextU (calls.after restU).toDomainCallMemory stable h36 h40 h44 h32 readyU modU odd r2U
    peerU peerLength scalarU positive scalarFit scalarCount (by rw [restU.sp]; exact calls.scalarBelow)) ?_
  rintro v ⟨contextV, readyV, power, modV, _, _, frameV, restV⟩
  rw [WP.seq_iff]
  refine WP.mono (inRange_ok v readyV op6 (by decide) (by rw [modV]; exact odd)) ?_
  rintro w ⟨readyW, flag, arraysW, frameW, restW⟩
  have contextW := contextV.after_workspace frameW restW readyW.ptr (fun d hd => (stableSlots_at stable hd).1)
  have valueW := (arraysW 6 op6 (by decide)).trans power
  have flagW : w.gpr .r11 = if sharedAccepted p yb xb then 1 else 0 := by
    rw [power, modV] at flag
    change w.gpr .r11 = if decide (1 < sharedValue p yb xb ∧ sharedValue p yb xb < p.P - 1) = true then 1 else 0
    change w.gpr .r11 = (if 1 < sharedValue p yb xb ∧ sharedValue p yb xb < p.P - 1 then 1 else 0) at flag
    simpa only [decide_eq_true_eq] using flag
  have valueFit : numAt w.mem (State.addr p.base) p.w 6 < 2 ^ (8 * p.k) := by
    rw [valueW, VG.Proof.Bignum.powMod_eq]
    exact Nat.lt_trans (Nat.mod_lt _ (by omega : 0 < p.P)) p.modulusBound
  change WP isa (.seq (.block VG.Impl.Ffdh.Arm.Domain.Exchange.saveResult)
    (.seq VG.Impl.Ffdh.Arm.Domain.Exchange.exportResult VG.Impl.Ffdh.Arm.Domain.Exchange.maskOutput)) w _
  refine WP.mono (exchangeFinish_ok w (sharedAccepted p yb xb) contextW stable h4 h32 saved readyW
    (((output.after restU).after restV).after restW) workspaceSep
    (by rw [restW.sp, restV.sp, restU.sp]; exact stackSep) valueFit flagW) ?_
  rintro t ⟨status, bytes, frameT, _⟩
  rw [valueW] at bytes
  refine ⟨status, bytes, ?_⟩
  have fU : Frame (writes p s) s.mem u.mem := frameU.sub (by
    intro r hr
    simp only [domainPrepareWrites, prepareAtWrites, prepareWrites, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl | rfl) | rfl
    · exact ⟨⟨State.addr p.base, 8 * p.len⟩, by simp [writes, exchangeWrites], by intro a ha; exact ha⟩
    · exact ⟨⟨State.addr s.sp, 72⟩, by simp [writes, exchangeWrites], Offset.sub_base _ (by decide)⟩
    · exact ⟨⟨State.addr s.sp, 72⟩, by simp [writes, exchangeWrites], Offset.sub_base _ (by decide)⟩
    · exact ⟨FrameStack.belowA s.sp 48, by simp [writes], by intro a ha; exact ha⟩)
  have fT : Frame (writes p s) w.mem t.mem := by
    have localFrame := frameT.mono (by simp [writes, exchangeWrites] : ∀ r ∈ exchangeWrites p w, r ∈ writes p w)
    simpa only [writes, exchangeWrites, restW.sp, restV.sp, restU.sp] using localFrame

  have fV : Frame (writes p s) u.mem v.mem := by
    apply extend
    simpa only [restU.sp] using frameV
  have fW : Frame (writes p s) v.mem w.mem := frameW.mono (by simp [writes, exchangeWrites])
  exact ((fU.trans fV).trans fW).trans fT

end VG.Proof.Ffdh.Arm.SharedExchange
