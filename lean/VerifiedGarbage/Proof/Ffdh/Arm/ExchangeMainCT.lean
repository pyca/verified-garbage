module

import VerifiedGarbage.Proof.Ffdh.Arm.ExchangeMain
public import VerifiedGarbage.Proof.Ffdh.Arm.ExchangeFinishCT
public import VerifiedGarbage.Proof.Ffdh.Arm.PowerAtCT
import VerifiedGarbage.Proof.Ffdh.Arm.PrepareAtCT
import VerifiedGarbage.Proof.Ffdh.Arm.RangeCT
import VerifiedGarbage.Proof.Ffdh.Arm.Range
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Ffdh.Arm.Output
public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Impl.Ffdh.Arm.Domain
import VerifiedGarbage.Proof.Ffdh.Arm.PowerAt

/-! Shared-secret computation uses the same window and masking trace for distinct private scalars. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt Operand)

structure ExchangeMainInput (p : Inputs) (slots : List Nat) (yb xb : List Byte) (s : State) : Prop where
  context : Context p slots s
  peer : Octets p.base p.publicValue p.len yb s
  scalar : Octets p.base p.privateValue p.len xb s
  output : OutputBuffer p.output p.k s
  peerStack : Region.Disjoint ⟨State.addr p.publicValue, yb.length⟩ ⟨State.addr s.sp, 72⟩
  scalarStack : Region.Disjoint ⟨State.addr p.privateValue, xb.length⟩ ⟨State.addr s.sp, 72⟩
  workspaceSep : Region.Disjoint ⟨State.addr p.base, 8 * p.len⟩ ⟨State.addr p.output, p.k⟩
  stackSep : Region.Disjoint ⟨State.addr s.sp, 72⟩ ⟨State.addr p.output, p.k⟩

structure ExchangePowerInput (p : Inputs) (slots : List Nat) (yb xb : List Byte) (s : State) : Prop extends
    PowerAtInput p slots 36 40 p.P yb xb s where
  output : OutputBuffer p.output p.k s
  workspaceSep : Region.Disjoint ⟨State.addr p.base, 8 * p.len⟩ ⟨State.addr p.output, p.k⟩
  stackSep : Region.Disjoint ⟨State.addr s.sp, 72⟩ ⟨State.addr p.output, p.k⟩

structure ExchangePowered (p : Inputs) (slots : List Nat) (s : State) : Prop extends
    ExchangeFinishInput p slots s where
  modulus : numAt s.mem (State.addr p.base) p.w 0 = p.P

theorem exchangePrepare_power (s : State) {p : Inputs} {slots : List Nat} {yb xb : List Byte}
    (h : ExchangeMainInput p slots yb xb s) (stable : stableSlots slots = true)
    (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h32 : 32 ∈ slots) (large : 1 < p.P) (odd : p.P % 2 = 1) :
    WP isa (VG.Impl.Ffdh.Arm.Domain.prepareAt 24) s (ExchangePowerInput p slots yb xb) := by
  have pStack : Region.Disjoint ⟨State.addr p.domain, p.k⟩ ⟨State.addr s.sp, 72⟩ :=
    h.context.domainStack.sub_left (Region.sub_prefix (by rw [p.domainLength]; split <;> omega))
  refine WP.mono (prepareAt_ok s 24 h.context stable h24 h32 h0 h.context.pBytes p.pLength pStack large odd) ?_
  rintro u ⟨context, ready, modulus, r2, frame, rest⟩
  have sourceSep {src : BitVec 32} {bs : List Byte} (source : Octets p.base src p.len bs s)
      (stack : Region.Disjoint ⟨State.addr src, bs.length⟩ ⟨State.addr s.sp, 72⟩)
      (r : Region) (hr : r ∈ prepareAtWrites p s) : (⟨State.addr src, bs.length⟩ : Region).Disjoint r := by
    simp only [prepareAtWrites, prepareWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact source.separate
    · exact stack.sub_right (Offset.sub_base _ (by decide))
    · exact stack.sub_right (Offset.sub_base _ (by decide))
  exact ⟨⟨context, ready, modulus, r2, h.peer.after_frame frame rest (sourceSep h.peer h.peerStack),
    h.scalar.after_frame frame rest (sourceSep h.scalar h.scalarStack)⟩, h.output.after rest,
    h.workspaceSep, by rw [rest.sp]; exact h.stackSep⟩

theorem exchangePower_finish (s : State) {p : Inputs} {slots : List Nat} {yb xb : List Byte}
    (h : ExchangePowerInput p slots yb xb s) (stable : stableSlots slots = true)
    (h32 : 32 ∈ slots) (h36 : 36 ∈ slots) (h40 : 40 ∈ slots) (h44 : 44 ∈ slots)
    (peerLength : yb.length = p.k) (positive : 0 < xb.length) (fits : xb.length < 2 ^ 32)
    (count : p.slotValue 44 = BitVec.ofNat 32 xb.length) (odd : p.P % 2 = 1) :
    WP isa (VG.Impl.Ffdh.Arm.Domain.powerAt 36 40 44) s (ExchangePowered p slots) := by
  refine WP.mono (powerAt_ok s 36 40 44 h.context stable h36 h40 h44 h32 h.ready h.modulus odd h.r2
    h.source peerLength h.exponent positive fits count) ?_
  rintro u ⟨context, ready, value, modulus, _, _, _, rest⟩
  refine ⟨⟨context, ready, h.output.after rest, h.workspaceSep, by rw [rest.sp]; exact h.stackSep, ?_⟩, modulus⟩
  rw [value, VG.Proof.Bignum.powMod_eq]
  exact Nat.lt_trans (Nat.mod_lt _ (by have := h.ready.modulus; rw [h.modulus] at this; omega)) p.modulusBound

theorem exchangeRange_finish (s : State) {p : Inputs} {slots : List Nat}
    (h : ExchangePowered p slots s) (stable : stableSlots slots = true) (odd : p.P % 2 = 1) :
    WP isa (VG.Impl.Ffdh.Arm.inRange 6) s (ExchangeFinishInput p slots) := by
  have op6 : Operand 6 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  refine WP.mono (inRange_ok s h.ready op6 (by decide) (by rw [h.modulus]; exact odd)) ?_
  rintro u ⟨ready, _, arrays, frame, rest⟩
  exact ⟨h.context.after_workspace frame rest ready.ptr (fun d hd => (stableSlots_at stable hd).1),
    ready, h.output.after rest, h.workspaceSep, by rw [rest.sp]; exact h.stackSep,
    by rw [arrays 6 op6 (by decide)]; exact h.valueFit⟩

theorem exchangeMain_ct {p : Inputs} {slots : List Nat} {yb xb1 xb2 : List Byte}
    (stable : stableSlots slots = true) (h0 : 0 ∈ slots) (h4 : 4 ∈ slots) (h24 : 24 ∈ slots)
    (h32 : 32 ∈ slots) (h36 : 36 ∈ slots) (h40 : 40 ∈ slots) (h44 : 44 ∈ slots)
    (saved : ∀ d ∈ slots, d + 4 ≤ 64 ∨ 68 ≤ d)
    (peerLength : yb.length = p.k) (positive : 0 < xb1.length) (fits : xb1.length < 2 ^ 32)
    (count : p.slotValue 44 = BitVec.ofNat 32 xb1.length) (length : xb1.length = xb2.length)
    (large : 1 < p.P) (odd : p.P % 2 = 1) :
    RelCT isa (fun s t => ExchangeMainInput p slots yb xb1 s ∧ ExchangeMainInput p slots yb xb2 t ∧ s.sp = t.sp)
      VG.Impl.Ffdh.Arm.Domain.Exchange.main (fun _ _ => True) := by
  have pStack (s : State) {xb : List Byte} (h : ExchangeMainInput p slots yb xb s) :
      Region.Disjoint ⟨State.addr p.domain, p.k⟩ ⟨State.addr s.sp, 72⟩ :=
    h.context.domainStack.sub_left (Region.sub_prefix (by rw [p.domainLength]; split <;> omega))
  have prepare := (prepareAt_ct (p := p) (slot := 24) stable h24 h32 h0 p.pLength large odd).mono
    (P' := fun (s t : State) => ExchangeMainInput p slots yb xb1 s ∧ ExchangeMainInput p slots yb xb2 t ∧ s.sp = t.sp)
    (fun s t h => ⟨⟨h.1.context, h.1.context.pBytes, pStack s h.1⟩,
      ⟨h.2.1.context, h.2.1.context.pBytes, pStack t h.2.1⟩, h.2.2⟩) (fun _ _ h => h)
  have powers := (powerAt_ct (p := p) stable h36 h40 h44 h32 peerLength positive fits count length odd).mono
    (P' := fun (s t : State) => ExchangePowerInput p slots yb xb1 s ∧ ExchangePowerInput p slots yb xb2 t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨h.1.toPowerAtInput, h.2.1.toPowerAtInput, h.2.2⟩) (fun _ _ h => h)
  have ranges := (inRange_ct (base := p.base) (len := p.len) (w := p.w)
    (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp] : Operand 6) (by decide)).mono
    (P' := fun (s t : State) => ExchangePowered p slots s ∧ ExchangePowered p slots t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨h.1.ready, h.2.1.ready, h.2.2⟩) (fun _ _ h => h)
  unfold VG.Impl.Ffdh.Arm.Domain.Exchange.main
  exact relCT_chain prepare
    (fun s h => exchangePrepare_power s h stable h0 h24 h32 large odd)
    (fun s h => exchangePrepare_power s h stable h0 h24 h32 large odd)
    (relCT_chain powers
      (fun s h => exchangePower_finish s h stable h32 h36 h40 h44 peerLength positive fits count odd)
      (fun s h => exchangePower_finish s h stable h32 h36 h40 h44 peerLength
        (by rw [← length]; exact positive) (by rw [← length]; exact fits) (by rw [← length]; exact count) odd)
      (relCT_chain ranges (fun s h => exchangeRange_finish s h stable odd)
        (fun s h => exchangeRange_finish s h stable odd) (exchangeFinish_ct stable h4 h32 saved)))

end VG.Proof.Ffdh.Arm
