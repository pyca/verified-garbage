module

import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Ffdh.Arm.ExchangeMain
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
public import VerifiedGarbage.Impl.Bignum.Arm.MontCall
public import VerifiedGarbage.Proof.Ffdh.Arm.SharedExchangeMemory
public import VerifiedGarbage.Impl.Ffdh.Arm.SharedExchange
import VerifiedGarbage.Proof.Ffdh.Arm.DomainNormalizedPrepareAt
import VerifiedGarbage.Proof.Ffdh.Arm.SharedCheckPublicPower
public import VerifiedGarbage.Proof.Ffdh.Arm.ExchangeMainCT
public import VerifiedGarbage.Proof.Ffdh.Arm.SharedCheckPublicPowerCT
import VerifiedGarbage.Proof.Ffdh.Arm.DomainNormalizedPrepareAtCT
import VerifiedGarbage.Proof.Bignum.Arm.TwoExpSharedCT
import VerifiedGarbage.Proof.Ffdh.Arm.RangeCT
import VerifiedGarbage.Proof.Ffdh.Arm.Range
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Offset

/-! Callable exchange preserves the private scalar's fixed public-length trace. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.SharedExchange
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Spec.Rsa.Mont (numAt Operand)

structure MainInput (p : Inputs) (slots : List Nat) (yb xb : List Byte) (s : State) : Prop extends
    ExchangeMainInput p slots yb xb s where
  calls : CallMemory p xb.length s

structure PowerInput (p : Inputs) (slots : List Nat) (yb xb : List Byte) (s : State) : Prop extends
    ExchangePowerInput p slots yb xb s where
  calls : CallMemory p xb.length s

theorem prepare_power (backend : MontBackend) (s : State) {p : Inputs} {slots : List Nat} {yb xb : List Byte}
    (h : MainInput p slots yb xb s) (stable : stableSlots slots = true)
    (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h32 : 32 ∈ slots)
    (peerLength : yb.length = p.k) (large : 1 < p.P) (odd : p.P % 2 = 1)
    (normalized : 2 ^ (64 * (p.w - 1)) ≤ p.P) :
    WP isa (VG.Impl.Ffdh.Arm.NormalizedPrepare.prepareAt
      (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul) 24) s (PowerInput p slots yb xb) := by
  refine WP.mono (domainNormalizedPrepareAt24_ok backend s h.context h.calls.toDomainCallMemory stable h0 h24 h32 large odd normalized) ?_
  rintro u ⟨context, ready, modulus, r2, frame, rest⟩
  have sourceSep {src : BitVec 32} {bs : List Byte} (source : Octets p.base src p.len bs s)
      (stack : Region.Disjoint ⟨State.addr src, bs.length⟩ ⟨State.addr s.sp, 72⟩)
      (below : Region.Disjoint ⟨State.addr src, bs.length⟩ (FrameStack.belowA s.sp 48))
      (r : Region) (hr : r ∈ domainPrepareWrites p s) : (⟨State.addr src, bs.length⟩ : Region).Disjoint r := by
    simp only [domainPrepareWrites, List.mem_append, List.mem_singleton] at hr
    rcases hr with hr | rfl
    · simp only [prepareAtWrites, prepareWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact source.separate
      · exact stack.sub_right (Offset.sub_base _ (by decide))
      · exact stack.sub_right (Offset.sub_base _ (by decide))
    · exact below
  exact ⟨⟨⟨context, ready, modulus, r2,
    h.peer.after_frame frame rest (sourceSep h.peer h.peerStack (by rw [peerLength]; exact h.calls.publicValue)),
    h.scalar.after_frame frame rest (sourceSep h.scalar h.scalarStack h.calls.scalarBelow)⟩,
    h.output.after rest, h.workspaceSep, by rw [rest.sp]; exact h.stackSep⟩, h.calls.after rest⟩

theorem power_finish (backend : MontBackend) (s : State) {p : Inputs} {slots : List Nat} {yb xb : List Byte}
    (h : PowerInput p slots yb xb s) (stable : stableSlots slots = true)
    (h32 : 32 ∈ slots) (h36 : 36 ∈ slots) (h40 : 40 ∈ slots) (h44 : 44 ∈ slots)
    (peerLength : yb.length = p.k) (positive : 0 < xb.length) (fits : xb.length < 2 ^ 32)
    (count : p.slotValue 44 = BitVec.ofNat 32 xb.length) (odd : p.P % 2 = 1) :
    WP isa (VG.Impl.Ffdh.Arm.SharedCheckPublic.powerAt
      (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul) 36 40 44) s (ExchangePowered p slots) := by
  refine WP.mono (sharedCheckPublicPower_ok backend s 36 40 44 h.context h.calls.toDomainCallMemory stable
    h36 h40 h44 h32 h.ready h.modulus odd h.r2 h.source peerLength h.exponent positive fits count h.calls.scalarBelow) ?_
  rintro u ⟨context, ready, value, modulus, _, _, _, rest⟩
  refine ⟨⟨context, ready, h.output.after rest, h.workspaceSep, by rw [rest.sp]; exact h.stackSep, ?_⟩, modulus⟩
  rw [value, VG.Proof.Bignum.powMod_eq]
  exact Nat.lt_trans (Nat.mod_lt _ (by have := h.ready.modulus; rw [h.modulus] at this; omega)) p.modulusBound

private theorem power_ct (backend : MontBackend) {p : Inputs} {slots : List Nat} {yb xb1 xb2 : List Byte}
    (stable : stableSlots slots = true) (h32 : 32 ∈ slots) (h36 : 36 ∈ slots)
    (h40 : 40 ∈ slots) (h44 : 44 ∈ slots)
    (peerLength : yb.length = p.k) (positive : 0 < xb1.length) (fits : xb1.length < 2 ^ 32)
    (count : p.slotValue 44 = BitVec.ofNat 32 xb1.length) (length : xb1.length = xb2.length)
    (odd : p.P % 2 = 1) :
    RelCT isa (fun s t => PowerInput p slots yb xb1 s ∧ PowerInput p slots yb xb2 t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.SharedCheckPublic.powerAt
        (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul) 36 40 44) (fun _ _ => True) := by
  intro s t tr1 tr2 u v h e1 e2
  let correct := fun o a b ho ha hb z input => backend.correct z (base := p.base) (len := p.len) (w := p.w)
    (o := o) (a := a) (b := b) input ho ha hb
  let K := TwoExp.sharedMontgomery p.base s.sp p.len p.w backend.name backend.mul correct backend.stackOk
  have timing : TwoExp.MontgomeryTiming K :=
    TwoExp.sharedMontgomeryTiming p.base s.sp p.len p.w backend.name backend.mul correct backend.stackOk
      (fun _ _ _ ho ha hb => backend.rawCT ho ha hb)
  have separate : ∀ r ∈ [⟨State.addr p.base, 8 * p.len⟩, FrameStack.belowA s.sp 48],
      Region.Disjoint ⟨State.addr (p.slotValue 40), xb1.length⟩ r := by
    intro r hr
    rcases List.mem_cons.mp hr with hr | hr
    · subst r; exact h.1.exponent.separate
    · have eq := List.mem_singleton.mp hr; subst r; exact h.1.calls.scalarBelow
  have run := (sharedCheckPublicPowerAt_ct K timing stable h36 h40 h44 h32
    peerLength positive fits count length odd separate).mono
    (P' := fun (a b : State) => (PowerInput p slots yb xb1 a ∧ a.sp = s.sp) ∧
      (PowerInput p slots yb xb2 b ∧ b.sp = s.sp) ∧ a.sp = b.sp)
    (fun _ _ hab => ⟨⟨hab.1.1.toExchangePowerInput.toPowerAtInput, hab.1.1.calls.stack, hab.1.2⟩,
      ⟨hab.2.1.1.toExchangePowerInput.toPowerAtInput, hab.2.1.1.calls.stack, hab.2.1.2⟩, hab.2.2⟩)
    (fun _ _ hx => hx)
  exact run s t tr1 tr2 u v ⟨⟨h.1,rfl⟩,⟨h.2.1,h.2.2.symm⟩,h.2.2⟩ e1 e2

theorem main_ct (backend : MontBackend) {p : Inputs} {slots : List Nat} {yb xb1 xb2 : List Byte}
    (stable : stableSlots slots = true) (h0 : 0 ∈ slots) (h4 : 4 ∈ slots) (h24 : 24 ∈ slots)
    (h32 : 32 ∈ slots) (h36 : 36 ∈ slots) (h40 : 40 ∈ slots) (h44 : 44 ∈ slots)
    (saved : ∀ d ∈ slots, d + 4 ≤ 64 ∨ 68 ≤ d)
    (peerLength : yb.length = p.k) (positive : 0 < xb1.length) (fits : xb1.length < 2 ^ 32)
    (count : p.slotValue 44 = BitVec.ofNat 32 xb1.length) (length : xb1.length = xb2.length)
    (large : 1 < p.P) (odd : p.P % 2 = 1)
    (normalized : 2 ^ (64 * (p.w - 1)) ≤ p.P) :
    RelCT isa (fun s t => MainInput p slots yb xb1 s ∧ MainInput p slots yb xb2 t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.SharedExchange.main (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul)) (fun _ _ => True) := by
  have prepare := (domainNormalizedPrepareAt24_ct backend stable h0 h24 h32 large odd normalized).mono
    (P' := fun (s t : State) => MainInput p slots yb xb1 s ∧ MainInput p slots yb xb2 t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨⟨h.1.context,h.1.calls.toDomainCallMemory⟩,
      ⟨h.2.1.context,h.2.1.calls.toDomainCallMemory⟩,h.2.2⟩) (fun _ _ h => h)
  have ranges := (inRange_ct (base := p.base) (len := p.len) (w := p.w)
    (by simp [Operand, Spec.Rsa.Mont.aAcc, Spec.Rsa.Mont.aTmp] : Operand 6) (by decide)).mono
    (P' := fun (s t : State) => ExchangePowered p slots s ∧ ExchangePowered p slots t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨h.1.ready,h.2.1.ready,h.2.2⟩) (fun _ _ h => h)
  unfold VG.Impl.Ffdh.Arm.SharedExchange.main
  exact relCT_chain prepare
    (fun s h => prepare_power backend s h stable h0 h24 h32 peerLength large odd normalized)
    (fun s h => prepare_power backend s h stable h0 h24 h32 peerLength large odd normalized)
    (relCT_chain (power_ct backend stable h32 h36 h40 h44 peerLength positive fits count length odd)
      (fun s h => power_finish backend s h stable h32 h36 h40 h44 peerLength positive fits count odd)
      (fun s h => power_finish backend s h stable h32 h36 h40 h44 peerLength
        (by rw [←length]; exact positive) (by rw [←length]; exact fits) (by rw [←length]; exact count) odd)
      (relCT_chain ranges (fun s h => exchangeRange_finish s h stable odd)
        (fun s h => exchangeRange_finish s h stable odd) (exchangeFinish_ct stable h4 h32 saved)))

end VG.Proof.Ffdh.Arm.SharedExchange
