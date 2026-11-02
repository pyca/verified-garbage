module

public import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
public import VerifiedGarbage.Impl.Bignum.Arm.MontCall
public import Init.Data.BitVec.Basic
public import VerifiedGarbage.Impl.Ffdh.Arm.SharedExchange
public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.TCB.Arm.Target

import VerifiedGarbage.Proof.Ffdh.Arm.SharedExchangeCorrect
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Ffdh.Arm.SharedExchangePre
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Ffdh.Arm.ExchangeMain
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Ffdh.Arm.SharedExchangeMemory
import VerifiedGarbage.Proof.Ffdh.Arm.DomainNormalizedPrepareAt
import VerifiedGarbage.Proof.Ffdh.Arm.SharedCheckPublicPower
import VerifiedGarbage.Proof.Ffdh.Arm.ExchangeMainCT
import VerifiedGarbage.Proof.Ffdh.Arm.SharedCheckPublicPowerCT
import VerifiedGarbage.Proof.Ffdh.Arm.DomainNormalizedPrepareAtCT
import VerifiedGarbage.Proof.Bignum.Arm.TwoExpSharedCT
import VerifiedGarbage.Proof.Ffdh.Arm.RangeCT
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Impl.Ffdh.Arm.SharedCheckPublic
import VerifiedGarbage.Proof.Ffdh.Arm.PowerAtCT
import VerifiedGarbage.Proof.Ffdh.Arm.Head
import VerifiedGarbage.Proof.Ffdh.Arm.HeadCT
import VerifiedGarbage.Proof.Ffdh.Arm.BranchCT
import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack
import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Ffdh.Arm.SharedExchangeFn
import VerifiedGarbage.Proof.Ffdh.Arm.ExchangeEntryCT
import VerifiedGarbage.Proof.Ffdh.Arm.FrameCT
import VerifiedGarbage.Proof.Ffdh.Arm.Entered
import VerifiedGarbage.Proof.Ffdh.Arm.Block
/-! The shared exchange timing policy is satisfied even when private values and statuses differ. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/SharedExchangeMainCT.lean`, which only this module imported.
section

/-! Callable exchange preserves the private scalar's fixed public-length trace. -/

section
namespace VG.Proof.Ffdh.Arm.SharedExchange
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt Operand)

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
    (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp] : Operand 6) (by decide)).mono
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
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/SharedExchangeBodyCT.lean`, which only this module imported.
section

/-! Invalid-domain handling and the shared-secret body reveal no private scalar data. -/

section
namespace VG.Proof.Ffdh.Arm.SharedExchange
open VG VG.Arm VG.Proof.Bignum.Arm

theorem body_ct (backend : MontBackend) {p : Inputs} {slots : List Nat} {yb xb1 xb2 : List Byte}
    (stable : stableSlots slots = true) (h0 : 0 ∈ slots) (h4 : 4 ∈ slots) (h24 : 24 ∈ slots)
    (h32 : 32 ∈ slots) (h36 : 36 ∈ slots) (h40 : 40 ∈ slots) (h44 : 44 ∈ slots)
    (saved : ∀ d ∈ slots, d + 4 ≤ 64 ∨ 68 ≤ d)
    (peerLength : yb.length = p.k) (positive : 0 < xb1.length) (fits : xb1.length < 2 ^ 32)
    (count : p.slotValue 44 = BitVec.ofNat 32 xb1.length) (length : xb1.length = xb2.length) :
    RelCT isa (fun s t => MainInput p slots yb xb1 s ∧ MainInput p slots yb xb2 t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.Domain.head (VG.Impl.Ffdh.Arm.SharedExchange.main (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul))) (fun _ _ => True) := by
  let Q := fun (xb : List Byte) (s : State) => MainInput p (60 :: 56 :: slots) yb xb s ∧
    s.z = Spec.Rsa.modulusValid p.P p.k
  have head := (head_ct stable h0 h24 h32).mono
    (P' := fun (s t : State) => MainInput p slots yb xb1 s ∧ MainInput p slots yb xb2 t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨h.1.context, h.2.1.context, h.2.2⟩) (fun _ _ h => h)
  have wp (s : State) {xb : List Byte} (h : MainInput p slots yb xb s) :
      WP isa (.seq (.block (VG.Impl.Ffdh.Arm.Domain.prepareArgs 24 ++ VG.Impl.Ffdh.Arm.Domain.domainPointers))
        (.block VG.Impl.Bignum.Arm.modulusCheck)) s (Q xb) := by
    refine WP.mono (head_ok s h.context stable h0 h24 h32) ?_
    rintro u ⟨context, zero, frame, rest⟩
    have sourceSep {src : BitVec 32} {bs : List Byte}
        (sep : Region.Disjoint ⟨State.addr src, bs.length⟩ ⟨State.addr s.sp, 72⟩)
        (r : Region) (hr : r ∈ [⟨State.addr s.sp, 72⟩]) : (⟨State.addr src, bs.length⟩ : Region).Disjoint r := by
      rw [List.mem_singleton] at hr; subst r; exact sep
    exact ⟨⟨⟨context, h.peer.after_frame frame rest (sourceSep h.peerStack),
      h.scalar.after_frame frame rest (sourceSep h.scalarStack), h.output.after rest,
      by rw [rest.sp]; exact h.peerStack, by rw [rest.sp]; exact h.scalarStack,
      h.workspaceSep, by rw [rest.sp]; exact h.stackSep⟩, h.calls.after rest⟩, zero⟩
  have stable' : stableSlots (60 :: 56 :: slots) = true := by
    change (true && (true && stableSlots slots)) = true
    rw [Bool.true_and, Bool.true_and, stable]
  have saved' : ∀ d ∈ 60 :: 56 :: slots, d + 4 ≤ 64 ∨ 68 ≤ d := by
    intro d hd
    simp only [List.mem_cons] at hd
    rcases hd with rfl | rfl | hd
    · exact Or.inl (by decide)
    · exact Or.inl (by decide)
    · exact saved d hd
  have branches : RelCT isa (fun s t => Q xb1 s ∧ Q xb2 t ∧ s.sp = t.sp)
      (.ite .eq (VG.Impl.Ffdh.Arm.SharedExchange.main (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul)) (VG.Impl.Ffdh.Arm.Domain.ret 0)) (fun _ _ => True) := by
    apply RelCT.ite (fun s t h => by change some s.z = some t.z; rw [h.1.2, h.2.1.2])
    · intro s t tr1 tr2 u v h e1 e2
      have valid : Spec.Rsa.modulusValid p.P p.k = true := by
        have selected := h.2
        change some s.z = some true at selected
        rw [h.1.1.2] at selected
        exact Option.some.inj selected
      have facts := VG.Proof.Bignum.valid_facts valid p.minLength
      exact main_ct backend stable' (by simp [h0]) (by simp [h4]) (by simp [h24])
        (by simp [h32]) (by simp [h36]) (by simp [h40]) (by simp [h44]) saved'
        peerLength positive fits count length facts.2.1 facts.1 facts.2.2 s t tr1 tr2 u v
        ⟨h.1.1.1, h.1.2.1.1, h.1.2.2⟩ e1 e2
    · exact (ret_ct 0).mono (fun _ _ _ => trivial) (fun _ _ h => h)
  unfold VG.Impl.Ffdh.Arm.Domain.head
  apply RelCT.assoc
  exact relCT_chain head (fun s h => wp s h) (fun s h => wp s h) branches

end VG.Proof.Ffdh.Arm.SharedExchange
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/SharedExchangeFnCT.lean`, which only this module imported.
section

/-! The complete callable shared-secret computation is constant time in the private scalar. -/

section
namespace VG.Proof.Ffdh.Arm.SharedExchange
open VG VG.Arm VG.Proof.Bignum.Arm

theorem fn_ct (backend : MontBackend) {p : Inputs} {yb xb1 xb2 : List Byte} (length : xb1.length = xb2.length) :
    RelCT isa (fun s t => FnInput p yb xb1 s ∧ FnInput p yb xb2 t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.SharedExchange.code (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul)) (fun _ _ => True) := by
  let P := fun (xb : List Byte) (a : State) => ∃ s, FnInput p yb xb s ∧ a = entered s
  have entry := exchangeEntry_ct.mono
    (P' := fun (s t : State) => P xb1 s ∧ P xb2 t ∧ s.sp = t.sp)
    (fun _ _ h => h.2.2) (fun _ _ h => h)
  have wp (a : State) {xb : List Byte} (h : P xb a) :
      WP isa (.block VG.Impl.Ffdh.Arm.Domain.Exchange.entry) a
        (MainInput p [0, 36, 44, 40, 32, 28, 24, 4] yb xb) := by
    obtain ⟨s, input, rfl⟩ := h
    refine WP.mono (withAllRest (exchangeEntry_ok (entered s) input.input.args input.input.incoming input.input.out input.input.domain input.input.domainLength)) ?_
    rintro u ⟨⟨context, frame⟩, rest⟩
    have sourceSep {src : BitVec 32} {bs : List Byte}
        (sep : Region.Disjoint ⟨State.addr src, bs.length⟩ ⟨State.addr (entered s).sp, 72⟩)
        (r : Region) (hr : r ∈ [⟨State.addr (entered s).sp, 72⟩]) : (⟨State.addr src, bs.length⟩ : Region).Disjoint r := by
      rw [List.mem_singleton] at hr; subst r; exact sep
    exact ⟨⟨context, input.input.peer.after_frame frame rest (sourceSep input.input.peerStack),
      input.input.scalar.after_frame frame rest (sourceSep input.input.scalarStack), input.input.output.after rest,
      by rw [rest.sp]; exact input.input.peerStack, by rw [rest.sp]; exact input.input.scalarStack,
      input.input.workspaceSep, by rw [rest.sp]; exact input.input.stackSep⟩, input.calls.after rest⟩
  unfold VG.Impl.Ffdh.Arm.SharedExchange.code
  apply framed_ct (fun _ _ h => ⟨h.1.input.stackFits, h.2.1.input.stackFits⟩) (fun _ _ h => h.2.2)
  intro a b tr1 tr2 u v h e1 e2
  obtain ⟨s, t, related, rfl, rfl⟩ := h
  have body := relCT_chain entry (fun a h => wp a h) (fun a h => wp a h)
    (body_ct backend (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by intro d hd; revert d; decide) related.1.input.peerLength related.1.input.positive related.1.input.scalarFit related.1.input.scalarCount length)
  exact body _ _ _ _ _ _ ⟨⟨s, related.1, rfl⟩, ⟨t, related.2.1, rfl⟩,
    by rw [entered_sp, entered_sp, related.2.2]⟩ e1 e2

end VG.Proof.Ffdh.Arm.SharedExchange
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm.SharedExchange
open VG VG.Arm

theorem contract_ct (backend : Bignum.Arm.MontBackend) : ConstantTime isa (Spec.Ffdh.exchangeContract abi 176).pre
    (Spec.Ffdh.exchangeContract abi 176).pub (VG.Impl.Ffdh.Arm.SharedExchange.code (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul)) := by
  intro s t tr1 tr2 u v hs ht hp e1 e2
  obtain ⟨p, yb, xb, base, out, domain, peer, scalar, count, capacity, privateCount,
    domainBytes, peerBytes, scalarBytes, inputS⟩ := data s hs
  have peerLength (a : State) (h : (Spec.Ffdh.exchangeContract abi 176).pre a) :
      (stackArg a 4).toNat = (stackArg a 0).toNat := by
    sig_pre [Spec.Ffdh.exchangeContract, Spec.Ffdh.exchangeSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at h
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, length, _, _, _⟩ := h
    exact length
  sig_pub [Spec.Ffdh.exchangeContract, Spec.Ffdh.exchangeSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at hp
  obtain ⟨sp, bytes, p0, _, p2, p3, p4, p5, p6, p7, _, p9, p10⟩ := hp
  rw [peerLength s hs, peerLength t ht, ← p2, ← p3, ← p7, ← p4] at bytes
  simp only [List.append_assoc] at bytes
  obtain ⟨domEqNat, tailEq⟩ := List.append_inj bytes
    (by simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range])
  obtain ⟨peerEqNat, _⟩ := List.append_inj tailEq
    (by simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range])
  have recover {a b : List Byte} (h : a.map BitVec.toNat = b.map BitVec.toNat) : a = b := by
    have eq := congrArg (List.map (BitVec.ofNat 8)) h
    simpa only [List.map_map, Function.comp_def, BitVec.ofNat_toNat,
      BitVec.setWidth_eq, List.map_id'] using eq
  have domEq := recover domEqNat
  have peerEq := recover peerEqNat
  let xb2 := Spec.Rsa.bytesAt t.mem (State.addr p.privateValue) p.privateLength
  have inputT := input t ht (p := p) (yb := yb) (xb := xb2)
    (p9.symm.trans base) (p0.symm.trans out) (p2.symm.trans domain) (p7.symm.trans peer) (p5.symm.trans scalar)
    (by rw [← p4]; exact count) (by rw [← p10]; exact capacity) (by rw [← p6]; exact privateCount) ?_ ?_ rfl
  · have xLength : xb.length = p.privateLength := by
      have eq := congrArg List.length scalarBytes
      simpa only [VG.Proof.Bignum.bytesAt_length] using eq.symm
    have x2Length : xb2.length = p.privateLength := VG.Proof.Bignum.bytesAt_length _ _ _
    exact (fn_ct backend (by rw [xLength, x2Length]) s t tr1 tr2 u v ⟨inputS, inputT, sp⟩ e1 e2).1
  · rw [← p3, ← domain]
    change Spec.Rsa.bytesAt t.mem (BitVec.setWidth 64 (s.gpr .r2)) (s.gpr .r3).toNat = p.dom
    rw [← domEq, domain]
    exact domainBytes
  · rw [← peer, ← count]
    change Spec.Rsa.bytesAt t.mem (BitVec.setWidth 64 (stackArg s 3)) (stackArg s 0).toNat = yb
    rw [← peerEq, peer, count]
    exact peerBytes

end VG.Proof.Ffdh.Arm.SharedExchange
