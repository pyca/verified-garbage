module

import VerifiedGarbage.Proof.Ffdh.Arm.SharedDeriveTail
public import VerifiedGarbage.Proof.Ffdh.Arm.ExchangeMainCT
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Ffdh.Arm.SharedCheckPublicPower
import VerifiedGarbage.Proof.Ffdh.Arm.SharedCheckPublicPowerCT
import VerifiedGarbage.Proof.Ffdh.Arm.MaskOutputCT
import VerifiedGarbage.Proof.Ffdh.Arm.RangeCT
import VerifiedGarbage.Proof.Ffdh.Arm.BranchCT
import VerifiedGarbage.Proof.Ffdh.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Bignum.Arm.TwoExpSharedCT
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Impl.Ffdh.Arm.SharedDerive
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import Init.Prelude
public import VerifiedGarbage.Impl.Ffdh.Arm.SharedDerive
public import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
public import VerifiedGarbage.Proof.Ffdh.Arm.SharedExchangeMemory

/-! After the scalar test, both paths' traces depend only on the domain and lengths: the power
of g over x's `x_len` bytes, y's range, export and masking for any flag, and the status in
registers; or the zero mask and 2. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.SharedDerive
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt Operand)

/-- The prepared modulus with x, the output and the call area. -/
structure Prepared (p : Inputs) (slots : List Nat) (xb : List Byte) (s : State) : Prop where
  context : Context p slots s
  ready : ArithmeticReady p.base p.len p.w s
  modulus : numAt s.mem (State.addr p.base) p.w 0 = p.P
  r2 : numAt s.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % p.P
  calls : SharedExchange.CallMemory p xb.length s
  scalar : Octets p.base p.privateValue p.len xb s
  output : OutputBuffer p.output p.k s
  workspaceSep : Region.Disjoint ⟨State.addr p.base, 8 * p.len⟩ ⟨State.addr p.output, p.k⟩
  stackSep : Region.Disjoint ⟨State.addr s.sp, 72⟩ ⟨State.addr p.output, p.k⟩

theorem Prepared.after_mem {p : Inputs} {slots : List Nat} {xb : List Byte} {s t : State}
    (h : Prepared p slots xb s) (mem : t.mem = s.mem) (rest : VG.Proof.X25519.Arm.Rest [] s t) :
    Prepared p slots xb t := by
  have ptr := (rest.gpr .r0 (by simp)).trans h.context.ptr
  have frame : Frame [⟨State.addr p.base, 8 * p.len⟩] s.mem t.mem := by rw [mem]; exact Frame.refl _ _
  exact ⟨h.context.of_mem mem rest ptr, h.ready.of_mem mem rest ptr, by rw [mem]; exact h.modulus,
    by rw [mem]; exact h.r2, h.calls.after rest, h.scalar.after_workspace frame rest, h.output.after rest,
    h.workspaceSep, by rw [rest.sp]; exact h.stackSep⟩

theorem status_ct : RelCT isa (fun _ _ => True)
    (.block VG.Impl.Ffdh.Arm.SharedDerive.status) (fun _ _ => True) := by
  apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
  intro s t _
  exact Taint.agree_ofRegs (by simp)

theorem fail_ct {p : Inputs} {slots : List Nat} {xb1 xb2 : List Byte} (h4 : 4 ∈ slots) (h32 : 32 ∈ slots) :
    RelCT isa (fun s t => Prepared p slots xb1 s ∧ Prepared p slots xb2 t ∧ s.sp = t.sp)
      VG.Impl.Ffdh.Arm.SharedDerive.fail (fun _ _ => True) := by
  have save := (RelCT.block_append (stackAddr_ct.seq (storeLocal_ct .r11 64))).mono
    (P' := fun (s t : State) => Prepared p slots xb1 s ∧ Prepared p slots xb2 t ∧ s.sp = t.sp)
    (fun _ _ h => h.2.2) (fun _ _ _ => trivial)
  have wp (s : State) {xb : List Byte} (h : Prepared p slots xb s) :
      WP isa (.block VG.Impl.Ffdh.Arm.Domain.Exchange.saveResult) s (AnyMaskInput p) :=
    WP.mono (failSave_ok s h.context h4 h32 h.output h.stackSep) fun _ hu => ⟨_, hu.1⟩
  have mask : RelCT isa (fun s t => AnyMaskInput p s ∧ AnyMaskInput p t ∧ s.sp = t.sp)
      VG.Impl.Ffdh.Arm.Domain.Exchange.maskOutput (fun _ _ => True) := by
    intro s t tr1 tr2 u v h e1 e2
    obtain ⟨_, h1⟩ := h.1
    obtain ⟨_, h2⟩ := h.2.1
    exact maskOutput_ct s t tr1 tr2 u v ⟨h1, h2, h.2.2⟩ e1 e2
  unfold VG.Impl.Ffdh.Arm.SharedDerive.fail
  exact relCT_chain save (fun s h => wp s h) (fun s h => wp s h) (mask.seq ((ret_ct 2).mono (fun _ _ _ => trivial) (fun _ _ h => h)))

theorem power_finish (backend : MontBackend) (s : State) {p : Inputs} {slots : List Nat} {xb : List Byte}
    (h : Prepared p slots xb s) (stable : stableSlots slots = true)
    (h32 : 32 ∈ slots) (h40 : 40 ∈ slots) (h44 : 44 ∈ slots) (h56 : 56 ∈ slots)
    (positive : 0 < xb.length) (fits : xb.length < 2 ^ 32)
    (count : p.slotValue 44 = BitVec.ofNat 32 xb.length) (odd : p.P % 2 = 1) :
    WP isa (VG.Impl.Ffdh.Arm.SharedCheckPublic.powerAt
      (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul) 56 40 44) s (ExchangePowered p slots) := by
  refine WP.mono (sharedCheckPublicPower_ok backend s 56 40 44 h.context h.calls.toDomainCallMemory stable
    h56 h40 h44 h32 h.ready h.modulus odd h.r2 h.context.gBytes p.gLength h.scalar positive fits count
    h.calls.scalarBelow) ?_
  rintro u ⟨context, ready, value, modulus, _, _, _, rest⟩
  refine ⟨⟨context, ready, h.output.after rest, h.workspaceSep, by rw [rest.sp]; exact h.stackSep, ?_⟩, modulus⟩
  rw [value, VG.Proof.Bignum.powMod_eq]
  exact Nat.lt_trans (Nat.mod_lt _ (by have := h.ready.modulus; rw [h.modulus] at this; omega)) p.modulusBound

theorem power_ct (backend : MontBackend) {p : Inputs} {slots : List Nat} {xb1 xb2 : List Byte}
    (stable : stableSlots slots = true) (h32 : 32 ∈ slots) (h40 : 40 ∈ slots)
    (h44 : 44 ∈ slots) (h56 : 56 ∈ slots)
    (positive : 0 < xb1.length) (fits : xb1.length < 2 ^ 32)
    (count : p.slotValue 44 = BitVec.ofNat 32 xb1.length) (length : xb1.length = xb2.length)
    (odd : p.P % 2 = 1) :
    RelCT isa (fun s t => Prepared p slots xb1 s ∧ Prepared p slots xb2 t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.SharedCheckPublic.powerAt
        (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul) 56 40 44) (fun _ _ => True) := by
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
    · subst r; exact h.1.scalar.separate
    · have eq := List.mem_singleton.mp hr; subst r; exact h.1.calls.scalarBelow
  have input (a : State) {xb : List Byte} (ha : Prepared p slots xb a) :
      PowerAtInput p slots 56 40 p.P (gOctets p) xb a :=
    ⟨ha.context, ha.ready, ha.modulus, ha.r2, ha.context.gBytes, ha.scalar⟩
  have run := (sharedCheckPublicPowerAt_ct K timing stable h56 h40 h44 h32
    p.gLength positive fits count length odd separate).mono
    (P' := fun (a b : State) => (Prepared p slots xb1 a ∧ a.sp = s.sp) ∧
      (Prepared p slots xb2 b ∧ b.sp = s.sp) ∧ a.sp = b.sp)
    (fun _ _ hab => ⟨⟨input _ hab.1.1, hab.1.1.calls.stack, hab.1.2⟩,
      ⟨input _ hab.2.1.1, hab.2.1.1.calls.stack, hab.2.1.2⟩, hab.2.2⟩)
    (fun _ _ hx => hx)
  exact run s t tr1 tr2 u v ⟨⟨h.1, rfl⟩, ⟨h.2.1, h.2.2.symm⟩, h.2.2⟩ e1 e2

theorem tail_ct (backend : MontBackend) {p : Inputs} {slots : List Nat} {xb1 xb2 : List Byte}
    (stable : stableSlots slots = true) (h4 : 4 ∈ slots) (h32 : 32 ∈ slots) (h40 : 40 ∈ slots)
    (h44 : 44 ∈ slots) (h56 : 56 ∈ slots) (saved : ∀ d ∈ slots, d + 4 ≤ 64 ∨ 68 ≤ d)
    (positive : 0 < xb1.length) (fits : xb1.length < 2 ^ 32)
    (count : p.slotValue 44 = BitVec.ofNat 32 xb1.length) (length : xb1.length = xb2.length)
    (odd : p.P % 2 = 1) :
    RelCT isa (fun s t => Prepared p slots xb1 s ∧ Prepared p slots xb2 t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.SharedDerive.tail (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul))
      (fun _ _ => True) := by
  have ranges := (inRange_ct (base := p.base) (len := p.len) (w := p.w)
    (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp] : Operand 6) (by decide)).mono
    (P' := fun (s t : State) => ExchangePowered p slots s ∧ ExchangePowered p slots t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨h.1.ready, h.2.1.ready, h.2.2⟩) (fun _ _ h => h)
  unfold VG.Impl.Ffdh.Arm.SharedDerive.tail VG.Impl.Ffdh.Arm.SharedExchange.finish
  exact relCT_chain (power_ct backend stable h32 h40 h44 h56 positive fits count length odd)
    (fun s h => power_finish backend s h stable h32 h40 h44 h56 positive fits count odd)
    (fun s h => power_finish backend s h stable h32 h40 h44 h56
      (by rw [← length]; exact positive) (by rw [← length]; exact fits) (by rw [← length]; exact count) odd)
    (relCT_chain ranges (fun s h => exchangeRange_finish s h stable odd)
      (fun s h => exchangeRange_finish s h stable odd)
      ((exchangeFinish_ct stable h4 h32 saved).seq status_ct))

end VG.Proof.Ffdh.Arm.SharedDerive
