module

public import VerifiedGarbage.Spec.Ffdh.DerivePublicContract
public import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
public import VerifiedGarbage.Impl.Bignum.Arm.MontCall
public import VerifiedGarbage.Impl.Ffdh.Arm.SharedDerive
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Ffdh.Arm.ScalarRange
import VerifiedGarbage.Proof.Ffdh.Arm.ScalarRangeCT
import VerifiedGarbage.Proof.Ffdh.Arm.DomainNormalizedPrepareAt
import VerifiedGarbage.Proof.Ffdh.Arm.DomainNormalizedPrepareAtCT
import VerifiedGarbage.Proof.Ffdh.Arm.ImportAt
import VerifiedGarbage.Proof.Ffdh.Arm.ImportAtCT
import VerifiedGarbage.Proof.Ffdh.Arm.FlagCT
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ffdh.Arm.PrepareAt
import VerifiedGarbage.TCB.Arm.Isa
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Ffdh.Arm.StackCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Ffdh.Arm.Head
import VerifiedGarbage.Proof.Ffdh.Arm.HeadCT
import VerifiedGarbage.Proof.Ffdh.Arm.BranchCT
import VerifiedGarbage.Proof.Ffdh.Arm.FrameCT
import VerifiedGarbage.Proof.Ffdh.Arm.Entered
import VerifiedGarbage.Proof.Ffdh.Arm.Block
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import Batteries.Logic
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Ffdh.DerivePublicContract
meta import VerifiedGarbage.TCB.Arm.Target
public import Init.Core
import VerifiedGarbage.Proof.Ffdh.Arm.CheckPublicSpec
import VerifiedGarbage.Proof.Ffdh.Arm.DomainSpec
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Ffdh.Power
import VerifiedGarbage.Proof.Ffdh.KeyScalar
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Proof.Ffdh.Arm.SharedDeriveTail
import VerifiedGarbage.Proof.Ffdh.Arm.Branch
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Rsa.BytesFrame
public import VerifiedGarbage.Proof.Ffdh.Arm.Frame
public import VerifiedGarbage.Proof.Ffdh.Arm.IncomingWord
import VerifiedGarbage.Proof.Bignum.Arm.PcEntry
import VerifiedGarbage.Proof.Ffdh.Arm.EntryStore
public import VerifiedGarbage.Proof.Ffdh.Arm.ExchangeMainCT
public import VerifiedGarbage.Proof.Ffdh.Arm.SharedCheckPublicPower
import VerifiedGarbage.Proof.Ffdh.Arm.SharedCheckPublicPowerCT
import VerifiedGarbage.Proof.Ffdh.Arm.ExchangeFinishCT
import VerifiedGarbage.Proof.Ffdh.Arm.RangeCT
import VerifiedGarbage.Proof.Bignum.Arm.TwoExpSharedCT
import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Impl.Ffdh.Arm.SharedDerive
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import Init.Prelude

/-! ### `Ffdh.Arm.SharedDeriveVerified`, which only this module used -/

section

/-! ### `Ffdh.Arm.SharedDeriveTailCT`, which only this module used -/

section

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
  exact Nat.lt_trans (Nat.mod_lt _ (by have := h.ready.modulus; rw [h.modulus] at this; omega_using [odd])) p.modulusBound

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

end

end

/-! ### `Ffdh.Arm.SharedDerivePrograms`, which this module and modules that import it used -/

section

/-! ### `Ffdh.Arm.SharedDeriveCorrect`, which the modules that import this one used -/

section

/-! ### `Ffdh.Arm.SharedDerivePre`, which this module and modules that import it used -/

section

/-! ### `Ffdh.Arm.SharedDeriveFn`, which this module and modules that import it used -/

section

/-! ### `Ffdh.Arm.SharedDeriveMain`, which only this module used -/

section

/-! Modulus preparation, the scalar's range, and the derivation's two paths. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.SharedDerive
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt Operand arrAt)

/-- The scalar is in range and its public value is accepted. -/
def accepted (p : Inputs) (xb : List Byte) : Prop :=
  (0 < Spec.Rsa.os2ip xb ∧ Spec.Rsa.os2ip xb < scalarBound p) ∧ sharedAccepted p (gOctets p) xb = true

/-- The status returned: 2 for a scalar out of range, then 1 or 3 by y's range. -/
def status (p : Inputs) (xb : List Byte) : BitVec 32 :=
  if 0 < Spec.Rsa.os2ip xb ∧ Spec.Rsa.os2ip xb < scalarBound p then
    (if sharedAccepted p (gOctets p) xb then 1 else 3) else 2

def result (p : Inputs) (xb : List Byte) (s : State) : Prop :=
  s.gpr .r0 = status p xb ∧ Spec.Rsa.bytesAt s.mem (State.addr p.output) p.k =
    (open Classical in if accepted p xb then Spec.Rsa.i2osp (sharedValue p (gOctets p) xb) p.k
      else List.replicate p.k 0)

theorem main_ok (backend : MontBackend) (s : State) {p : Inputs} {slots : List Nat} {xb : List Byte}
    (h : Context p slots s) (calls : SharedExchange.CallMemory p xb.length s) (stable : stableSlots slots = true)
    (h0 : 0 ∈ slots) (h4 : 4 ∈ slots) (h24 : 24 ∈ slots) (h28 : 28 ∈ slots) (h32 : 32 ∈ slots)
    (h40 : 40 ∈ slots) (h44 : 44 ∈ slots) (h56 : 56 ∈ slots) (h60 : 60 ∈ slots)
    (saved : ∀ d ∈ slots, d + 4 ≤ 64 ∨ 68 ≤ d)
    (large : 1 < p.P) (odd : p.P % 2 = 1) (normalized : 2 ^ (64 * (p.w - 1)) ≤ p.P)
    (scalar : Octets p.base p.privateValue p.len xb s) (positive : 0 < xb.length)
    (scalarLength : xb.length ≤ p.k) (scalarCount : p.slotValue 44 = BitVec.ofNat 32 xb.length)
    (scalarStack : Region.Disjoint ⟨State.addr p.privateValue, xb.length⟩ ⟨State.addr s.sp, 72⟩)
    (output : OutputBuffer p.output p.k s)
    (workspaceSep : Region.Disjoint ⟨State.addr p.base, 8 * p.len⟩ ⟨State.addr p.output, p.k⟩)
    (stackSep : Region.Disjoint ⟨State.addr s.sp, 72⟩ ⟨State.addr p.output, p.k⟩) :
    WP isa (VG.Impl.Ffdh.Arm.SharedDerive.main (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul)) s
      fun t => result p xb t ∧ Frame (SharedExchange.writes p s) s.mem t.mem := by
  obtain op0 : Operand 0 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  obtain op4 : Operand 4 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have extend {m m' : Mem} (f : Frame [⟨State.addr p.base, 8 * p.len⟩] m m') :
      Frame (SharedExchange.writes p s) m m' :=
    f.mono (by simp [SharedExchange.writes, exchangeWrites])
  rw [VG.Impl.Ffdh.Arm.SharedDerive.main, WP.seq_iff]
  refine WP.mono (domainNormalizedPrepareAt24_ok backend s h calls.toDomainCallMemory stable h0 h24 h32
    large odd normalized) ?_
  rintro u ⟨contextU, readyU, modU, r2U, frameU, restU⟩
  obtain scalarU := scalar.after_frame frameU restU (by
    intro r hr
    simp only [domainPrepareWrites, prepareAtWrites, prepareWrites, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl | rfl) | rfl
    · exact scalar.separate
    · exact scalarStack.sub_right (Offset.sub_base _ (by decide))
    · exact scalarStack.sub_right (Offset.sub_base _ (by decide))
    · exact calls.scalarBelow)
  obtain fU : Frame (SharedExchange.writes p s) s.mem u.mem := frameU.sub (by
    intro r hr
    simp only [domainPrepareWrites, prepareAtWrites, prepareWrites, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl | rfl) | rfl
    · exact ⟨⟨State.addr p.base, 8 * p.len⟩, by simp [SharedExchange.writes, exchangeWrites],
        by intro a ha; exact ha⟩
    · exact ⟨⟨State.addr s.sp, 72⟩, by simp [SharedExchange.writes, exchangeWrites], Offset.sub_base _ (by decide)⟩
    · exact ⟨⟨State.addr s.sp, 72⟩, by simp [SharedExchange.writes, exchangeWrites], Offset.sub_base _ (by decide)⟩
    · exact ⟨FrameStack.belowA s.sp 48, by simp [SharedExchange.writes], by intro a ha; exact ha⟩)
  rw [WP.seq_iff]
  refine WP.mono (importAt_ok u 1 40 44 contextU stable h40 h44 readyU (by decide) (by decide)
    scalarU positive (Nat.le_trans scalarLength p.width.2.2.2.1) scalarCount) ?_
  rintro v ⟨contextV, readyV, x, keepsV, frameV, restV⟩
  obtain fits : arrAt p.w 8 ≤ 8 * p.len := readyV.width ▸ readyV.layout.2.2.1
  obtain modV := (keeps_array_num keepsV fits op0 (by decide)).trans modU
  obtain r2V := (keeps_array_num keepsV fits op4 (by decide)).trans r2U
  rw [WP.seq_iff]
  refine WP.mono (scalarRange_ok v contextV stable h28 h32 h60 readyV modV odd) ?_
  rintro w ⟨contextW, readyW, flag, arraysW, frameW, restW⟩
  rw [x] at flag
  obtain modW := (arraysW 0 (by simp)).trans modV
  obtain r2W := (arraysW 4 (by simp)).trans r2V
  obtain scalarW := (scalarU.after_workspace frameV restV).after_workspace frameW restW
  obtain fUW := (fU.trans (extend frameV)).trans (extend frameW)
  obtain restUW := (restU.trans restV).trans restW
  rw [VG.Impl.Ffdh.Arm.Domain.ifFlag, WP.seq_iff]
  refine WP.mono (testFlag_ok w) ?_
  rintro z ⟨⟨zeroZ, memZ⟩, restZ⟩
  obtain ptrZ := (restZ.gpr .r0 (by simp)).trans contextW.ptr
  obtain contextZ := contextW.of_mem memZ restZ ptrZ
  obtain restSZ := restUW.trans (restZ.mono (by simp))
  by_cases valid : 0 < Spec.Rsa.os2ip xb ∧ Spec.Rsa.os2ip xb < scalarBound p
  · refine WP.ite true (by change some (!z.z) = some true; rw [zeroZ, flag, scalarValidFlag, ite_eq_left valid]; rfl) ?_ (by intro hf; cases hf)
    intro _
    obtain frameZ : Frame [⟨State.addr p.base, 8 * p.len⟩] w.mem z.mem := by rw [memZ]; exact Frame.refl _ _
    refine WP.mono (tail_ok backend z contextZ ⟨calls.toDomainCallMemory.after restSZ,
        by rw [restSZ.sp]; exact calls.scalarBelow, by rw [restSZ.sp]; exact calls.outputBelow⟩
      stable h4 h32 h40 h44 h56 saved odd
      (readyW.of_mem memZ restZ ptrZ) (by rw [memZ]; exact modW) (by rw [memZ]; exact r2W)
      (scalarW.after_workspace frameZ restZ) positive (by have := p.maxLength; omega_using [scalarLength, this]) scalarCount
      (output.after restSZ) workspaceSep (by rw [restSZ.sp]; exact stackSep)) ?_
    rintro t ⟨status_t, bytes, frameT⟩
    refine ⟨⟨by rw [status, ite_eq_left valid]; exact status_t, ?_⟩, ?_⟩
    · rw [bytes]
      by_cases acc : sharedAccepted p (gOctets p) xb = true
      · rw [ite_eq_left acc, ite_eq_left ⟨valid, acc⟩]
      · rw [ite_eq_right acc, ite_eq_right (fun h => acc h.2)]
    · have fT := frameT
      simp only [SharedExchange.writes, exchangeWrites, restSZ.sp] at fT
      exact (fUW.trans (by rw [memZ]; exact Frame.refl _ _)).trans fT
  · refine WP.ite false (by change some (!z.z) = some false; rw [zeroZ, flag, scalarValidFlag, ite_eq_right valid]; rfl) (by intro ht; cases ht) ?_
    intro _
    obtain flagZ : z.gpr .r11 = 0 := by
      rw [restZ.gpr .r11 (by simp), flag, scalarValidFlag, ite_eq_right valid]
    refine WP.mono (fail_ok z contextZ h4 h32 flagZ (output.after restSZ) (by rw [restSZ.sp]; exact stackSep)) ?_
    rintro t ⟨status_t, bytes, frameT⟩
    refine ⟨⟨by rw [status, ite_eq_right valid]; exact status_t, ?_⟩, ?_⟩
    · rw [bytes, ite_eq_right (fun h => valid h.1)]
    · have fT : Frame (SharedExchange.writes p s) z.mem t.mem := frameT.mono (by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> simp [SharedExchange.writes, exchangeWrites, restSZ.sp])
      exact (fUW.trans (by rw [memZ]; exact Frame.refl _ _)).trans fT

end VG.Proof.Ffdh.Arm.SharedDerive

end

end

/-! The AAPCS derivation of an imported scalar's public value. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/SharedDeriveEntry.lean`, which only this module imported.
section

/-! Retain the public-value derivation's output, domain, scalar, and workspace arguments. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

structure DeriveIncoming (p : Inputs) (s : State) : Prop where
  modulus : IncomingWord (BitVec.ofNat 32 p.k) 128 s
  scalar : IncomingWord p.privateValue 132 s
  scalarCount : IncomingWord (BitVec.ofNat 32 p.privateLength) 136 s
  scratch : IncomingWord p.base 140 s

theorem deriveEntry_ok (s : State) {p : Inputs} (h : ArgumentMemory p [] s)
    (incoming : DeriveIncoming p s) (out : s.gpr .r0 = p.output)
    (domain : s.gpr .r2 = p.domain) (domainLength : s.gpr .r3 = BitVec.ofNat 32 p.dom.length) :
    WP isa (.block VG.Impl.Ffdh.Arm.SharedDerive.entry) s fun t =>
      Context p [0, 44, 40, 32, 28, 24, 4] t ∧ Frame [⟨State.addr s.sp, 72⟩] s.mem t.mem := by
  unfold VG.Impl.Ffdh.Arm.SharedDerive.entry VG.Impl.Ffdh.Arm.Domain.st
  refine wp_stackAddr (by decide) fun s0 moved => ?_
  obtain rest0 : Rest [.r12] s s0 := moved.rest (by simp)
  obtain args0 := h.of_mem moved.mem rest0
  obtain frame0 : Frame [⟨State.addr s.sp, 72⟩] s.mem s0.mem := by rw [moved.mem]; exact Frame.refl _ _
  obtain stack0 : s0.gpr .r12 = s0.sp := by rw [moved.gpr, moved.sp, BitVec.add_zero]
  refine wp_store_arg .r0 4 args0 (by decide) (by decide) (by decide)
    ((rest0.gpr .r0 (by simp)).trans out) stack0 fun s1 args1 stepFrame1 stepRest1 => ?_
  obtain rest1 := rest0.trans (stepRest1.mono (by simp))
  obtain stack1 := (stepRest1.gpr .r12 (by simp)).trans (stack0.trans stepRest1.sp.symm)
  rw [rest0.sp] at stepFrame1
  obtain frame1 := frame0.trans stepFrame1
  refine wp_store_arg .r2 24 args1 (by decide) (by decide) (by decide)
    ((rest1.gpr .r2 (by simp)).trans domain) stack1 fun s2 args2 stepFrame2 stepRest2 => ?_
  obtain rest2 := rest1.trans (stepRest2.mono (by simp))
  obtain stack2 := (stepRest2.gpr .r12 (by simp)).trans (stack1.trans stepRest2.sp.symm)
  rw [rest1.sp] at stepFrame2
  obtain frame2 := frame1.trans stepFrame2
  refine wp_store_arg .r3 28 args2 (by decide) (by decide) (by decide)
    ((rest2.gpr .r3 (by simp)).trans domainLength) stack2 fun s3 args3 stepFrame3 stepRest3 => ?_
  obtain rest3 := rest2.trans (stepRest3.mono (by simp))
  obtain stack3 := (stepRest3.gpr .r12 (by simp)).trans (stack2.trans stepRest3.sp.symm)
  rw [rest2.sp] at stepFrame3
  obtain frame3 := frame2.trans stepFrame3
  obtain allRest3 : Rest roundClobbers s s3 := rest3.mono (by simp [roundClobbers])
  refine wp_retain_incoming .r3 (by decide) args3 (by decide)
    (incoming.modulus.after (by decide) frame3 allRest3) (by decide) (by decide) (by decide) stack3
    fun s4 args4 stepFrame4 stepRest4 value4 stack4 => ?_
  obtain allRest4 := allRest3.trans (stepRest4.mono (by simp [roundClobbers]))
  rw [allRest3.sp] at stepFrame4
  obtain frame4 := frame3.trans stepFrame4
  refine wp_retain_incoming .r3 (by decide) args4 (by decide)
    (incoming.scalar.after (by decide) frame4 allRest4) (by decide) (by decide) (by decide) stack4
    fun s5 args5 stepFrame5 stepRest5 value5 stack5 => ?_
  obtain allRest5 := allRest4.trans (stepRest5.mono (by simp [roundClobbers]))
  rw [allRest4.sp] at stepFrame5
  obtain frame5 := frame4.trans stepFrame5
  refine wp_retain_incoming .r3 (by decide) args5 (by decide)
    (incoming.scalarCount.after (by decide) frame5 allRest5) (by decide) (by decide) (by decide) stack5
    fun s6 args6 stepFrame6 stepRest6 value6 stack6 => ?_
  obtain allRest6 := allRest5.trans (stepRest6.mono (by simp [roundClobbers]))
  rw [allRest5.sp] at stepFrame6
  obtain frame6 := frame5.trans stepFrame6
  refine wp_retain_incoming .r0 (by decide) args6 (by decide)
    (incoming.scratch.after (by decide) frame6 allRest6) (by decide) (by decide) (by decide) stack6
    fun s7 args7 stepFrame7 stepRest7 value7 stack7 => WP.block_nil ?_
  refine ⟨⟨args7, value7⟩, ?_⟩
  rw [allRest6.sp] at stepFrame7
  exact frame6.trans stepFrame7

end VG.Proof.Ffdh.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/SharedDeriveBody.lean`, which only this module imported.
section

/-! The derivation's body is safe for every domain encoding, and specified for valid moduli. -/

section
namespace VG.Proof.Ffdh.Arm.SharedDerive
open VG VG.Arm VG.Proof.Bignum.Arm

theorem body_ok (backend : MontBackend) (s : State) {p : Inputs} {slots : List Nat} {xb : List Byte}
    (h : Context p slots s) (calls : SharedExchange.CallMemory p xb.length s) (stable : stableSlots slots = true)
    (h0 : 0 ∈ slots) (h4 : 4 ∈ slots) (h24 : 24 ∈ slots) (h28 : 28 ∈ slots) (h32 : 32 ∈ slots)
    (h40 : 40 ∈ slots) (h44 : 44 ∈ slots)
    (saved : ∀ d ∈ slots, d + 4 ≤ 64 ∨ 68 ≤ d)
    (scalar : Octets p.base p.privateValue p.len xb s) (positive : 0 < xb.length)
    (scalarLength : xb.length ≤ p.k) (scalarCount : p.slotValue 44 = BitVec.ofNat 32 xb.length)
    (scalarStack : Region.Disjoint ⟨State.addr p.privateValue, xb.length⟩ ⟨State.addr s.sp, 72⟩)
    (output : OutputBuffer p.output p.k s)
    (workspaceSep : Region.Disjoint ⟨State.addr p.base, 8 * p.len⟩ ⟨State.addr p.output, p.k⟩)
    (stackSep : Region.Disjoint ⟨State.addr s.sp, 72⟩ ⟨State.addr p.output, p.k⟩) :
    WP isa (VG.Impl.Ffdh.Arm.Domain.head
      (VG.Impl.Ffdh.Arm.SharedDerive.main (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul))) s fun t =>
      (Spec.Rsa.modulusValid p.P p.k = true → result p xb t) ∧
      Frame (SharedExchange.writes p s) s.mem t.mem := by
  unfold VG.Impl.Ffdh.Arm.Domain.head
  apply WP.assoc
  rw [WP.seq_iff]
  refine WP.mono (head_ok s h stable h0 h24 h32) ?_
  rintro u ⟨context, zero, frame, rest⟩
  obtain entryFrame : Frame (SharedExchange.writes p s) s.mem u.mem :=
    frame.mono (by simp [SharedExchange.writes, exchangeWrites])
  by_cases valid : Spec.Rsa.modulusValid p.P p.k = true
  · refine WP.ite true (by change some u.z = some true; rw [zero, valid]) ?_ (by intro hf; cases hf)
    intro _
    obtain facts := VG.Proof.Bignum.valid_facts valid p.minLength
    obtain stable' : stableSlots (60 :: 56 :: slots) = true := by
      change (true && (true && stableSlots slots)) = true
      rw [Bool.true_and, Bool.true_and, stable]
    obtain saved' : ∀ d ∈ 60 :: 56 :: slots, d + 4 ≤ 64 ∨ 68 ≤ d := by
      intro d hd
      simp only [List.mem_cons] at hd
      rcases hd with rfl | rfl | hd
      · exact Or.inl (by decide)
      · exact Or.inl (by decide)
      · exact saved d hd
    refine WP.mono (main_ok backend u context (calls.after rest) stable' (by simp [h0]) (by simp [h4])
      (by simp [h24]) (by simp [h28]) (by simp [h32]) (by simp [h40]) (by simp [h44]) (by simp) (by simp)
      saved' facts.2.1 facts.1 facts.2.2
      (scalar.after_frame frame rest (by
        intro r hr; rw [List.mem_singleton] at hr; subst r; exact scalarStack))
      positive scalarLength scalarCount (by rw [rest.sp]; exact scalarStack) (output.after rest)
      workspaceSep (by rw [rest.sp]; exact stackSep)) ?_
    rintro t ⟨res, frameT⟩
    exact ⟨fun _ => res, entryFrame.trans (by simpa only [SharedExchange.writes, exchangeWrites, rest.sp] using frameT)⟩
  · refine WP.ite false (by change some u.z = some false; rw [zero, Bool.eq_false_iff.mpr valid])
      (by intro ht; cases ht) ?_
    intro _
    refine WP.mono (ret_ok u 0 (by decide)) ?_
    rintro t ⟨⟨_, mem⟩, _⟩
    exact ⟨fun hv => (valid hv).elim, by rw [mem]; exact entryFrame⟩

end VG.Proof.Ffdh.Arm.SharedDerive
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm.SharedDerive
open VG VG.Arm VG.Proof.Bignum.Arm

theorem entered_ok (backend : MontBackend) (s : State) {p : Inputs} {xb : List Byte}
    (h : ArgumentMemory p [] s) (incoming : DeriveIncoming p s) (calls : SharedExchange.CallMemory p xb.length s)
    (out : s.gpr .r0 = p.output) (domain : s.gpr .r2 = p.domain)
    (domainLength : s.gpr .r3 = BitVec.ofNat 32 p.dom.length)
    (scalar : Octets p.base p.privateValue p.len xb s) (positive : 0 < xb.length)
    (scalarLength : xb.length ≤ p.k) (scalarCount : p.slotValue 44 = BitVec.ofNat 32 xb.length)
    (scalarStack : Region.Disjoint ⟨State.addr p.privateValue, xb.length⟩ ⟨State.addr s.sp, 72⟩)
    (output : OutputBuffer p.output p.k s)
    (workspaceSep : Region.Disjoint ⟨State.addr p.base, 8 * p.len⟩ ⟨State.addr p.output, p.k⟩)
    (stackSep : Region.Disjoint ⟨State.addr s.sp, 72⟩ ⟨State.addr p.output, p.k⟩) :
    WP isa (.seq (.block VG.Impl.Ffdh.Arm.SharedDerive.entry)
      (VG.Impl.Ffdh.Arm.Domain.head
        (VG.Impl.Ffdh.Arm.SharedDerive.main (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul)))) s
      fun t => (Spec.Rsa.modulusValid p.P p.k = true → result p xb t) ∧
        Frame (SharedExchange.writes p s) s.mem t.mem := by
  rw [WP.seq_iff]
  refine WP.mono (withAllRest (deriveEntry_ok s h incoming out domain domainLength)) ?_
  rintro u ⟨⟨context, frame⟩, rest⟩
  refine WP.mono (body_ok backend u context (calls.after rest) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by intro d hd; revert d; decide)
    (scalar.after_frame frame rest (by intro r hr; rw [List.mem_singleton] at hr; subst r; exact scalarStack))
    positive scalarLength scalarCount (by rw [rest.sp]; exact scalarStack) (output.after rest)
    workspaceSep (by rw [rest.sp]; exact stackSep)) ?_
  rintro t ⟨res, frameT⟩
  obtain entryFrame : Frame (SharedExchange.writes p s) s.mem u.mem :=
    frame.mono (by simp [SharedExchange.writes, exchangeWrites])
  exact ⟨res, entryFrame.trans (by simpa only [SharedExchange.writes, exchangeWrites, rest.sp] using frameT)⟩

structure FnInput (p : Inputs) (xb : List Byte) (s : State) : Prop where
  stackFits : 128 ≤ s.sp.toNat
  args : ArgumentMemory p [] (entered s)
  incoming : DeriveIncoming p (entered s)
  calls : SharedExchange.CallMemory p xb.length (entered s)
  out : s.gpr .r0 = p.output
  domain : s.gpr .r2 = p.domain
  domainLength : s.gpr .r3 = BitVec.ofNat 32 p.dom.length
  scalar : Octets p.base p.privateValue p.len xb (entered s)
  positive : 0 < xb.length
  scalarLength : xb.length ≤ p.k
  scalarCount : p.slotValue 44 = BitVec.ofNat 32 xb.length
  scalarStack : Region.Disjoint ⟨State.addr p.privateValue, xb.length⟩ ⟨State.addr (entered s).sp, 72⟩
  output : OutputBuffer p.output p.k (entered s)
  workspaceSep : Region.Disjoint ⟨State.addr p.base, 8 * p.len⟩ ⟨State.addr p.output, p.k⟩
  stackSep : Region.Disjoint ⟨State.addr (entered s).sp, 72⟩ ⟨State.addr p.output, p.k⟩
  saved : ∀ r ∈ SharedExchange.writes p (entered s), (⟨State.addr (pcPushed s).sp, 56⟩ : Region).Disjoint r

theorem fn_ok (backend : MontBackend) (s : State) {p : Inputs} {xb : List Byte} (h : FnInput p xb s) :
    WP isa (VG.Impl.Ffdh.Arm.SharedDerive.code (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul)) s
      fun t => abiPreserved s t ∧ (Spec.Rsa.modulusValid p.P p.k = true → result p xb t) := by
  unfold VG.Impl.Ffdh.Arm.SharedDerive.code
  refine framed_of_separate _ s h.stackFits (SharedExchange.writes p (entered s))
    (fun m status => Spec.Rsa.modulusValid p.P p.k = true → status = SharedDerive.status p xb ∧
      Spec.Rsa.bytesAt m (State.addr p.output) p.k =
        (open Classical in if accepted p xb then Spec.Rsa.i2osp (sharedValue p (gOctets p) xb) p.k
          else List.replicate p.k 0)) h.saved ?_ ?_
  · refine WP.mono (entered_ok backend (entered s) h.args h.incoming h.calls h.out h.domain h.domainLength
      h.scalar h.positive h.scalarLength h.scalarCount h.scalarStack h.output h.workspaceSep h.stackSep) ?_
    rintro t ⟨res, frame⟩
    exact ⟨frame, res⟩
  · intro m₁ m₂ v hf hq hv
    obtain ⟨hs, he⟩ := hq hv
    refine ⟨hs, ?_⟩
    rw [VG.Proof.Rsa.rsa_bytes_frame hf (by have := h.output.fits; omega_using [this]) ?_]
    · exact he
    · intro r hr
      simp only [released, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (h.saved _ (by simp [SharedExchange.writes, exchangeWrites])).symm
      · exact h.stackSep.symm

end VG.Proof.Ffdh.Arm.SharedDerive

end

end

/-! The derivation's signature supplies its native buffers and incoming argument words; it
reserves the outer frame plus the callable arithmetic stack. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.SharedDerive
open VG VG.Arm VG.Arm.FrameStack VG.Proof.Bignum.Arm VG.Proof.Mont

theorem input (s : State) (pre : (Spec.Ffdh.derivePublicContract abi 176).pre s)
    {p : Inputs} {xb : List Byte}
    (base : stackArg s 3 = p.base) (out : s.gpr .r0 = p.output) (domain : s.gpr .r2 = p.domain)
    (scalar : stackArg s 1 = p.privateValue) (publicValue : p.publicValue = p.domain)
    (count : (stackArg s 0).toNat = p.k) (capacity : (stackArg s 4).toNat = p.len)
    (privateCount : (stackArg s 2).toNat = p.privateLength)
    (domainBytes : Spec.Rsa.bytesAt s.mem (State.addr p.domain) (s.gpr .r3).toNat = p.dom)
    (scalarBytes : Spec.Rsa.bytesAt s.mem (State.addr p.privateValue) p.privateLength = xb) :
    FnInput p xb s := by
  sig_pre [Spec.Ffdh.derivePublicContract, Spec.Ffdh.derivePublicSig, abi, argRegs, reduceClassify,
    Loc.val, State.addr] at pre
  obtain ⟨stackFit, argFit, rd, wr, outDom, outX, outS, outArgs, domS, xS, sArgs,
    stackOut, stackDom, stackX, stackS, stackArgs, outFit, domFit, xFit, sFit,
    _, _, outLen, xPositive, xMax, _⟩ := pre
  have domLen : (s.gpr .r3).toNat = p.dom.length := by
    have eq := congrArg List.length domainBytes
    simpa only [VG.Proof.Bignum.bytesAt_length] using eq
  have xLength : xb.length = p.privateLength := by
    have eq := congrArg List.length scalarBytes
    simpa only [VG.Proof.Bignum.bytesAt_length] using eq.symm
  rw [count] at outLen xMax
  rw [outLen] at wr outDom outX outS outArgs stackOut outFit
  rw [privateCount] at rd outX xS stackX xFit xPositive xMax
  rw [out] at wr outDom outX outS outArgs stackOut outFit
  rw [domain, domLen] at rd outDom domS stackDom domFit
  rw [scalar] at rd outX xS stackX xFit
  rw [base, capacity, Nat.mul_comm p.len 8] at wr outS domS xS sArgs stackS sFit
  have reserved : State.addr s.sp - BitVec.ofNat 64 176 = State.addr (s.sp - BitVec.ofNat 32 176) :=
    (addr_sub' stackFit).symm
  simp only [State.addr] at reserved
  rw [reserved] at stackOut stackDom stackX stackS stackArgs
  have inner : Region.Sub (belowA s.sp 128) (belowA s.sp 176) := by
    simp only [belowA]
    rw [addr_sub' (by omega_using [stackFit] : 128 ≤ s.sp.toNat), addr_sub' stackFit]
    exact Offset.below_mono _ (by decide) (by decide)
  have stackFit' : 128 ≤ s.sp.toNat := by omega_using [stackFit]
  have ws : Workspace s p.base (8 * p.len) := ⟨sFit, by rw [wr]; simp [State.addr]⟩
  have domainRead : InRegions (s.rd ++ s.wr) (State.addr p.domain) p.dom.length :=
    ⟨⟨State.addr p.domain, p.dom.length⟩, List.mem_append_left _ (by rw [rd]; simp [State.addr]),
      Region.contains_self _ _⟩
  have scalarRead : InRegions (s.rd ++ s.wr) (State.addr p.privateValue) p.privateLength :=
    ⟨⟨State.addr p.privateValue, p.privateLength⟩, List.mem_append_left _ (by rw [rd]; simp [State.addr]),
      Region.contains_self _ _⟩
  have rootDomain : Octets p.base p.domain p.len p.dom s :=
    ⟨domFit, domainRead, domS, by rw [← domLen]; exact domainBytes⟩
  have rootScalar : Octets p.base p.privateValue p.len xb s :=
    ⟨by rw [xLength]; exact xFit, by rw [xLength]; exact scalarRead,
      by rw [xLength]; exact xS, by rw [xLength]; exact scalarBytes⟩
  have stackDom' := stackDom.sub_left inner
  have stackS' := stackS.sub_left inner
  have stackX' := stackX.sub_left inner
  have stackOut' := stackOut.sub_left inner
  have args : ArgumentMemory p [] (entered s) :=
    ⟨entered_workspace ws, entered_locals s stackFit' stackS', entered_octets rootDomain stackFit' stackDom',
      stackDom'.symm.sub_right (locals_sub_reserved s stackFit'), by simp⟩
  have argStart : stackArgAddr s 0 = State.addr s.sp := by simp [stackArgAddr]
  have argAddr (i : Nat) (hi : i < 5) : stackArgAddr s i = off (State.addr s.sp) (4 * i) :=
    VG.Arm.addr_add (by omega_using [argFit, hi])
  have argSub (i : Nat) (hi : i < 5) :
      (⟨stackArgAddr s i, 4⟩ : Region).Sub ⟨stackArgAddr s 0, 20⟩ := by
    rw [argStart, argAddr i hi]
    exact Offset.sub_base _ (by omega_using [hi])
  have incoming (i : Nat) (hi : i < 5) : IncomingWord (stackArg s i) (128 + 4 * i) (entered s) :=
    enteredIncoming s stackFit' (by omega_using [argFit, hi])
      ⟨⟨stackArgAddr s 0, 20⟩, List.mem_append_left _ (by rw [rd]; simp), by
        rw [argStart, argAddr i hi]; exact Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩
      ((stackArgs.sub_left inner).sub_right (argSub i hi)) rfl
  have nativeIncoming : DeriveIncoming p (entered s) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · have h := incoming 0 (by decide)
      rw [← count, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      exact h
    · rw [← scalar]; exact incoming 1 (by decide)
    · have h := incoming 2 (by decide)
      rw [← privateCount, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      exact h
    · rw [← base]; exact incoming 3 (by decide)
  have outWrite : InRegions (entered s).wr (State.addr p.output) p.k :=
    ⟨⟨State.addr p.output, p.k⟩, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (by rw [wr]; simp [State.addr])),
      Region.contains_self _ _⟩
  have pLen : p.k ≤ p.dom.length := by rw [p.domainLength]; split <;> omega_using []
  have pubStack : Region.Disjoint ⟨State.addr p.publicValue, p.k⟩ (belowA s.sp 176) := by
    rw [publicValue]
    exact stackDom.symm.sub_left (Region.sub_prefix pLen)
  have calls := SharedExchange.CallMemory.of_outer (p := p) (n := xb.length) stackFit (entered_sp s)
    stackS stackDom.symm pubStack (by rw [xLength]; exact stackX.symm) stackOut.symm
  refine ⟨stackFit', args, nativeIncoming, calls, out, domain, ?_,
    entered_octets rootScalar stackFit' (by rw [xLength]; exact stackX'),
    by rw [xLength]; omega_using [xPositive], by rw [xLength]; omega_using [xMax], ?_, ?_,
    ⟨outFit, outWrite⟩, outS.symm, stackOut'.sub_left (locals_sub_reserved s stackFit'), ?_⟩
  · rw [← domLen, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · change BitVec.ofNat 32 p.privateLength = _; rw [xLength]
  · rw [xLength]; exact stackX'.symm.sub_right (locals_sub_reserved s stackFit')
  · intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · simp only [exchangeWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact stackS'.sub_left (saved_sub_reserved s stackFit')
      · exact saved_separate_locals s stackFit'
      · exact stackOut'.sub_left (saved_sub_reserved s stackFit')
    · have eq := List.mem_singleton.mp hr
      subst r
      have shifted : (pcPushed s).sp = (entered s).sp + BitVec.ofNat 32 72 := (BitVec.sub_add_cancel _ _).symm
      have fit : (entered s).sp.toNat + 72 < 2^32 := by
        rw [entered_nat s stackFit']; have := s.sp.isLt; omega_using []
      rw [shifted, VG.Arm.addr_add fit, belowA, addr_sub' calls.stack.fit]
      exact (Offset.disjoint_below_above _ (m := 48) (a := 72) (l := 56) (by decide)).symm

end VG.Proof.Ffdh.Arm.SharedDerive

end

end

/-! The callable derivation satisfies the architecture-independent contract: its status is
`keyStatus`, since a power of the checked generator is in its subgroup. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.SharedDerive
open VG VG.Arm VG.Proof.Bignum.Arm

theorem scalar_iff (p : Inputs) (x : Nat) :
    Spec.Ffdh.privateValid (Spec.Ffdh.domainOf p.k p.dom) x = true ↔ 0 < x ∧ x < scalarBound p := by
  unfold Spec.Ffdh.privateValid scalarBound
  rw [p.domainP, p.domainQ]
  by_cases hasQ : p.hasQ = true <;> simp [hasQ]

/-- The status tells whether the scalar is in range, for any domain. -/
theorem keyStatus_two_iff (p : Inputs) (x : Nat) :
    Spec.Ffdh.keyStatus (Spec.Ffdh.domainOf p.k p.dom) x = 2 ↔ ¬ (0 < x ∧ x < scalarBound p) := by
  rw [← scalar_iff p x]
  unfold Spec.Ffdh.keyStatus
  cases Spec.Ffdh.privateValid (Spec.Ffdh.domainOf p.k p.dom) x
  · simp
  · simp only [Bool.not_true, Bool.false_eq_true, ite_false, not_true_eq_false, iff_false]
    split <;> decide

theorem status_spec (p : Inputs) (xb : List Byte) (valid : Spec.Ffdh.domainValid p.k p.dom = true) :
    (status p xb).toNat = Spec.Ffdh.keyStatus (Spec.Ffdh.domainOf p.k p.dom) (Spec.Rsa.os2ip xb) ∧
      (accepted p xb ↔ Spec.Ffdh.keyStatus (Spec.Ffdh.domainOf p.k p.dom) (Spec.Rsa.os2ip xb) = 1) := by
  have parameters : Spec.Ffdh.parametersValid (Spec.Ffdh.domainOf p.k p.dom) = true := by
    have h := valid
    rw [Spec.Ffdh.domainValid, Bool.and_eq_true] at h
    exact h.1
  have scalar := scalar_iff p (Spec.Rsa.os2ip xb)
  have power := VG.Proof.Ffdh.publicValid_power parameters (Spec.Rsa.os2ip xb)
  rw [VG.Proof.Ffdh.KeyScalar.keyStatus_eq parameters]
  rw [p.domainP, p.domainG] at power ⊢
  have shared : sharedAccepted p (gOctets p) xb = true ↔
      1 < p.G ^ Spec.Rsa.os2ip xb % p.P ∧ p.G ^ Spec.Rsa.os2ip xb % p.P < p.P - 1 := by
    simp only [sharedAccepted, sharedValue, gOctets, VG.Proof.Bignum.powMod_eq, decide_eq_true_eq]
    rfl
  unfold status accepted
  by_cases range : 0 < Spec.Rsa.os2ip xb ∧ Spec.Rsa.os2ip xb < scalarBound p
  · have pv : Spec.Ffdh.privateValid (Spec.Ffdh.domainOf p.k p.dom) (Spec.Rsa.os2ip xb) = true :=
      scalar.mpr range
    rw [ite_eq_left range, pv]
    by_cases acc : sharedAccepted p (gOctets p) xb = true
    · have pub := power.mpr (shared.mp acc)
      simp [acc, pub, range]
    · have pub : ¬ Spec.Ffdh.publicValid ⟨Spec.Ffdh.domainOf p.k p.dom, p.G ^ Spec.Rsa.os2ip xb % p.P⟩ = true :=
        fun h => acc (shared.mpr (power.mp h))
      simp [acc, pub, range]
  · have pv : Spec.Ffdh.privateValid (Spec.Ffdh.domainOf p.k p.dom) (Spec.Rsa.os2ip xb) = false := by
      cases e : Spec.Ffdh.privateValid (Spec.Ffdh.domainOf p.k p.dom) (Spec.Rsa.os2ip xb)
      · rfl
      · exact (range (scalar.mp e)).elim
    rw [ite_eq_right range, pv]
    simp [range]

theorem data (s : State) (pre : (Spec.Ffdh.derivePublicContract abi 176).pre s) :
    ∃ (p : Inputs) (xb : List Byte), stackArg s 3 = p.base ∧ s.gpr .r0 = p.output ∧
      s.gpr .r2 = p.domain ∧ stackArg s 1 = p.privateValue ∧ p.publicValue = p.domain ∧
      (stackArg s 0).toNat = p.k ∧ (stackArg s 4).toNat = p.len ∧ (stackArg s 2).toNat = p.privateLength ∧
      Spec.Rsa.bytesAt s.mem (State.addr p.domain) (s.gpr .r3).toNat = p.dom ∧
      Spec.Rsa.bytesAt s.mem (State.addr p.privateValue) p.privateLength = xb ∧ FnInput p xb s := by
  have original := pre
  sig_pre [Spec.Ffdh.derivePublicContract, Spec.Ffdh.derivePublicSig, abi, argRegs, reduceClassify,
    Loc.val, State.addr] at pre
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, bounds, domainLen, _, _, _, space⟩ := pre
  let dom := Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat
  have domLength : dom.length = (s.gpr .r3).toNat := VG.Proof.Bignum.bytesAt_length _ _ _
  let p : Inputs := {
    base := stackArg s 3
    domain := s.gpr .r2
    publicValue := s.gpr .r2
    privateValue := stackArg s 1
    output := s.gpr .r0
    entropy := 0
    len := (stackArg s 4).toNat
    k := (stackArg s 0).toNat
    privateLength := (stackArg s 2).toNat
    hasQ := decide ((s.gpr .r3).toNat = 3 * (stackArg s 0).toNat)
    dom := dom
    minLength := bounds.1
    maxLength := bounds.2
    space := space
    domainLength := by
      rw [domLength]
      simp only [decide_eq_true_eq]
      split
      · assumption
      · rename_i different
        rcases domainLen with h | h
        · exact h
        · exact False.elim (different h) }
  let xb := Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 1)) (stackArg s 2).toNat
  exact ⟨p, xb, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    input s original (p := p) (xb := xb) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩

theorem correct (backend : MontBackend) (s : State) (pre : (Spec.Ffdh.derivePublicContract abi 176).pre s) :
    ∃ tr t, Exec isa (VG.Impl.Ffdh.Arm.SharedDerive.code
        (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul)) s tr t ∧
      abiPreserved s t ∧ (Spec.Ffdh.derivePublicContract abi 176).post s t := by
  obtain ⟨p, xb, _, out, domain, scalar, _, count, _, privateCount, domainBytes, scalarBytes, input⟩ :=
    data s pre
  obtain ⟨tr, t, run, preserved, res⟩ := fn_ok backend s input
  refine ⟨tr, t, run, preserved, ?_⟩
  sig_post [Spec.Ffdh.derivePublicContract, Spec.Ffdh.derivePublicSig, abi, argRegs, reduceClassify,
    Loc.val, State.addr]
  rw [BitVec.setWidth_append_eq_right]
  simp only [State.addr] at domainBytes scalarBytes
  simp only [count, domain, scalar, privateCount, domainBytes, scalarBytes, out]
  intro valid
  have modValid := VG.Proof.Ffdh.domainValid_mod valid
  rw [p.domainP] at modValid
  obtain ⟨status_t, bytes⟩ := res modValid
  obtain ⟨statusEq, acceptedIff⟩ := status_spec p xb valid
  refine ⟨by rw [status_t]; exact statusEq, ?_⟩
  simp only [State.addr] at bytes
  by_cases acc : accepted p xb
  · rw [ite_eq_left (acceptedIff.mp acc), bytes, ite_eq_left acc]
    rfl
  · rw [ite_eq_right (fun h => acc (acceptedIff.mpr h)), bytes, ite_eq_right acc]

end VG.Proof.Ffdh.Arm.SharedDerive

end

end

/-! One public-value derivation program for every shared Montgomery backend. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.SharedDerive
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Bignum.Arm

def code (b : MontBackend) : Prog isa :=
  VG.Impl.Ffdh.Arm.SharedDerive.code (MontCall.op b.name b.mul)

end VG.Proof.Ffdh.Arm.SharedDerive

end

end

/-! ### `Ffdh.Arm.SharedDeriveContractCT`, which only this module used -/

section

/-! The derivation's timing depends on the domain, the lengths and the status alone. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/SharedDeriveMainCT.lean`, which only this module imported.
section

/-! The derivation branches only on the scalar's validity, which its status discloses. -/

section
namespace VG.Proof.Ffdh.Arm.SharedDerive
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt Operand arrAt)

structure MainInput (p : Inputs) (slots : List Nat) (xb : List Byte) (s : State) : Prop where
  context : Context p slots s
  calls : SharedExchange.CallMemory p xb.length s
  scalar : Octets p.base p.privateValue p.len xb s
  scalarStack : Region.Disjoint ⟨State.addr p.privateValue, xb.length⟩ ⟨State.addr s.sp, 72⟩
  output : OutputBuffer p.output p.k s
  workspaceSep : Region.Disjoint ⟨State.addr p.base, 8 * p.len⟩ ⟨State.addr p.output, p.k⟩
  stackSep : Region.Disjoint ⟨State.addr s.sp, 72⟩ ⟨State.addr p.output, p.k⟩

structure Imported (p : Inputs) (slots : List Nat) (xb : List Byte) (s : State) : Prop extends
    Prepared p slots xb s where
  imported : numAt s.mem (State.addr p.base) p.w 1 = Spec.Rsa.os2ip xb

structure Ranged (p : Inputs) (slots : List Nat) (xb : List Byte) (s : State) : Prop extends
    Prepared p slots xb s where
  flag : s.gpr .r11 = scalarValidFlag p (Spec.Rsa.os2ip xb)

theorem prepare_ready (backend : MontBackend) (s : State) {p : Inputs} {slots : List Nat} {xb : List Byte}
    (h : MainInput p slots xb s) (stable : stableSlots slots = true)
    (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h32 : 32 ∈ slots)
    (large : 1 < p.P) (odd : p.P % 2 = 1) (normalized : 2 ^ (64 * (p.w - 1)) ≤ p.P) :
    WP isa (VG.Impl.Ffdh.Arm.NormalizedPrepare.prepareAt
      (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul) 24) s (Prepared p slots xb) := by
  refine WP.mono (domainNormalizedPrepareAt24_ok backend s h.context h.calls.toDomainCallMemory stable h0 h24 h32
    large odd normalized) ?_
  rintro u ⟨context, ready, modulus, r2, frame, rest⟩
  refine ⟨context, ready, modulus, r2, h.calls.after rest, h.scalar.after_frame frame rest ?_,
    h.output.after rest, h.workspaceSep, by rw [rest.sp]; exact h.stackSep⟩
  intro r hr
  simp only [domainPrepareWrites, prepareAtWrites, prepareWrites, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hr
  rcases hr with (rfl | rfl | rfl) | rfl
  · exact h.scalar.separate
  · exact h.scalarStack.sub_right (Offset.sub_base _ (by decide))
  · exact h.scalarStack.sub_right (Offset.sub_base _ (by decide))
  · exact h.calls.scalarBelow

theorem import_ready (s : State) {p : Inputs} {slots : List Nat} {xb : List Byte}
    (h : Prepared p slots xb s) (stable : stableSlots slots = true) (h40 : 40 ∈ slots) (h44 : 44 ∈ slots)
    (positive : 0 < xb.length) (length : xb.length ≤ p.k) (count : p.slotValue 44 = BitVec.ofNat 32 xb.length) :
    WP isa (VG.Impl.Ffdh.Arm.Domain.importAt 1 40 44) s (Imported p slots xb) := by
  have op0 : Operand 0 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op4 : Operand 4 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  refine WP.mono (importAt_ok s 1 40 44 h.context stable h40 h44 h.ready (by decide) (by decide) h.scalar
    positive (Nat.le_trans length p.width.2.2.2.1) count) ?_
  rintro u ⟨context, ready, value, keeps, frame, rest⟩
  have fits : arrAt p.w 8 ≤ 8 * p.len := ready.width ▸ ready.layout.2.2.1
  exact ⟨⟨context, ready, (keeps_array_num keeps fits op0 (by decide)).trans h.modulus,
    (keeps_array_num keeps fits op4 (by decide)).trans h.r2, h.calls.after rest,
    h.scalar.after_workspace frame rest, h.output.after rest, h.workspaceSep,
    by rw [rest.sp]; exact h.stackSep⟩, value⟩

theorem range_ready (s : State) {p : Inputs} {slots : List Nat} {xb : List Byte}
    (h : Imported p slots xb s) (stable : stableSlots slots = true)
    (h28 : 28 ∈ slots) (h32 : 32 ∈ slots) (h60 : 60 ∈ slots) (odd : p.P % 2 = 1) :
    WP isa VG.Impl.Ffdh.Arm.Domain.CheckPrivate.scalarRange s (Ranged p slots xb) := by
  refine WP.mono (scalarRange_ok s h.context stable h28 h32 h60 h.ready h.modulus odd) ?_
  rintro u ⟨context, ready, flag, arrays, frame, rest⟩
  rw [h.imported] at flag
  exact ⟨⟨context, ready, (arrays 0 (by simp)).trans h.modulus, (arrays 4 (by simp)).trans h.r2,
    h.calls.after rest, h.scalar.after_workspace frame rest, h.output.after rest, h.workspaceSep,
    by rw [rest.sp]; exact h.stackSep⟩, flag⟩

theorem main_ct (backend : MontBackend) {p : Inputs} {slots : List Nat} {xb1 xb2 : List Byte}
    (stable : stableSlots slots = true) (h0 : 0 ∈ slots) (h4 : 4 ∈ slots) (h24 : 24 ∈ slots)
    (h28 : 28 ∈ slots) (h32 : 32 ∈ slots) (h40 : 40 ∈ slots) (h44 : 44 ∈ slots) (h56 : 56 ∈ slots)
    (h60 : 60 ∈ slots) (saved : ∀ d ∈ slots, d + 4 ≤ 64 ∨ 68 ≤ d)
    (positive : 0 < xb1.length) (scalarLength : xb1.length ≤ p.k)
    (count : p.slotValue 44 = BitVec.ofNat 32 xb1.length) (length : xb1.length = xb2.length)
    (classification : (0 < Spec.Rsa.os2ip xb1 ∧ Spec.Rsa.os2ip xb1 < scalarBound p) ↔
      (0 < Spec.Rsa.os2ip xb2 ∧ Spec.Rsa.os2ip xb2 < scalarBound p))
    (large : 1 < p.P) (odd : p.P % 2 = 1) (normalized : 2 ^ (64 * (p.w - 1)) ≤ p.P) :
    RelCT isa (fun s t => MainInput p slots xb1 s ∧ MainInput p slots xb2 t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.SharedDerive.main (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul))
      (fun _ _ => True) := by
  have fits : xb1.length < 2 ^ 32 := by have := p.maxLength; omega
  have prepare := (domainNormalizedPrepareAt24_ct backend stable h0 h24 h32 large odd normalized).mono
    (P' := fun (s t : State) => MainInput p slots xb1 s ∧ MainInput p slots xb2 t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨⟨h.1.context, h.1.calls.toDomainCallMemory⟩,
      ⟨h.2.1.context, h.2.1.calls.toDomainCallMemory⟩, h.2.2⟩) (fun _ _ h => h)
  have imports := (importAt_ct (p := p) (a := 1) (slot := 40) (k := xb1.length)
    stable h40 h44 count (by decide)).mono
    (P' := fun (s t : State) => Prepared p slots xb1 s ∧ Prepared p slots xb2 t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨⟨h.1.context, h.1.ready⟩, ⟨h.2.1.context, h.2.1.ready⟩, h.2.2⟩) (fun _ _ h => h)
  have ranges := (scalarRange_ct stable h28 h32 h60 odd).mono
    (P' := fun (s t : State) => Imported p slots xb1 s ∧ Imported p slots xb2 t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨⟨h.1.context, h.1.ready, h.1.modulus⟩, ⟨h.2.1.context, h.2.1.ready, h.2.1.modulus⟩, h.2.2⟩)
    (fun _ _ h => h)
  have branches : RelCT isa (fun s t => Ranged p slots xb1 s ∧ Ranged p slots xb2 t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.Domain.ifFlag
        (VG.Impl.Ffdh.Arm.SharedDerive.tail (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul))
        VG.Impl.Ffdh.Arm.SharedDerive.fail) (fun _ _ => True) := by
    apply ifFlag_pair_ct (decide (0 < Spec.Rsa.os2ip xb1 ∧ Spec.Rsa.os2ip xb1 < scalarBound p))
      (fun _ h => by simpa only [scalarValidFlag, decide_eq_true_eq] using h.flag)
      (fun _ h => by simpa only [scalarValidFlag, decide_eq_true_eq, ← classification] using h.flag)
      (fun _ _ h mem rest => ⟨h.toPrepared.after_mem mem rest, (rest.gpr .r11 (by simp)).trans h.flag⟩)
      (fun _ _ h mem rest => ⟨h.toPrepared.after_mem mem rest, (rest.gpr .r11 (by simp)).trans h.flag⟩)
    · intro _
      exact (tail_ct backend stable h4 h32 h40 h44 h56 saved positive fits count length odd).mono
        (fun _ _ h => ⟨h.1.toPrepared, h.2.1.toPrepared, h.2.2⟩) (fun _ _ h => h)
    · intro _
      exact (fail_ct h4 h32).mono
        (fun _ _ h => ⟨h.1.toPrepared, h.2.1.toPrepared, h.2.2⟩) (fun _ _ h => h)
  unfold VG.Impl.Ffdh.Arm.SharedDerive.main
  exact relCT_chain prepare
    (fun s h => prepare_ready backend s h stable h0 h24 h32 large odd normalized)
    (fun s h => prepare_ready backend s h stable h0 h24 h32 large odd normalized)
    (relCT_chain imports (fun s h => import_ready s h stable h40 h44 positive scalarLength count)
      (fun s h => import_ready s h stable h40 h44 (by rw [← length]; exact positive)
        (by rw [← length]; exact scalarLength) (by rw [← length]; exact count))
      (relCT_chain ranges (fun s h => range_ready s h stable h28 h32 h60 odd)
        (fun s h => range_ready s h stable h28 h32 h60 odd) branches))

end VG.Proof.Ffdh.Arm.SharedDerive
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/SharedDeriveEntryCT.lean`, which only this module imported.
section

/-! The public-value derivation's entry uses fixed local and incoming stack slots. -/

section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm

theorem deriveEntry_ct : RelCT isa (fun s t => s.sp = t.sp)
    (.block VG.Impl.Ffdh.Arm.SharedDerive.entry) (fun _ _ => True) := by
  have accesses := RelCT.block_append ((storeLocal_ct .r0 4).seq (RelCT.block_append ((storeLocal_ct .r2 24).seq (RelCT.block_append ((storeLocal_ct .r3 28).seq (RelCT.block_append ((loadLocal_ct .r3 128 (by decide)).seq (RelCT.block_append ((storeLocal_ct .r3 32).seq (RelCT.block_append ((loadLocal_ct .r3 132 (by decide)).seq (RelCT.block_append ((storeLocal_ct .r3 40).seq (RelCT.block_append ((loadLocal_ct .r3 136 (by decide)).seq (RelCT.block_append ((storeLocal_ct .r3 44).seq (RelCT.block_append ((loadLocal_ct .r0 140 (by decide)).seq ((storeLocal_ct .r0 0)))))))))))))))))))))
  exact (RelCT.block_append (stackAddr_ct.seq accesses)).mono
    (fun _ _ h => h) (fun _ _ _ => trivial)

end VG.Proof.Ffdh.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/SharedDeriveFnCT.lean`, which only this module imported.
section

/-! Invalid-domain handling, the entry and the frame reveal no scalar data: the complete
derivation is constant time for scalars of one length and validity. -/

section
namespace VG.Proof.Ffdh.Arm.SharedDerive
open VG VG.Arm VG.Proof.Bignum.Arm

theorem body_ct (backend : MontBackend) {p : Inputs} {slots : List Nat} {xb1 xb2 : List Byte}
    (stable : stableSlots slots = true) (h0 : 0 ∈ slots) (h4 : 4 ∈ slots) (h24 : 24 ∈ slots)
    (h28 : 28 ∈ slots) (h32 : 32 ∈ slots) (h40 : 40 ∈ slots) (h44 : 44 ∈ slots)
    (saved : ∀ d ∈ slots, d + 4 ≤ 64 ∨ 68 ≤ d)
    (positive : 0 < xb1.length) (scalarLength : xb1.length ≤ p.k)
    (count : p.slotValue 44 = BitVec.ofNat 32 xb1.length) (length : xb1.length = xb2.length)
    (classification : (0 < Spec.Rsa.os2ip xb1 ∧ Spec.Rsa.os2ip xb1 < scalarBound p) ↔
      (0 < Spec.Rsa.os2ip xb2 ∧ Spec.Rsa.os2ip xb2 < scalarBound p)) :
    RelCT isa (fun s t => MainInput p slots xb1 s ∧ MainInput p slots xb2 t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.Domain.head
        (VG.Impl.Ffdh.Arm.SharedDerive.main (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul)))
      (fun _ _ => True) := by
  let Q := fun (xb : List Byte) (s : State) => MainInput p (60 :: 56 :: slots) xb s ∧
    s.z = Spec.Rsa.modulusValid p.P p.k
  have head := (head_ct stable h0 h24 h32).mono
    (P' := fun (s t : State) => MainInput p slots xb1 s ∧ MainInput p slots xb2 t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨h.1.context, h.2.1.context, h.2.2⟩) (fun _ _ h => h)
  have wp (s : State) {xb : List Byte} (h : MainInput p slots xb s) :
      WP isa (.seq (.block (VG.Impl.Ffdh.Arm.Domain.prepareArgs 24 ++ VG.Impl.Ffdh.Arm.Domain.domainPointers))
        (.block VG.Impl.Bignum.Arm.modulusCheck)) s (Q xb) := by
    refine WP.mono (head_ok s h.context stable h0 h24 h32) ?_
    rintro u ⟨context, zero, frame, rest⟩
    exact ⟨⟨context, h.calls.after rest,
      h.scalar.after_frame frame rest (by
        intro r hr; rw [List.mem_singleton] at hr; subst r; exact h.scalarStack),
      by rw [rest.sp]; exact h.scalarStack, h.output.after rest, h.workspaceSep,
      by rw [rest.sp]; exact h.stackSep⟩, zero⟩
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
      (.ite .eq (VG.Impl.Ffdh.Arm.SharedDerive.main (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul))
        (VG.Impl.Ffdh.Arm.Domain.ret 0)) (fun _ _ => True) := by
    apply RelCT.ite (fun s t h => by change some s.z = some t.z; rw [h.1.2, h.2.1.2])
    · intro s t tr1 tr2 u v h e1 e2
      have valid : Spec.Rsa.modulusValid p.P p.k = true := by
        have selected := h.2
        change some s.z = some true at selected
        rw [h.1.1.2] at selected
        exact Option.some.inj selected
      have facts := VG.Proof.Bignum.valid_facts valid p.minLength
      exact main_ct backend stable' (by simp [h0]) (by simp [h4]) (by simp [h24]) (by simp [h28])
        (by simp [h32]) (by simp [h40]) (by simp [h44]) (by simp) (by simp) saved'
        positive scalarLength count length classification facts.2.1 facts.1 facts.2.2 s t tr1 tr2 u v
        ⟨h.1.1.1, h.1.2.1.1, h.1.2.2⟩ e1 e2
    · exact (ret_ct 0).mono (fun _ _ _ => trivial) (fun _ _ h => h)
  unfold VG.Impl.Ffdh.Arm.Domain.head
  apply RelCT.assoc
  exact relCT_chain head (fun s h => wp s h) (fun s h => wp s h) branches

theorem fn_ct (backend : MontBackend) {p : Inputs} {xb1 xb2 : List Byte} (length : xb1.length = xb2.length)
    (classification : (0 < Spec.Rsa.os2ip xb1 ∧ Spec.Rsa.os2ip xb1 < scalarBound p) ↔
      (0 < Spec.Rsa.os2ip xb2 ∧ Spec.Rsa.os2ip xb2 < scalarBound p)) :
    RelCT isa (fun s t => FnInput p xb1 s ∧ FnInput p xb2 t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.SharedDerive.code (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul))
      (fun _ _ => True) := by
  let P := fun (xb : List Byte) (a : State) => ∃ s, FnInput p xb s ∧ a = entered s
  have entry := deriveEntry_ct.mono
    (P' := fun (s t : State) => P xb1 s ∧ P xb2 t ∧ s.sp = t.sp)
    (fun _ _ h => h.2.2) (fun _ _ h => h)
  have wp (a : State) {xb : List Byte} (h : P xb a) :
      WP isa (.block VG.Impl.Ffdh.Arm.SharedDerive.entry) a (MainInput p [0, 44, 40, 32, 28, 24, 4] xb) := by
    obtain ⟨s, input, rfl⟩ := h
    refine WP.mono (withAllRest (deriveEntry_ok (entered s) input.args input.incoming input.out input.domain
      input.domainLength)) ?_
    rintro u ⟨⟨context, frame⟩, rest⟩
    exact ⟨context, input.calls.after rest,
      input.scalar.after_frame frame rest (by
        intro r hr; rw [List.mem_singleton] at hr; subst r; exact input.scalarStack),
      by rw [rest.sp]; exact input.scalarStack, input.output.after rest, input.workspaceSep,
      by rw [rest.sp]; exact input.stackSep⟩
  unfold VG.Impl.Ffdh.Arm.SharedDerive.code
  apply framed_ct (fun _ _ h => ⟨h.1.stackFits, h.2.1.stackFits⟩) (fun _ _ h => h.2.2)
  intro a b tr1 tr2 u v h e1 e2
  obtain ⟨s, t, related, rfl, rfl⟩ := h
  have body := relCT_chain entry (fun a h => wp a h) (fun a h => wp a h)
    (body_ct backend (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by intro d hd; revert d; decide) related.1.positive related.1.scalarLength
      related.1.scalarCount length classification)
  exact body _ _ _ _ _ _ ⟨⟨s, related.1, rfl⟩, ⟨t, related.2.1, rfl⟩,
    by rw [entered_sp, entered_sp, related.2.2]⟩ e1 e2

end VG.Proof.Ffdh.Arm.SharedDerive
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm.SharedDerive
open VG VG.Arm

theorem contract_ct (backend : Bignum.Arm.MontBackend) : ConstantTime isa
    (Spec.Ffdh.derivePublicContract abi 176).pre (Spec.Ffdh.derivePublicContract abi 176).pub
    (VG.Impl.Ffdh.Arm.SharedDerive.code (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul)) := by
  intro s t tr1 tr2 u v hs ht hp e1 e2
  obtain ⟨p, xb, base, out, domain, scalar, publicValue, count, capacity, privateCount,
    domainBytes, scalarBytes, inputS⟩ := data s hs
  sig_pub [Spec.Ffdh.derivePublicContract, Spec.Ffdh.derivePublicSig, abi, argRegs, reduceClassify,
    Loc.val, State.addr] at hp
  obtain ⟨sp, bytes, p0, _, p2, p3, p4, p5, p6, p7, p8⟩ := hp
  rw [← p2, ← p3, ← p4, ← p5, ← p6] at bytes
  obtain ⟨domEqNat, statusEq⟩ := List.append_inj bytes
    (by simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range])
  have recover {a b : List Byte} (h : a.map BitVec.toNat = b.map BitVec.toNat) : a = b := by
    have eq := congrArg (List.map (BitVec.ofNat 8)) h
    simpa only [List.map_map, Function.comp_def, BitVec.ofNat_toNat,
      BitVec.setWidth_eq, List.map_id'] using eq
  have domEq := recover domEqNat
  let xb2 := Spec.Rsa.bytesAt t.mem (State.addr p.privateValue) p.privateLength
  have domT : Spec.Rsa.bytesAt t.mem (State.addr p.domain) (s.gpr .r3).toNat = p.dom := by
    rw [← domain]
    change Spec.Rsa.bytesAt t.mem (BitVec.setWidth 64 (s.gpr .r2)) (s.gpr .r3).toNat = p.dom
    rw [← domEq, domain]
    exact domainBytes
  have inputT := input t ht (p := p) (xb := xb2)
    (p7.symm.trans base) (p0.symm.trans out) (p2.symm.trans domain) (p5.symm.trans scalar) publicValue
    (by rw [← p4]; exact count) (by rw [← p8]; exact capacity) (by rw [← p6]; exact privateCount)
    (by rw [← p3]; exact domT) rfl
  have xLength : xb.length = p.privateLength := by
    have eq := congrArg List.length scalarBytes
    simpa only [VG.Proof.Bignum.bytesAt_length] using eq.symm
  have x2Length : xb2.length = p.privateLength := VG.Proof.Bignum.bytesAt_length _ _ _
  have status : Spec.Ffdh.keyStatus (Spec.Ffdh.domainOf p.k p.dom) (Spec.Rsa.os2ip xb) =
      Spec.Ffdh.keyStatus (Spec.Ffdh.domainOf p.k p.dom) (Spec.Rsa.os2ip xb2) := by
    have eq := List.singleton_inj.mp statusEq
    simp only [State.addr] at domainBytes scalarBytes domT
    rw [count, scalar, privateCount, ← domEq, domain, domainBytes, scalarBytes] at eq
    exact eq
  have classification : (0 < Spec.Rsa.os2ip xb ∧ Spec.Rsa.os2ip xb < scalarBound p) ↔
      (0 < Spec.Rsa.os2ip xb2 ∧ Spec.Rsa.os2ip xb2 < scalarBound p) := by
    have a := keyStatus_two_iff p (Spec.Rsa.os2ip xb)
    have b := keyStatus_two_iff p (Spec.Rsa.os2ip xb2)
    rw [status] at a
    have n := a.symm.trans b
    exact ⟨fun h => Classical.byContradiction fun h2 => n.mpr h2 h,
      fun h => Classical.byContradiction fun h1 => n.mp h1 h⟩
  exact (fn_ct backend (by rw [xLength, x2Length]) classification s t tr1 tr2 u v
    ⟨inputS, inputT, sp⟩ e1 e2).1

end VG.Proof.Ffdh.Arm.SharedDerive

end

end


/-! The native ARMv7 derivation of an imported scalar's public value is verified against the
shared FFDH API. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.SharedDerive
open VG VG.Arm

private def deriveSat : State where
  gpr r := match r with | .r0 => 0x1000 | .r1 => 64 | .r2 => 0x2000 | .r3 => 128 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x8000 then 64 else if a = 0x8005 then 0x30 else if a = 0x8008 then 1 else
    if a = 0x800d then 0x40 else if a = 0x8010 then 0x20 else if a = 0x8011 then 4 else 0
  rd := [⟨0x2000, 128⟩, ⟨0x3000, 1⟩, ⟨0x8000, 20⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x4000, 8448⟩]

theorem sat : ∃ s, (Spec.Ffdh.derivePublicContract abi 176).pre s := by
  sig_implies_sat [Spec.Ffdh.derivePublicContract, Spec.Ffdh.derivePublicSig, Spec.Ffdh.pLenValid,
    Spec.Ffdh.domainLenValid, abi, argRegs, reduceClassify, Loc.val, State.addr]
    [deriveSat, stackArg, stackArgAddr, Mem.readW, Mem.read, Spec.Rsa.scratchWords] using deriveSat

theorem verified (backend : VG.Proof.Bignum.Arm.MontBackend) : Verified target (code backend)
    (Spec.Ffdh.derivePublicContract abi 176) :=
  ⟨correct backend, contract_ct backend, sat⟩

end VG.Proof.Ffdh.Arm.SharedDerive

end

end

/-! The backend's caller transformation preserves shared Montgomery calls. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.SharedDerive
open VG VG.Arm VG.Proof.Bignum.Arm

def calledCode (b : MontBackend) : Prog isa := b.caller.code (code b)

theorem called_verified (b : MontBackend) :
    Verified target (calledCode b) (Spec.Ffdh.derivePublicContract abi 176) :=
  b.caller.verified (verified b)

end VG.Proof.Ffdh.Arm.SharedDerive
