module

public import VerifiedGarbage.Impl.Bignum.Arm.MontCall
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Ffdh.Arm.DomainSharedPrepareAt
public import VerifiedGarbage.Impl.Ffdh.Arm.NormalizedPrepare
public import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
import VerifiedGarbage.Proof.Ffdh.Arm.NormalizedPrepareCT
import VerifiedGarbage.Proof.Ffdh.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.TwoExpSharedCT
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
public import VerifiedGarbage.Proof.Ffdh.Arm.DomainCallMemory
public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack
import VerifiedGarbage.Proof.Ffdh.Arm.NormalizedPrepare
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
import VerifiedGarbage.Proof.Bignum.Arm.TwoExpShared
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Impl.Ffdh.Arm.SharedCheckPublic
public import VerifiedGarbage.Proof.Ffdh.Arm.PowerAtCT
public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpMontgomeryCT
import VerifiedGarbage.Proof.Ffdh.Arm.KeyPowerCT
import VerifiedGarbage.Proof.Ffdh.Arm.PowerArgs
import VerifiedGarbage.Proof.Bignum.Arm.SharedWindowPhaseCT
public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpMontgomery

/-! ### `Ffdh.Arm.SharedCheckPublicPowerCT`, which the modules that import this one used -/

section

/-! Shared public-key exponentiation retains the three-bit window timing policy. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

private theorem sharedPublicPower_ct {base src ep : BitVec 32} {len w M : Nat}
    {P : State → Prop} {regions : List Region} {bb eb1 eb2 : List Byte}
    (K : TwoExp.Montgomery base len w P regions) (ct : TwoExp.MontgomeryTiming K)
    (fits : Proof.Rsa.Mont.arrAt w 16 ≤ 8 * len) (positive : 0 < eb1.length)
    (length : eb1.length = eb2.length)
    (separate : ∀ r ∈ regions, Region.Disjoint ⟨State.addr ep, eb1.length⟩ r) :
    RelCT isa (fun s t => KeyPower.Input base src ep len w M P regions bb eb1 s ∧
      KeyPower.Input base src ep len w M P regions bb eb2 t ∧ s.sp = t.sp)
      (.seq VG.Impl.Ffdh.Arm.powerImport (VG.Impl.Bignum.Arm.SharedWindow.phase K.op))
      (fun _ _ => True) := by
  exact relCT_chain
    ((KeyPower.import_ct length).mono
      (fun _ _ h => ⟨h.1.power, h.2.1.power, h.2.2⟩) (fun _ _ h => h))
    (fun s h => WP.mono (KeyPower.import_ok K s h) fun _ k => ⟨k.1.phase, k.1.persistent⟩)
    (fun s h => WP.mono (KeyPower.import_ok K s h) fun _ k => ⟨k.1.phase, k.1.persistent⟩)
    (SharedWindow.phase_ct K ct fits positive length separate)

theorem sharedCheckPublicPowerAt_ct {p : Inputs} {slots : List Nat} {bs es ec M : Nat}
    {bb eb1 eb2 : List Byte} {P : State → Prop} {regions : List Region}
    (K : TwoExp.Montgomery p.base p.len p.w P regions) (ct : TwoExp.MontgomeryTiming K)
    (stable : stableSlots slots = true) (hb : bs ∈ slots) (he : es ∈ slots)
    (hc : ec ∈ slots) (hk : 32 ∈ slots)
    (baseLength : bb.length = p.k) (positive : 0 < eb1.length) (fit : eb1.length < 2 ^ 32)
    (count : p.slotValue ec = BitVec.ofNat 32 eb1.length) (length : eb1.length = eb2.length)
    (odd : M % 2 = 1)
    (separate : ∀ r ∈ regions, Region.Disjoint ⟨State.addr (p.slotValue es), eb1.length⟩ r) :
    RelCT isa (fun s t => (PowerAtInput p slots bs es M bb eb1 s ∧ P s) ∧
      (PowerAtInput p slots bs es M bb eb2 t ∧ P t) ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.SharedCheckPublic.powerAt K.op bs es ec) (fun _ _ => True) := by
  have args (s : State) {eb : List Byte} (h : PowerAtInput p slots bs es M bb eb s ∧ P s)
      (positive : 0 < eb.length) (fit : eb.length < 2 ^ 32)
      (count : p.slotValue ec = BitVec.ofNat 32 eb.length)
      (sep : ∀ r ∈ regions, Region.Disjoint ⟨State.addr (p.slotValue es), eb.length⟩ r) :
      WP isa (.block (VG.Impl.Ffdh.Arm.Domain.powerArgs bs es ec)) s
        (KeyPower.Input p.base (p.slotValue bs) (p.slotValue es) p.len p.w M P regions bb eb) := by
    obtain ⟨tr,u,run,input⟩ := powerArgs_input s stable hb he hc hk baseLength positive fit count odd h.1
    have retained := powerArgs_ok s bs es ec h.1.context stable hb he hc hk
    obtain ⟨_,v,run',values,rest⟩ := retained
    obtain ⟨_,rfl⟩ := Exec.det run run'
    have frame : Frame [⟨State.addr p.base,8*p.len⟩] s.mem u.mem := by
      rw [values.2.2.2.2]
      exact Frame.refl _ _
    exact ⟨tr,u,run, input, K.stable frame (rest.mono (by simp [roundClobbers])) h.2, sep⟩
  unfold VG.Impl.Ffdh.Arm.SharedCheckPublic.powerAt
  exact relCT_chain ((powerArgs_ct bs es ec).mono (fun _ _ h => h.2.2) (fun _ _ _ => trivial))
    (fun s h => args s h positive fit count separate)
    (fun s h => args s h (by rw [←length]; exact positive) (by rw [←length]; exact fit)
      (by rw [←length]; exact count) (by rw [←length]; exact separate))
    (sharedPublicPower_ct K ct p.width.2.2.1 positive length separate)

end VG.Proof.Ffdh.Arm

end

end

/-! ### `Ffdh.Arm.DomainNormalizedPrepareAt`, which this module and modules that import it used -/

section

/-! # Normalized callable modulus preparation within the FFDH argument frame -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)
open VG.Proof.Rsa.Mont (numAt)

theorem domainNormalizedPrepareAt24_ok (backend : MontBackend) (s : State) {p : Inputs} {slots : List Nat}
    (h : Context p slots s) (calls : DomainCallMemory p s)
    (stable : stableSlots slots = true) (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h32 : 32 ∈ slots)
    (large : 1 < p.P) (odd : p.P % 2 = 1)
    (normalized : 2 ^ (64 * (p.w - 1)) ≤ p.P) :
    WP isa (VG.Impl.Ffdh.Arm.NormalizedPrepare.prepareAt
      (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul) backend.dbl 24) s fun t =>
      Context p slots t ∧ ArithmeticReady p.base p.len p.w t ∧
      numAt t.mem (State.addr p.base) p.w 0 = p.P ∧
      numAt t.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % p.P ∧
      Frame (domainPrepareWrites p s) s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [VG.Impl.Ffdh.Arm.NormalizedPrepare.prepareAt, WP.seq_iff]
  refine WP.mono (prepareArgs_ok s 24 h stable h24 h32 h0) ?_
  rintro u ⟨contextU, stack, _, countU, _, frameU, restU⟩
  have sourceU := contextU.pBytes
  have bytes : Spec.Rsa.bytesAt u.mem (State.addr p.domain) p.k = p.dom.take p.k := by
    simpa only [p.pLength] using sourceU.bytes
  have input : PrepareInput p.base p.domain p.len p.k u :=
    ⟨contextU.workspace, by rw [stack.savedOutput]; exact stack, contextU.ptr, countU,
      p.minLength, p.maxLength, p.publicSpace,
      by rw [← p.pLength]; exact sourceU.fits,
      by rw [← p.pLength]; exact sourceU.readable,
      by rw [← p.pLength]; exact sourceU.separate,
      by rw [bytes]; exact large, by rw [bytes]; exact odd⟩
  let K := TwoExp.sharedMontgomery p.base s.sp p.len p.w backend.name backend.mul
    (fun _ _ _ ho ha hb v input => backend.correct v input ho ha hb) backend.stackOk
  have hp : TwoExp.CallReady p.base s.sp p.len u := ⟨(calls.after restU).stack, restU.sp⟩
  refine WP.mono (normalizedPrepare_ok u K (backend.doubling p.base s.sp p.len p.w) input hp (by rw [bytes]; exact normalized)) ?_
  rintro t ⟨ready, modulus, r2, _, frameT, restT⟩
  rw [bytes] at modulus r2
  have localFrame : Frame [⟨State.addr p.base, 8 * p.len⟩, FrameStack.belowA u.sp 48]
      u.mem t.mem := by simpa only [K, restU.sp] using frameT
  have contextT := contextU.after_arithmetic (calls.after restU) localFrame restT ready.ptr
    (fun d hd => (stableSlots_at stable hd).1)
  have frame : Frame (domainPrepareWrites p s) s.mem t.mem :=
    (frameU.mono (by intro r hr; simp only [domainPrepareWrites, prepareAtWrites, List.mem_append,
      List.mem_cons]; exact Or.inl (Or.inr hr))).trans
      (frameT.mono (by
        intro r hr
        simp only [List.mem_cons] at hr
        simp only [domainPrepareWrites, prepareAtWrites, List.mem_append, List.mem_cons]
        rcases hr with hr | hr
        · exact Or.inl (Or.inl hr)
        · exact Or.inr hr))
  exact ⟨contextT, ready, modulus, r2, frame,
    (restU.mono (by simp [roundClobbers])).trans restT⟩

end VG.Proof.Ffdh.Arm

end

end

/-! # The shared native key-preparation boundary hides modulus values -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem domainNormalizedPrepareAt24_ct (backend : MontBackend) {p : Inputs} {slots : List Nat}
    (stable : stableSlots slots = true) (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h32 : 32 ∈ slots)
    (large : 1 < p.P) (odd : p.P % 2 = 1) (normalized : 2 ^ (64 * (p.w - 1)) ≤ p.P) :
    RelCT isa (fun s t => (Context p slots s ∧ DomainCallMemory p s) ∧
      (Context p slots t ∧ DomainCallMemory p t) ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.NormalizedPrepare.prepareAt
        (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul) backend.dbl 24) (fun _ _ => True) := by
  have family (sp0 : BitVec 32) :
      RelCT isa (fun s t => (Context p slots s ∧ DomainCallMemory p s ∧ s.sp = sp0) ∧
        (Context p slots t ∧ DomainCallMemory p t ∧ t.sp = sp0) ∧ s.sp = t.sp)
        (VG.Impl.Ffdh.Arm.NormalizedPrepare.prepareAt
          (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul) backend.dbl 24) (fun _ _ => True) := by
    let correct := fun o a b ho ha hb v input => backend.correct v (base := p.base) (len := p.len) (w := p.w) (o := o) (a := a) (b := b) input ho ha hb
    let K := TwoExp.sharedMontgomery p.base sp0 p.len p.w backend.name backend.mul correct backend.stackOk
    have timing : TwoExp.MontgomeryTiming K :=
      TwoExp.sharedMontgomeryTiming p.base sp0 p.len p.w backend.name backend.mul correct backend.stackOk
        (fun _ _ _ ho ha hb => backend.rawCT ho ha hb)
    let D := backend.doubling p.base sp0 p.len p.w
    have dtiming : TwoExp.DoublingTiming D := backend.doublingTiming p.base sp0 p.len p.w
    have argsInput (s : State) (h : Context p slots s ∧ DomainCallMemory p s ∧ s.sp = sp0) :
        WP isa (.block (VG.Impl.Ffdh.Arm.Domain.prepareArgs 24)) s fun u =>
          PrepareInput p.base p.domain p.len p.k u ∧ TwoExp.CallReady p.base sp0 p.len u ∧ 2 ^ (64 * (p.w - 1)) ≤ Spec.Rsa.os2ip (Spec.Rsa.bytesAt u.mem (State.addr p.domain) p.k) := by
      refine WP.mono (prepareArgs_ok s 24 h.1 stable h24 h32 h0) ?_
      rintro u ⟨contextU, stack, _, countU, _, _, restU⟩
      have sourceU := contextU.pBytes
      have bytes : Spec.Rsa.bytesAt u.mem (State.addr p.domain) p.k = p.dom.take p.k := by
        simpa only [p.pLength] using sourceU.bytes
      refine ⟨?_, ⟨(h.2.1.after restU).stack, restU.sp.trans h.2.2⟩, by rw [bytes]; exact normalized⟩
      exact ⟨contextU.workspace, by rw [stack.savedOutput]; exact stack, contextU.ptr, countU,
        p.minLength, p.maxLength, p.publicSpace,
        by rw [← p.pLength]; exact sourceU.fits,
        by rw [← p.pLength]; exact sourceU.readable,
        by rw [← p.pLength]; exact sourceU.separate,
        by rw [bytes]; exact large, by rw [bytes]; exact odd⟩
    unfold VG.Impl.Ffdh.Arm.NormalizedPrepare.prepareAt
    exact relCT_chain ((prepareArgs_ct 24).mono (fun _ _ h => h.2.2) (fun _ _ h => h))
      argsInput argsInput (normalizedPrepare_ct K timing D dtiming p.width.2.2.2.2)
  intro s t tr1 tr2 u v h e1 e2
  exact family s.sp s t tr1 tr2 u v
    ⟨⟨h.1.1, h.1.2, rfl⟩, ⟨h.2.1.1, h.2.1.2, h.2.2.symm⟩, h.2.2⟩ e1 e2


end VG.Proof.Ffdh.Arm
