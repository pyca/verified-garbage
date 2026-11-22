module

public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Arm.StackScratchConsts
public import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
public import VerifiedGarbage.Impl.Bignum.Arm.MontCall
public import VerifiedGarbage.Impl.Ffdh.Arm.SharedCheckDomain
public import VerifiedGarbage.Proof.Ffdh.Arm.Backend
public import VerifiedGarbage.Proof.Ffdh.Arm.DomainCallMemory
public import VerifiedGarbage.Proof.Ffdh.Arm.DomainSharedPrepareAt
public import VerifiedGarbage.Proof.Ffdh.Arm.SharedCheckPublicInstances
public import VerifiedGarbage.Proof.Ffdh.Arm.DomainSpec
public import VerifiedGarbage.Proof.Ffdh.Arm.CheckPublicPre
public import VerifiedGarbage.Proof.Ffdh.Arm.Context
public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack
public import VerifiedGarbage.Proof.Ffdh.Arm.ImportAtCT
public import VerifiedGarbage.Proof.Ffdh.Arm.VettedGroupsState
public import VerifiedGarbage.Proof.Ffdh.Arm.VettedGroupsEnvironment
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpMontgomery
public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpMontgomeryCT
public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpShared
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Bignum.Arm.TwoExpSharedCT
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.SmallConstCT
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Ffdh.Arm.Prepare
import VerifiedGarbage.Proof.Ffdh.Arm.PrepareAt
import VerifiedGarbage.Proof.Ffdh.Arm.Head
import VerifiedGarbage.Proof.Ffdh.Arm.HeadCT
import VerifiedGarbage.Proof.Ffdh.Arm.Branch
import VerifiedGarbage.Proof.Ffdh.Arm.BranchCT
import VerifiedGarbage.Proof.Ffdh.Arm.FlagCT
import VerifiedGarbage.Proof.Ffdh.Arm.QTest
import VerifiedGarbage.Proof.Ffdh.Arm.ImportAt
import VerifiedGarbage.Proof.Ffdh.Arm.Range
import VerifiedGarbage.Proof.Ffdh.Arm.RangeCT
import VerifiedGarbage.Proof.Ffdh.Arm.CheckFlag
import VerifiedGarbage.Proof.Ffdh.Arm.EqualCT
import VerifiedGarbage.Proof.Ffdh.Arm.ValueChecks
import VerifiedGarbage.Proof.Ffdh.Arm.ValueChecksCT
import VerifiedGarbage.Proof.Ffdh.Arm.StackCT
import VerifiedGarbage.Proof.Ffdh.Arm.FrameCT
import VerifiedGarbage.Proof.Ffdh.Arm.Frame
import VerifiedGarbage.Proof.Ffdh.Arm.EntryStore
import VerifiedGarbage.Proof.Ffdh.Arm.VettedGroupsCT
import VerifiedGarbage.Proof.Ffdh.Arm.VettedGroupsConsts
import VerifiedGarbage.Proof.Ffdh.Arm.VettedGroupsBytes
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.Syms
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Lit
import Batteries.Logic
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Bignum.Arm.PcDimensions
import VerifiedGarbage.Proof.Ffdh.VettedValidation.Facts

/-! # `vg_ffdh_check_domain` on ARMv7, generic over the RSA Montgomery product

The imported-domain check (`Impl.Ffdh.Arm.SharedCheckDomain`) whose products
call a shared Montgomery product (`MontBackend`), proven against
`Spec.Ffdh.checkDomainContract` with the vetted groups' table and with the
48 bytes below its frame that the product's calls use reserved (176 bytes in
all): correct, constant time and satisfiable. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.SharedCheckDomain
open VG VG.Arm VG.Arm.FrameStack VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt Operand arrAt Keeps)
open VG.Proof.X25519.Arm (Rest)

/-- The shared product's call, as the code calls it. -/
abbrev mop (b : MontBackend) : Nat → Nat → Nat → Prog isa :=
  VG.Impl.Bignum.Arm.MontCall.op b.name b.mul

/-! ## Reduction by any Montgomery product -/

theorem reduce_ok {base : BitVec 32} {len w : Nat} {P : State → Prop} {regions : List Region}
    (K : TwoExp.Montgomery base len w P regions) (s : State) {o M : Nat}
    (h : ArithmeticReady base len w s) (hp : P s) (ho : Operand o) (ho0 : o ≠ 0) (ho7 : o ≠ 7)
    (modulus : numAt s.mem (State.addr base) w 0 = M) (odd : M % 2 = 1) (large : 1 < M)
    (r2 : numAt s.mem (State.addr base) w 4 = 2 ^ (128 * w) % M)
    (one : numAt s.mem (State.addr base) w 7 = 1) :
    WP isa (VG.Impl.Ffdh.Arm.SharedCheckDomain.reduce K.op o) s fun t =>
      ArithmeticReady base len w t ∧ P t ∧
      numAt t.mem (State.addr base) w 0 = M ∧
      numAt t.mem (State.addr base) w o = numAt s.mem (State.addr base) w o % M ∧
      Keeps (State.addr base) len w o s.mem t.mem ∧
      Frame regions s.mem t.mem ∧ Rest roundClobbers s t := by
  have op4 : Operand 4 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op7 : Operand 7 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have fits : arrAt w 8 ≤ 8 * len := h.width ▸ h.layout.2.2.1
  rw [VG.Impl.Ffdh.Arm.SharedCheckDomain.reduce, WP.seq_iff]
  refine WP.mono (K.op_ok s o o 4 h hp ho ho op4 ho0
    (by rw [modulus, r2]; exact Nat.mod_lt _ (by omega_using [large]))) ?_
  rintro u ⟨readyU, modU, boundU, valueU, keepsU, pu, frameU, restU⟩
  rw [modulus] at modU boundU valueU
  obtain encoded : numAt u.mem (State.addr base) w o =
      numAt s.mem (State.addr base) w o * 2 ^ (64 * w) % M := by
    have e : numAt u.mem (State.addr base) w o % M =
        numAt s.mem (State.addr base) w o * 2 ^ (64 * w) % M := by
      apply VG.Proof.Bignum.mont_cancel (VG.Proof.Bignum.coprime_pow2 odd (64 * w))
      rw [valueU, r2, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod,
        show 128 * w = 64 * w + 64 * w by omega_using [], Nat.pow_add, Nat.mul_assoc]
    rwa [Nat.mod_eq_of_lt boundU] at e
  have oneU := (keeps_array_num keepsU fits op7 (Ne.symm ho7)).trans one
  refine WP.mono (K.op_ok u o o 7 readyU pu ho ho op7 ho0 (by rw [oneU, modU]; exact large)) ?_
  rintro t ⟨ready, modT, bound, value, keepsT, pt, frameT, restT⟩
  rw [modU] at modT bound value
  rw [oneU, Nat.mul_one, encoded, Nat.mod_mod] at value
  have reduced := VG.Proof.Bignum.mont_cancel (VG.Proof.Bignum.coprime_pow2 odd (64 * w)) value
  rw [Nat.mod_eq_of_lt bound] at reduced
  exact ⟨ready, pt, modT, reduced, fun i hi sep => (keepsT i hi sep).trans (keepsU i hi sep),
    frameU.trans frameT, restU.trans restT⟩

structure ReduceReady (base : BitVec 32) (len w : Nat) (P : State → Prop) (s : State) : Prop where
  ready : ArithmeticReady base len w s
  persistent : P s
  r2bound : numAt s.mem (State.addr base) w 4 < numAt s.mem (State.addr base) w 0
  onebound : numAt s.mem (State.addr base) w 7 < numAt s.mem (State.addr base) w 0

theorem reduce_ct {base : BitVec 32} {len w : Nat} {P : State → Prop} {regions : List Region}
    (K : TwoExp.Montgomery base len w P regions) (ct : TwoExp.MontgomeryTiming K)
    {o : Nat} (ho : Operand o) (ho0 : o ≠ 0) (ho7 : o ≠ 7) :
    RelCT isa (fun s t => ReduceReady base len w P s ∧ ReduceReady base len w P t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.SharedCheckDomain.reduce K.op o) (fun _ _ => True) := by
  have op4 : Operand 4 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op7 : Operand 7 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have encode := (ct.op_ct o o 4 ho ho op4).mono
    (P' := fun (s t : State) => ReduceReady base len w P s ∧ ReduceReady base len w P t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨⟨h.1.ready, h.1.persistent, h.1.r2bound⟩,
      ⟨h.2.1.ready, h.2.1.persistent, h.2.1.r2bound⟩, h.2.2⟩) (fun _ _ h => h)
  have wp (s : State) (h : ReduceReady base len w P s) :
      WP isa (K.op o o 4) s (TwoExp.OpInput base len w P 7) := by
    refine WP.mono (K.op_ok s o o 4 h.ready h.persistent ho ho op4 ho0 h.r2bound) ?_
    rintro t ⟨ready, modulus, _, _, keeps, pt, _, _⟩
    have fits : arrAt w 8 ≤ 8 * len := h.ready.width ▸ h.ready.layout.2.2.1
    exact ⟨ready, pt, by rw [keeps_array_num keeps fits op7 (Ne.symm ho7), modulus]; exact h.onebound⟩
  unfold VG.Impl.Ffdh.Arm.SharedCheckDomain.reduce
  exact relCT_chain encode wp wp (ct.op_ct o o 7 ho ho op7)

theorem _root_.VG.Proof.Ffdh.Arm.DomainCallMemory.congr_sp {p : Inputs} {s t : State}
    (h : DomainCallMemory p s) (sp : s.sp = t.sp) : DomainCallMemory p t :=
  ⟨⟨by rw [← sp]; exact h.stack.fit, by rw [← sp]; exact h.stack.separate⟩,
    by rw [← sp]; exact h.domain, by rw [← sp]; exact h.publicValue⟩

/-! ## Frames -/

theorem callWrites_sub {p : Inputs} {s : State} :
    ∀ r ∈ [⟨State.addr p.base, 8 * p.len⟩, belowA s.sp 48], r ∈ domainPrepareWrites p s := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [domainPrepareWrites, prepareAtWrites, prepareWrites, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false]
  rcases hr with rfl | rfl
  · exact Or.inl (Or.inl rfl)
  · exact Or.inr rfl

theorem workspace_sub {p : Inputs} {s : State} :
    ∀ r ∈ [(⟨State.addr p.base, 8 * p.len⟩ : Region)], r ∈ domainPrepareWrites p s := by
  intro r hr
  rw [List.mem_singleton] at hr
  subst r
  simp [domainPrepareWrites, prepareAtWrites]

/-! ## The modulus q's preparation -/

theorem prepareQ_ok (backend : MontBackend) (s : State) {p : Inputs} {slots : List Nat}
    (h : Context p slots s) (calls : DomainCallMemory p s)
    (stable : stableSlots slots = true) (h0 : 0 ∈ slots) (h32 : 32 ∈ slots) (h60 : 60 ∈ slots)
    (hasQ : p.hasQ = true) (large : 1 < p.Q) (odd : p.Q % 2 = 1) :
    WP isa (VG.Impl.Ffdh.Arm.SharedPrepare.prepareAt (mop backend) 60) s fun t =>
      Context p slots t ∧ ArithmeticReady p.base p.len p.w t ∧
      numAt t.mem (State.addr p.base) p.w 0 = p.Q ∧
      numAt t.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % p.Q ∧
      Frame (domainPrepareWrites p s) s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [VG.Impl.Ffdh.Arm.SharedPrepare.prepareAt, WP.seq_iff]
  refine WP.mono (prepareArgs_ok s 60 h stable h60 h32 h0) ?_
  rintro u ⟨contextU, stack, _, countU, _, frameU, restU⟩
  have sourceU := contextU.qBytes hasQ
  have bytes : Spec.Rsa.bytesAt u.mem (State.addr p.q) p.k = (p.dom.drop (2 * p.k)).take p.k := by
    simpa only [p.qLength hasQ] using sourceU.bytes
  have input : PrepareInput p.base p.q p.len p.k u :=
    ⟨contextU.workspace, by rw [stack.savedOutput]; exact stack, contextU.ptr, countU,
      p.minLength, p.maxLength, p.publicSpace,
      by rw [← p.qLength hasQ]; exact sourceU.fits,
      by rw [← p.qLength hasQ]; exact sourceU.readable,
      by rw [← p.qLength hasQ]; exact sourceU.separate,
      by rw [bytes]; exact large, by rw [bytes]; exact odd⟩
  let K := TwoExp.sharedMontgomery p.base s.sp p.len p.w backend.name backend.mul
    (fun _ _ _ ho ha hb v input => backend.correct v input ho ha hb) backend.stackOk
  have hp : TwoExp.CallReady p.base s.sp p.len u := ⟨(calls.after restU).stack, restU.sp⟩
  refine WP.mono (sharedPrepare_ok u K input hp) ?_
  rintro t ⟨ready, modulus, r2, _, frameT, restT⟩
  rw [bytes] at modulus r2
  have localFrame : Frame [⟨State.addr p.base, 8 * p.len⟩, FrameStack.belowA u.sp 48]
      u.mem t.mem := by simpa only [K, restU.sp] using frameT
  have contextT := contextU.after_arithmetic (calls.after restU) localFrame restT ready.ptr
    (fun d hd => (stableSlots_at stable hd).1)
  have frame : Frame (domainPrepareWrites p s) s.mem t.mem :=
    (frameU.mono (by intro r hr; simp only [domainPrepareWrites, prepareAtWrites, List.mem_append,
      List.mem_cons]; exact Or.inl (Or.inr hr))).trans (frameT.mono callWrites_sub)
  exact ⟨contextT, ready, modulus, r2, frame, (restU.mono (by simp [roundClobbers])).trans restT⟩

theorem prepareQ_ct (backend : MontBackend) {p : Inputs} {slots : List Nat}
    (stable : stableSlots slots = true) (h0 : 0 ∈ slots) (h32 : 32 ∈ slots) (h60 : 60 ∈ slots)
    (hasQ : p.hasQ = true) (large : 1 < p.Q) (odd : p.Q % 2 = 1) :
    RelCT isa (fun s t => (Context p slots s ∧ DomainCallMemory p s) ∧
      (Context p slots t ∧ DomainCallMemory p t) ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.SharedPrepare.prepareAt (mop backend) 60) (fun _ _ => True) := by
  have family (sp0 : BitVec 32) :
      RelCT isa (fun s t => (Context p slots s ∧ DomainCallMemory p s ∧ s.sp = sp0) ∧
        (Context p slots t ∧ DomainCallMemory p t ∧ t.sp = sp0) ∧ s.sp = t.sp)
        (VG.Impl.Ffdh.Arm.SharedPrepare.prepareAt (mop backend) 60) (fun _ _ => True) := by
    let correct := fun o a b ho ha hb v input => backend.correct v (base := p.base) (len := p.len)
      (w := p.w) (o := o) (a := a) (b := b) input ho ha hb
    let K := TwoExp.sharedMontgomery p.base sp0 p.len p.w backend.name backend.mul correct backend.stackOk
    have timing : TwoExp.MontgomeryTiming K :=
      TwoExp.sharedMontgomeryTiming p.base sp0 p.len p.w backend.name backend.mul correct backend.stackOk
        (fun _ _ _ ho ha hb => backend.rawCT ho ha hb)
    have argsInput (s : State) (h : Context p slots s ∧ DomainCallMemory p s ∧ s.sp = sp0) :
        WP isa (.block (VG.Impl.Ffdh.Arm.Domain.prepareArgs 60)) s fun u =>
          PrepareInput p.base p.q p.len p.k u ∧ TwoExp.CallReady p.base sp0 p.len u := by
      refine WP.mono (prepareArgs_ok s 60 h.1 stable h60 h32 h0) ?_
      rintro u ⟨contextU, stack, _, countU, _, _, restU⟩
      have sourceU := contextU.qBytes hasQ
      have bytes : Spec.Rsa.bytesAt u.mem (State.addr p.q) p.k = (p.dom.drop (2 * p.k)).take p.k := by
        simpa only [p.qLength hasQ] using sourceU.bytes
      refine ⟨?_, (h.2.1.after restU).stack, restU.sp.trans h.2.2⟩
      exact ⟨contextU.workspace, by rw [stack.savedOutput]; exact stack, contextU.ptr, countU,
        p.minLength, p.maxLength, p.publicSpace,
        by rw [← p.qLength hasQ]; exact sourceU.fits,
        by rw [← p.qLength hasQ]; exact sourceU.readable,
        by rw [← p.qLength hasQ]; exact sourceU.separate,
        by rw [bytes]; exact large, by rw [bytes]; exact odd⟩
    unfold VG.Impl.Ffdh.Arm.SharedPrepare.prepareAt
    exact relCT_chain ((prepareArgs_ct 60).mono (fun _ _ h => h.2.2) (fun _ _ h => h))
      argsInput argsInput (sharedPrepare_ct K timing p.width.2.2.2.2)
  intro s t tr1 tr2 u v h e1 e2
  exact family s.sp s t tr1 tr2 u v
    ⟨⟨h.1.1, h.1.2, rfl⟩, ⟨h.2.1.1, h.2.1.2, h.2.2.symm⟩, h.2.2⟩ e1 e2

/-! ## The checks, from the arithmetic's preparation -/

theorem divides_ok (backend : MontBackend) (s : State) {p : Inputs} {slots : List Nat}
    (h : Context p slots s) (calls : DomainCallMemory p s) (stable : stableSlots slots = true)
    (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h32 : 32 ∈ slots) (h60 : 60 ∈ slots)
    (hasQ : p.hasQ = true) (large : 1 < p.Q) (odd : p.Q % 2 = 1) :
    WP isa (VG.Impl.Ffdh.Arm.SharedCheckDomain.divides (mop backend)) s fun t => Context p slots t ∧
      t.gpr .r11 = (if p.P % p.Q = 1 then 1 else 0) ∧
      Frame (domainPrepareWrites p s) s.mem t.mem ∧ Rest roundClobbers s t := by
  have op0 : Operand 0 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op1 : Operand 1 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op4 : Operand 4 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have fitSlots : ∀ d ∈ slots, d + 4 ≤ 72 := fun d hd => (stableSlots_at stable hd).1
  rw [VG.Impl.Ffdh.Arm.SharedCheckDomain.divides, WP.seq_iff]
  refine WP.mono (prepareQ_ok backend s h calls stable h0 h32 h60 hasQ large odd) ?_
  rintro u ⟨contextU, readyU, modU, r2U, frameU, restU⟩
  rw [WP.seq_iff]
  refine WP.mono (importAt_ok u 1 24 32 contextU stable h24 h32 readyU (by decide) (by decide) contextU.pBytes
    (by rw [p.pLength]; have := p.minLength; omega_using [this]) (by rw [p.pLength]; exact p.width.2.2.2.1)
    (by change BitVec.ofNat 32 p.k = _; rw [p.pLength])) ?_
  rintro v ⟨contextV, readyV, valueV, keepsV, frameV, restV⟩
  have fits : arrAt p.w 8 ≤ 8 * p.len := readyV.width ▸ readyV.layout.2.2.1
  have modV := (keeps_array_num keepsV fits op0 (by decide)).trans modU
  have r2V := (keeps_array_num keepsV fits op4 (by decide)).trans r2U
  rw [WP.seq_iff]
  refine WP.mono (smallConst_ok v 1 readyV (by decide : 7 < 8) (by decide) (by decide) (by decide)) ?_
  rintro w ⟨readyW, one, _, keepsW, frameW, restW⟩
  have modW := (keeps_array_num keepsW fits op0 (by decide)).trans modV
  have r2W := (keeps_array_num keepsW fits op4 (by decide)).trans r2V
  have contextW := contextV.after_workspace frameW restW readyW.ptr fitSlots
  have callsW := ((calls.after restU).after restV).after restW
  have spW : w.sp = s.sp := restW.sp.trans (restV.sp.trans restU.sp)
  let K := TwoExp.sharedMontgomery p.base s.sp p.len p.w backend.name backend.mul
    (fun _ _ _ ho ha hb z hi => backend.correct z hi ho ha hb) backend.stackOk
  have hp : TwoExp.CallReady p.base s.sp p.len w := ⟨callsW.stack, spW⟩
  rw [WP.seq_iff]
  refine WP.mono (reduce_ok K w readyW hp op1 (by decide) (by decide) modW odd large r2W one) ?_
  rintro x ⟨readyX, _, _, reduced, _, frameX, restX⟩
  rw [keeps_array_num keepsW fits op1 (by decide), valueV] at reduced
  have frameX' : Frame [⟨State.addr p.base, 8 * p.len⟩, FrameStack.belowA w.sp 48] w.mem x.mem := by
    rw [spW]; exact frameX
  have contextX := contextW.after_arithmetic callsW frameX' restX readyX.ptr fitSlots
  refine WP.mono (isOne_ok x readyX op1 (by decide)) ?_
  rintro t ⟨readyT, flag, _, frameT, restT⟩
  rw [reduced] at flag
  have frame : Frame (domainPrepareWrites p s) s.mem t.mem :=
    (((frameU.trans ((frameV.trans frameW).mono workspace_sub)).trans
      (frameX.mono callWrites_sub)).trans (frameT.mono workspace_sub))
  exact ⟨contextX.after_workspace frameT restT readyT.ptr fitSlots, flag, frame,
    (((restU.trans restV).trans restW).trans restX).trans restT⟩

/-- g's subgroup membership, from p's preparation. -/
theorem generator_ok (backend : MontBackend) (s : State) {p : Inputs} {slots : List Nat}
    (h : Context p slots s) (calls : DomainCallMemory p s) (stable : stableSlots slots = true)
    (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h32 : 32 ∈ slots) (h56 : 56 ∈ slots) (h60 : 60 ∈ slots)
    (hasQ : p.hasQ = true) (large : 1 < p.P) (odd : p.P % 2 = 1) :
    WP isa (VG.Impl.Ffdh.Arm.SharedCheckDomain.generator (mop backend)) s fun t =>
      t.gpr .r0 = (if Spec.Rsa.powMod p.G p.Q p.P = 1 then 1 else 0) ∧
      Frame (domainPrepareWrites p s) s.mem t.mem := by
  rw [VG.Impl.Ffdh.Arm.SharedCheckDomain.generator, WP.seq_iff]
  refine WP.mono (domainSharedPrepareAt24_ok backend s h calls stable h0 h24 h32 large odd) ?_
  rintro y ⟨contextY, readyY, modY, r2Y, frameY, restY⟩
  rw [WP.seq_iff]
  refine WP.mono (sharedCheckPublicSubgroup_ok backend y 56 contextY (calls.after restY) stable h56 h60 h32
    hasQ readyY modY odd r2Y contextY.gBytes p.gLength) ?_
  rintro z ⟨_, _, flagZ, _, _, frameZ, restZ⟩
  refine WP.mono (finishFlag_ok z) ?_
  rintro t ⟨⟨result, memT⟩, _⟩
  refine ⟨by rw [result, flagZ]; rfl, ?_⟩
  rw [memT]
  rw [restY.sp] at frameZ
  exact frameY.trans (frameZ.mono callWrites_sub)

theorem qChecks_ok (backend : MontBackend) (s : State) {p : Inputs} {slots : List Nat}
    (h : Context p slots s) (calls : DomainCallMemory p s) (stable : stableSlots slots = true)
    (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h32 : 32 ∈ slots) (h56 : 56 ∈ slots) (h60 : 60 ∈ slots)
    (hasQ : p.hasQ = true) (ready : ArithmeticReady p.base p.len p.w s)
    (modulus : numAt s.mem (State.addr p.base) p.w 0 = p.P) (large : 1 < p.P) (odd : p.P % 2 = 1)
    (r2 : numAt s.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % p.P) :
    WP isa (VG.Impl.Ffdh.Arm.SharedCheckDomain.qChecks (mop backend)) s fun t =>
      t.gpr .r0 = domainQFlag p ∧ Frame (domainPrepareWrites p s) s.mem t.mem := by
  rw [VG.Impl.Ffdh.Arm.SharedCheckDomain.qChecks, WP.seq_iff]
  refine WP.mono (qRange_ok s h stable h60 h32 hasQ ready modulus odd r2) ?_
  rintro u ⟨contextU, _, flagU, _, _, frameU, restU⟩
  rw [VG.Impl.Ffdh.Arm.Domain.ifFlag, WP.seq_iff]
  refine WP.mono (testFlag_ok u) ?_
  rintro v ⟨⟨zeroV, memV⟩, restV⟩
  have spV : v.sp = s.sp := restV.sp.trans restU.sp
  have frameUV : Frame (domainPrepareWrites p s) s.mem v.mem := by
    rw [memV]; exact frameU.mono workspace_sub
  by_cases qValid : 2 < p.Q ∧ p.Q < p.P - 1 ∧ p.Q % 2 = 1
  · refine WP.ite true (by change some (!v.z) = some true; rw [zeroV, flagU, qRangeFlag, ite_eq_left qValid]; rfl) ?_ (by intro hf; cases hf)
    intro _
    have contextV := contextU.of_mem memV restV ((restV.gpr .r0 (by simp)).trans contextU.ptr)
    have callsV := (calls.after restU).after restV
    rw [WP.seq_iff]
    refine WP.mono (divides_ok backend v contextV callsV stable h0 h24 h32 h60 hasQ
      (by omega_using [qValid]) qValid.2.2) ?_
    rintro w ⟨contextW, dividesW, frameW, restW⟩
    have frameW' : Frame (domainPrepareWrites p s) v.mem w.mem := by
      simpa only [domainPrepareWrites, prepareAtWrites, prepareWrites, spV] using frameW
    rw [VG.Impl.Ffdh.Arm.Domain.ifFlag, WP.seq_iff]
    refine WP.mono (testFlag_ok w) ?_
    rintro x ⟨⟨zeroX, memX⟩, restX⟩
    by_cases divides : p.P % p.Q = 1
    · refine WP.ite true (by change some (!x.z) = some true; rw [zeroX, dividesW, ite_eq_left divides]; rfl) ?_ (by intro hf; cases hf)
      intro _
      have contextX := contextW.of_mem memX restX ((restX.gpr .r0 (by simp)).trans contextW.ptr)
      refine WP.mono (generator_ok backend x contextX ((callsV.after restW).after restX) stable
        h0 h24 h32 h56 h60 hasQ large odd) ?_
      rintro t ⟨result, frameT⟩
      refine ⟨by rw [result, domainQFlag, ite_eq_left qValid, ite_eq_left divides], ?_⟩
      have frameT' : Frame (domainPrepareWrites p s) w.mem t.mem := by
        rw [memX] at frameT
        simpa only [domainPrepareWrites, prepareAtWrites, prepareWrites, restX.sp, restW.sp, spV] using frameT
      exact (frameUV.trans frameW').trans frameT'
    · refine WP.ite false (by change some (!x.z) = some false; rw [zeroX, dividesW, ite_eq_right divides]; rfl) (by intro ht; cases ht) ?_
      intro _
      refine WP.mono (ret_ok x 0 (by decide)) ?_
      rintro t ⟨⟨result, memT⟩, _⟩
      refine ⟨by rw [result, domainQFlag, ite_eq_left qValid, ite_eq_right divides], ?_⟩
      rw [memT, memX]
      exact frameUV.trans frameW'
  · refine WP.ite false (by change some (!v.z) = some false; rw [zeroV, flagU, qRangeFlag, ite_eq_right qValid]; rfl) (by intro ht; cases ht) ?_
    intro _
    refine WP.mono (ret_ok v 0 (by decide)) ?_
    rintro t ⟨⟨result, memT⟩, _⟩
    exact ⟨by rw [result, domainQFlag, ite_eq_right qValid], by rw [memT]; exact frameUV⟩

theorem tail_ok (backend : MontBackend) (s : State) {p : Inputs} {slots : List Nat}
    (h : Context p slots s) (calls : DomainCallMemory p s) (stable : stableSlots slots = true)
    (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h28 : 28 ∈ slots) (h32 : 32 ∈ slots)
    (h56 : 56 ∈ slots) (h60 : 60 ∈ slots)
    (ready : ArithmeticReady p.base p.len p.w s)
    (modulus : numAt s.mem (State.addr p.base) p.w 0 = p.P) (large : 1 < p.P) (odd : p.P % 2 = 1)
    (r2 : numAt s.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % p.P) :
    WP isa (VG.Impl.Ffdh.Arm.Domain.withQ (VG.Impl.Ffdh.Arm.SharedCheckDomain.qChecks (mop backend))
      (VG.Impl.Ffdh.Arm.Domain.ret 1)) s fun t =>
        t.gpr .r0 = domainTailFlag p ∧ Frame (domainPrepareWrites p s) s.mem t.mem := by
  rw [VG.Impl.Ffdh.Arm.Domain.withQ, WP.seq_iff]
  refine WP.mono (qTest_ok s h h28 h32) ?_
  rintro u ⟨⟨zero, memU⟩, restU⟩
  have ptrU := (restU.gpr .r0 (by simp)).trans ready.ptr
  have contextU := h.of_mem memU restU ptrU
  have readyU := ready.of_mem memU restU ptrU
  refine WP.ite p.hasQ (by simp only [eval, zero, Bool.not_not]) ?_ ?_
  · intro hasQ
    refine WP.mono (qChecks_ok backend u contextU (calls.after restU) stable h0 h24 h32 h56 h60 hasQ readyU
      (by rw [memU]; exact modulus) large odd (by rw [memU]; exact r2)) ?_
    rintro t ⟨result, frame⟩
    refine ⟨by rw [domainTailFlag, ite_eq_left hasQ]; exact result, ?_⟩
    rw [memU] at frame
    simpa only [domainPrepareWrites, prepareAtWrites, prepareWrites, restU.sp] using frame
  · intro hasQ
    refine WP.mono (ret_ok u 1 (by decide)) ?_
    rintro t ⟨⟨result, memT⟩, _⟩
    refine ⟨by rw [domainTailFlag, ite_eq_right (by rw [hasQ]; decide)]; exact result, ?_⟩
    rw [memT, memU]; exact Frame.refl _ _

theorem main_ok (backend : MontBackend) (s : State) {p : Inputs} {slots : List Nat} {yb : List Byte}
    (h : Context p slots s) (calls : DomainCallMemory p s) (stable : stableSlots slots = true)
    (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h28 : 28 ∈ slots) (h32 : 32 ∈ slots)
    (h56 : 56 ∈ slots) (h60 : 60 ∈ slots)
    (large : 1 < p.P) (odd : p.P % 2 = 1)
    (value : Octets p.base p.g p.len yb s) (length : yb.length = p.k)
    (valueStack : Region.Disjoint ⟨State.addr p.g, yb.length⟩ ⟨State.addr s.sp, 72⟩)
    (valueBelow : Region.Disjoint ⟨State.addr p.g, yb.length⟩ (belowA s.sp 48)) :
    WP isa (VG.Impl.Ffdh.Arm.SharedCheckDomain.main (mop backend)) s fun t =>
      t.gpr .r0 = domainMainFlag p (Spec.Rsa.os2ip yb) ∧ Frame (domainPrepareWrites p s) s.mem t.mem := by
  have op0 : Operand 0 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op4 : Operand 4 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op1 : Operand 1 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  rw [VG.Impl.Ffdh.Arm.SharedCheckDomain.main, WP.seq_iff]
  refine WP.mono (domainSharedPrepareAt24_ok backend s h calls stable h0 h24 h32 large odd) ?_
  rintro u ⟨contextU, readyU, modU, r2U, frameU, restU⟩
  have valueU := value.after_frame frameU restU (by
    intro r hr
    simp only [domainPrepareWrites, prepareAtWrites, prepareWrites, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl | rfl) | rfl
    · exact value.separate
    · exact valueStack.sub_right (Offset.sub_base _ (by decide))
    · exact valueStack.sub_right (Offset.sub_base _ (by decide))
    · exact valueBelow)
  rw [WP.seq_iff]
  refine WP.mono (importAt_ok u 1 56 32 contextU stable h56 h32 readyU (by decide) (by decide)
    valueU (by rw [length]; have := p.minLength; omega_using [this]) (by rw [length]; exact p.width.2.2.2.1)
    (by change BitVec.ofNat 32 p.k = _; rw [length])) ?_
  rintro v ⟨contextV, readyV, y, keepsV, frameV, restV⟩
  have bound : arrAt p.w 8 ≤ 8 * p.len := readyV.width ▸ readyV.layout.2.2.1
  have modV := (keeps_array_num keepsV bound op0 (by decide : 0 ≠ 1)).trans modU
  have r2V := (keeps_array_num keepsV bound op4 (by decide : 4 ≠ 1)).trans r2U
  rw [WP.seq_iff]
  refine WP.mono (inRange_ok v readyV op1 (by decide) (by rw [modV]; exact odd)) ?_
  rintro w ⟨readyW, flag, arraysW, frameW, restW⟩
  rw [y, modV] at flag
  change w.gpr .r11 = (if 1 < Spec.Rsa.os2ip yb ∧ Spec.Rsa.os2ip yb < p.P - 1 then 1 else 0) at flag
  have contextW := contextV.after_workspace frameW restW readyW.ptr (fun d hd => (stableSlots_at stable hd).1)
  have modW := (arraysW 0 op0 (by decide)).trans modV
  have r2W := (arraysW 4 op4 (by decide)).trans r2V
  have frameW' := (frameU.trans (frameV.mono workspace_sub)).trans (frameW.mono workspace_sub)
  rw [VG.Impl.Ffdh.Arm.Domain.ifFlag, WP.seq_iff]
  refine WP.mono (testFlag_ok w) ?_
  rintro z ⟨⟨zero, memZ⟩, restZ⟩
  by_cases valid : 1 < Spec.Rsa.os2ip yb ∧ Spec.Rsa.os2ip yb < p.P - 1
  · refine WP.ite true (by change some (!z.z) = some true; rw [zero, flag, ite_eq_left valid]; rfl) ?_ (by intro hf; cases hf)
    intro _
    have frameZ : Frame [⟨State.addr p.base, 8 * p.len⟩] w.mem z.mem := by rw [memZ]; exact Frame.refl _ _
    have ptrZ := (restZ.gpr .r0 (by simp)).trans readyW.ptr
    have contextZ := contextW.after_workspace frameZ restZ ptrZ (fun d hd => (stableSlots_at stable hd).1)
    have readyZ := readyW.of_mem memZ restZ ptrZ
    refine WP.mono (tail_ok backend z contextZ ((((calls.after restU).after restV).after restW).after restZ)
      stable h0 h24 h28 h32 h56 h60 readyZ (by rw [memZ]; exact modW) large odd (by rw [memZ]; exact r2W)) ?_
    rintro t ⟨result, frameT⟩
    refine ⟨?_, ?_⟩
    · rw [domainMainFlag, ite_eq_left valid]; exact result
    · rw [memZ] at frameT
      have frameT' : Frame (domainPrepareWrites p s) w.mem t.mem := by
        simpa only [domainPrepareWrites, prepareAtWrites, prepareWrites, restZ.sp, restW.sp, restV.sp,
          restU.sp] using frameT
      exact frameW'.trans frameT'
  · refine WP.ite false (by change some (!z.z) = some false; rw [zero, flag, ite_eq_right valid]; rfl) (by intro ht; cases ht) ?_
    intro _
    refine WP.mono (ret_ok z 0 (by decide)) ?_
    rintro t ⟨⟨result, memT⟩, _⟩
    refine ⟨?_, ?_⟩
    · rw [domainMainFlag, ite_eq_right valid]; exact result
    · rw [memT, memZ]; exact frameW'

theorem head_ok (backend : MontBackend) (s : State) {p : Inputs} {slots : List Nat}
    (h : Context p slots s) (calls : DomainCallMemory p s) (stable : stableSlots slots = true)
    (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h28 : 28 ∈ slots) (h32 : 32 ∈ slots) :
    WP isa (VG.Impl.Ffdh.Arm.Domain.head (VG.Impl.Ffdh.Arm.SharedCheckDomain.main (mop backend))) s fun t =>
      t.gpr .r0 = checkedDomainFlag p ∧ Frame (sharedPublicBodyWrites p s) s.mem t.mem := by
  unfold VG.Impl.Ffdh.Arm.Domain.head
  apply WP.assoc
  rw [WP.seq_iff]
  refine WP.mono (VG.Proof.Ffdh.Arm.head_ok s h stable h0 h24 h32) ?_
  rintro u ⟨contextU, zero, frameU, restU⟩
  have fU : Frame (sharedPublicBodyWrites p s) s.mem u.mem :=
    frameU.mono (by simp [sharedPublicBodyWrites, bodyWrites])
  by_cases valid : Spec.Rsa.modulusValid p.P p.k = true
  · refine WP.ite true (by change some u.z = some true; rw [zero, valid]) ?_ (by intro hf; cases hf)
    intro _
    have facts := VG.Proof.Bignum.valid_facts valid p.minLength
    have stableU : stableSlots (60 :: 56 :: slots) = true := by
      change (true && (true && stableSlots slots)) = true
      rw [Bool.true_and, Bool.true_and, stable]
    have callsU := calls.after restU
    have gStack : Region.Disjoint ⟨State.addr p.g, ((p.dom.drop p.k).take p.k).length⟩ ⟨State.addr u.sp, 72⟩ := by
      rw [p.gLength]
      exact contextU.toArgumentMemory.domainSliceStack (by have := p.minLength; omega_using [this])
        (by rw [p.domainLength]; split <;> omega_using [])
    have gBelow : Region.Disjoint ⟨State.addr p.g, ((p.dom.drop p.k).take p.k).length⟩ (belowA u.sp 48) := by
      rw [p.gLength]
      exact callsU.domainSlice contextU (by have := p.minLength; omega_using [this])
        (by rw [p.domainLength]; split <;> omega_using [])
    refine WP.mono (main_ok backend u contextU callsU stableU (by simp [h0]) (by simp [h24]) (by simp [h28])
      (by simp [h32]) (by simp) (by simp) facts.2.1 facts.1 contextU.gBytes p.gLength gStack gBelow) ?_
    rintro t ⟨result, frameT⟩
    refine ⟨by rw [checkedDomainFlag, ite_eq_left valid]; exact result, fU.trans (frameT.sub ?_)⟩
    intro r hr
    simp only [domainPrepareWrites, prepareAtWrites, prepareWrites, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl | rfl) | rfl
    · exact ⟨⟨State.addr p.base, 8 * p.len⟩, by simp [sharedPublicBodyWrites, bodyWrites], by intro a ha; exact ha⟩
    · refine ⟨⟨State.addr s.sp, 72⟩, by simp [sharedPublicBodyWrites, bodyWrites], ?_⟩
      rw [restU.sp]
      exact Offset.sub_base _ (by decide)
    · refine ⟨⟨State.addr s.sp, 72⟩, by simp [sharedPublicBodyWrites, bodyWrites], ?_⟩
      rw [restU.sp]
      exact Offset.sub_base _ (by decide)
    · refine ⟨belowA s.sp 48, by simp [sharedPublicBodyWrites], ?_⟩
      rw [restU.sp]
      intro a ha; exact ha
  · have invalid : Spec.Rsa.modulusValid p.P p.k = false := Bool.eq_false_iff.mpr valid
    refine WP.ite false (by change some u.z = some false; rw [zero, invalid]) (by intro ht; cases ht) ?_
    intro _
    refine WP.mono (ret_ok u 0 (by decide)) ?_
    rintro t ⟨⟨result, memT⟩, _⟩
    exact ⟨by rw [checkedDomainFlag, ite_eq_right valid]; exact result, by rw [memT]; exact fU⟩

open VG.Impl.Ffdh.Arm.VettedGroups (tableSym groups recognize) in
theorem body_ok (backend : MontBackend) (s : State) {p : Inputs} {slots : List Nat}
    (h : Context p slots s) (calls : DomainCallMemory p s) (stable : stableSlots slots = true)
    (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h28 : 28 ∈ slots) (h32 : 32 ∈ slots)
    (table : VettedGroups.TableAt (s.syms tableSym) groups s) :
    WP isa (VG.Impl.Ffdh.Arm.SharedCheckDomain.body (mop backend)) s fun t =>
      t.gpr .r0 = checkedDomainFlag p ∧ Frame (sharedPublicBodyWrites p s) s.mem t.mem := by
  rw [VG.Impl.Ffdh.Arm.SharedCheckDomain.body, WP.seq_iff]
  refine WP.mono (VettedGroups.code_ok s h h24 h28 h32 table) ?_
  rintro u ⟨context, cap, memU, restU⟩
  rw [WP.seq_iff]
  refine WP.mono (VettedGroups.zero_test u .r11) ?_
  rintro v ⟨⟨zero, memV⟩, restV⟩
  have value : v.z = (BitVec.ofNat 32 (recognize groups p.k p.dom) == 0) := by
    rw [zero, cap]
  by_cases hit : BitVec.ofNat 32 (recognize groups p.k p.dom) ≠ 0
  · refine WP.ite true (by simp only [eval, value, beq_eq_false_iff_ne.mpr hit]; rfl)
      (fun _ => ?_) (fun bad => Bool.noConfusion bad)
    have recognized : recognize groups p.k p.dom ≠ 0 := by
      intro impossible
      exact hit (by rw [impossible]; rfl)
    have valid := VG.Proof.Ffdh.VettedValidation.recognized_domain_valid groups
      (fun _ hg => hg) (by rw [p.domainLength]; split <;> simp) recognized
    refine WP.mono (ret_ok v 1 (by decide)) ?_
    rintro t ⟨⟨result, memT⟩, _⟩
    refine ⟨?_, ?_⟩
    · rw [checkedDomainFlag_spec, valid]
      exact result
    · rw [memT, memV, memU]
      exact Frame.refl _ _
  · have contextV := context.of_mem memV restV ((restV.gpr .r0 (by simp)).trans context.ptr)
    refine WP.ite false (by rw [Classical.not_not] at hit; simp only [eval, value, hit]; rfl)
      (fun bad => Bool.noConfusion bad) (fun _ => ?_)
    refine WP.mono (head_ok backend v contextV ((calls.after restU).after restV) stable h0 h24 h28 h32) ?_
    rintro t ⟨result, frame⟩
    refine ⟨result, ?_⟩
    rw [memV, memU] at frame
    simpa only [sharedPublicBodyWrites, bodyWrites, restV.sp, restU.sp] using frame

/-! ## The function -/

open VG.Impl.Ffdh.Arm.VettedGroups (tableSym groups) in
/-- What the precondition gives the function, with the 48 bytes below its frame. -/
structure Input (p : Inputs) (s : State) : Prop extends DomainFnInput p s where
  table : VettedGroups.TableAt ((entered s).syms tableSym) groups (entered s)
  safe : VettedGroups.TableSafe ((entered s).syms tableSym) groups
    [⟨State.addr (entered s).sp, 72⟩]
  calls : DomainCallMemory p (entered s)
  sharedSaved : ∀ r ∈ sharedPublicBodyWrites p (entered s),
    (⟨State.addr (pcPushed s).sp, 56⟩ : Region).Disjoint r

open VG.Impl.Ffdh.Arm.VettedGroups (tableSym groups) in
theorem entered_ok (backend : MontBackend) (s : State) {p : Inputs}
    (h : ArgumentMemory p [] s) (calls : DomainCallMemory p s)
    (domain : s.gpr .r0 = p.domain) (domainLength : s.gpr .r1 = BitVec.ofNat 32 p.dom.length)
    (count : s.gpr .r2 = BitVec.ofNat 32 p.k) (scratch : s.gpr .r3 = p.base)
    (table : VettedGroups.TableAt (s.syms tableSym) groups s)
    (safe : VettedGroups.TableSafe (s.syms tableSym) groups [⟨State.addr s.sp, 72⟩]) :
    WP isa (.seq (.block VG.Impl.Ffdh.Arm.Domain.CheckDomain.entry)
      (VG.Impl.Ffdh.Arm.SharedCheckDomain.body (mop backend))) s fun t =>
      t.gpr .r0 = checkedDomainFlag p ∧ Frame (sharedPublicBodyWrites p s) s.mem t.mem := by
  rw [WP.seq_iff]
  refine WP.mono_syms (withAllRest (domainEntry_ok s h domain domainLength count scratch)) ?_
  rintro u ⟨⟨context, frameU⟩, restU⟩ syms
  have tableU := table.after_frame safe frameU restU
  rw [← syms] at tableU
  refine WP.mono (body_ok backend u context (calls.after restU) (by decide) (by decide) (by decide)
    (by decide) (by decide) tableU) ?_
  rintro t ⟨result, frameT⟩
  have entryFrame : Frame (sharedPublicBodyWrites p s) s.mem u.mem :=
    frameU.mono (by simp [sharedPublicBodyWrites, bodyWrites])
  change Frame [⟨State.addr p.base, 8 * p.len⟩, ⟨State.addr u.sp, 72⟩, belowA u.sp 48] u.mem t.mem at frameT
  rw [restU.sp] at frameT
  exact ⟨result, entryFrame.trans frameT⟩

theorem fn_ok (backend : MontBackend) (s : State) {p : Inputs} (h : Input p s) :
    WP isa (VG.Impl.Ffdh.Arm.SharedCheckDomain.code (mop backend)) s fun t =>
      abiPreserved s t ∧ t.gpr .r0 = checkedDomainFlag p := by
  unfold VG.Impl.Ffdh.Arm.SharedCheckDomain.code
  refine framed_of_separate _ s h.stackFits (sharedPublicBodyWrites p (entered s))
    (fun _ status => status = checkedDomainFlag p) h.sharedSaved ?_
  refine WP.mono (entered_ok backend (entered s) h.args h.calls h.domain h.domainLength
    h.count h.scratch h.table h.safe) ?_
  rintro t ⟨result, frame⟩
  exact ⟨frame, result⟩

/-! ## From the precondition -/

open VG.Impl.Ffdh.Arm.VettedGroups

/-- The contract the function is proven against. -/
abbrev contract := Spec.Ffdh.checkDomainContract (abi.withConsts tableConsts) 176

theorem pre128 (s : State) (pre : (Spec.Ffdh.checkDomainContract abi 176).pre s) :
    (Spec.Ffdh.checkDomainContract abi 128).pre s := by
  sig_pre [Spec.Ffdh.checkDomainContract, Spec.Ffdh.checkDomainSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at pre ⊢
  obtain ⟨stackFit, argFit, rd, wr, domS, sArgs, stackDom, stackS, stackArgs, domFit, sFit, bounds,
    domainLen, space⟩ := pre
  have inner : Region.Sub ⟨State.addr s.sp - BitVec.ofNat 64 128, 128⟩
      ⟨State.addr s.sp - BitVec.ofNat 64 176, 176⟩ :=
    Offset.below_mono _ (by decide) (by decide)
  exact ⟨by omega_using [stackFit], argFit, rd, wr, domS, sArgs, stackDom.sub_left inner,
    stackS.sub_left inner, stackArgs.sub_left inner, domFit, sFit, bounds, domainLen, space⟩

private theorem entered_read_widen {s : State} {a : Addr} {n : Nat}
    (h : InRegions ((entered (stripConsts tableConsts s)).rd ++
      (entered (stripConsts tableConsts s)).wr) a n) :
    InRegions ((entered s).rd ++ (entered s).wr) a n := by
  obtain ⟨r, member, contains⟩ := h
  refine ⟨r, ?_, contains⟩
  rcases List.mem_append.mp member with read | write
  · exact List.mem_append_left _ (List.mem_of_mem_take read)
  · exact List.mem_append_right _ write

theorem input_widen {s : State} {p : Inputs}
    (h : DomainFnInput p (stripConsts tableConsts s)) : DomainFnInput p s := by
  refine ⟨h.stackFits, ?_, h.domain, h.domainLength, h.count, h.scratch, h.saved⟩
  exact ⟨h.args.workspace.congr rfl,
    ⟨h.args.locals.space.congr rfl, h.args.locals.separate⟩,
    ⟨h.args.domain.fits, entered_read_widen h.args.domain.readable,
      h.args.domain.separate, h.args.domain.bytes⟩,
    h.args.domainStack, h.args.saved⟩

theorem table_input {s : State} (hc : ConstsOk tableConsts 176 s) (stackFit : 176 ≤ s.sp.toNat) :
    VettedGroups.TableAt ((entered s).syms tableSym) groups (entered s) ∧
    VettedGroups.TableSafe ((entered s).syms tableSym) groups
      [⟨State.addr (entered s).sp, 72⟩] := by
  have geometry := VettedGroups.consts_singleton_regions (name := tableSym) (words := tableWords) hc
  have fit := hc.fit (name := tableSym) (ws := tableWords) List.mem_cons_self
  rw [VettedGroups.tableWords_length] at geometry fit
  have span : tableBytes.length = 8 * 2218 := VettedGroups.tableBytes_length
  have reserved : (⟨State.addr (s.syms tableSym), tableBytes.length⟩ : Region).Disjoint
      (FrameStack.belowA s.sp 176) := by
    rw [span]
    apply geometry.2.2
    rw [FrameStack.belowA, FrameStack.addr_sub' stackFit]
    simp only [abi, stackBelow]
    exact List.mem_cons_self
  have localSub : (⟨State.addr (entered s).sp, 72⟩ : Region).Sub (FrameStack.belowA s.sp 176) :=
    fun a h => FrameStack.belowA_sub (by decide) stackFit a
      (locals_sub_reserved s (by omega_using [stackFit]) a h)
  have savedSub : (⟨State.addr (pcPushed s).sp, 56⟩ : Region).Sub (FrameStack.belowA s.sp 176) :=
    fun a h => FrameStack.belowA_sub (by decide) stackFit a
      (saved_sub_reserved s (by omega_using [stackFit]) a h)
  have bytes : Spec.Rsa.bytesAt (entered s).mem
      (State.addr ((entered s).syms tableSym)) tableBytes.length = tableBytes := by
    rw [VG.Proof.Bignum.Arm.rsa_bytes_frame (entered_frame s (by omega_using [stackFit]))
      (by rw [span]; omega_using []) (by
        intro r hr
        obtain rfl := List.mem_singleton.mp hr
        exact reserved.sub_right savedSub)]
    exact VettedGroups.consts_table_bytes hc
  apply VettedGroups.tableOfBytes (entered s) ((entered s).syms tableSym) groups
    (by change ((entered s).syms tableSym).toNat + tableBytes.length ≤ 2 ^ 32; rw [span]; exact fit)
    (entered_read (VettedGroups.consts_table_read hc)) bytes
  · intro g hg
    simp only [groups, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact reserved.sub_right localSub

/-- What the precondition of the contract without the table gives at 176 bytes. -/
theorem calls_input (s : State) (pre : (Spec.Ffdh.checkDomainContract abi 176).pre s)
    {p : Inputs} (base : s.gpr .r3 = p.base) (domain : s.gpr .r0 = p.domain)
    (publicValue : p.publicValue = p.domain)
    (capacity : (stackArg s 0).toNat = p.len)
    (domainBytes : Spec.Rsa.bytesAt s.mem (State.addr p.domain) (s.gpr .r1).toNat = p.dom)
    (old : DomainFnInput p s) :
    DomainCallMemory p (entered s) ∧ ∀ r ∈ sharedPublicBodyWrites p (entered s),
      (⟨State.addr (pcPushed s).sp, 56⟩ : Region).Disjoint r := by
  sig_pre [Spec.Ffdh.checkDomainContract, Spec.Ffdh.checkDomainSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at pre
  obtain ⟨stackFit, _, _, _, _, _, stackDom, stackS, _, _, _, _, _, _⟩ := pre
  have domLen : (s.gpr .r1).toNat = p.dom.length := by
    have eq := congrArg List.length domainBytes
    simpa only [VG.Proof.Bignum.bytesAt_length] using eq
  rw [domain, domLen] at stackDom
  rw [base, capacity, Nat.mul_comm p.len 8] at stackS
  have reserved : State.addr s.sp - BitVec.ofNat 64 176 = State.addr (s.sp - BitVec.ofNat 32 176) :=
    (addr_sub' stackFit).symm
  simp only [State.addr] at reserved
  rw [reserved] at stackDom stackS
  have prefixSub : (⟨State.addr p.domain, p.k⟩ : Region).Sub ⟨State.addr p.domain, p.dom.length⟩ :=
    Region.sub_prefix (by rw [p.domainLength]; split <;> omega_using [])
  have calls := DomainCallMemory.of_outer (p := p) stackFit (entered_sp s)
    stackS stackDom.symm (by rw [publicValue]; exact stackDom.symm.sub_left prefixSub)
  refine ⟨calls, ?_⟩
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact old.saved r hr
  · have eq := List.mem_singleton.mp hr
    subst r
    have shifted : (pcPushed s).sp = (entered s).sp + BitVec.ofNat 32 72 := (BitVec.sub_add_cancel _ _).symm
    have fit : (entered s).sp.toNat + 72 < 2^32 := by
      rw [entered_nat s (by omega_using [stackFit])]; have := s.sp.isLt; omega_using []
    rw [shifted, VG.Arm.addr_add fit, belowA, addr_sub' calls.stack.fit]
    exact (Offset.disjoint_below_above _ (m:=48) (a:=72) (l:=56) (by decide)).symm

theorem input (s : State) (pre : contract.pre s)
    {p : Inputs} (base : s.gpr .r3 = p.base) (domain : s.gpr .r0 = p.domain)
    (publicValue : p.publicValue = p.domain)
    (count : (s.gpr .r2).toNat = p.k) (capacity : (stackArg s 0).toNat = p.len)
    (domainBytes : Spec.Rsa.bytesAt s.mem (State.addr p.domain) (s.gpr .r1).toNat = p.dom) :
    Input p s := by
  have split : (Spec.Ffdh.checkDomainContract abi 176).pre (stripConsts tableConsts s) ∧
      ConstsOk tableConsts 176 s := pre_consts.mp pre
  have old := domain_input (stripConsts tableConsts s) (pre128 _ split.1) base domain count capacity domainBytes
  have calls := calls_input (stripConsts tableConsts s) split.1 base domain publicValue capacity domainBytes old
  have wide := input_widen old
  have stackFit : 176 ≤ s.sp.toNat := by
    have plain := split.1
    sig_pre [Spec.Ffdh.checkDomainContract, Spec.Ffdh.checkDomainSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at plain
    exact plain.1
  have table := table_input split.2 stackFit
  exact ⟨wide, table.1, table.2, calls.1.congr_sp rfl, calls.2⟩

theorem data (s : State) (pre : contract.pre s) :
    ∃ p : Inputs, s.gpr .r3 = p.base ∧ s.gpr .r0 = p.domain ∧ p.publicValue = p.domain ∧
      (s.gpr .r2).toNat = p.k ∧ (stackArg s 0).toNat = p.len ∧
      Spec.Rsa.bytesAt s.mem (State.addr p.domain) (s.gpr .r1).toNat = p.dom ∧ Input p s := by
  have original := pre
  have split : (Spec.Ffdh.checkDomainContract abi 176).pre (stripConsts tableConsts s) ∧
      ConstsOk tableConsts 176 s := pre_consts.mp pre
  have plain := split.1
  sig_pre [Spec.Ffdh.checkDomainContract, Spec.Ffdh.checkDomainSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at plain
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, bounds, domainLen, space⟩ := plain
  let dom := Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat
  have domLength : dom.length = (s.gpr .r1).toNat := VG.Proof.Bignum.bytesAt_length _ _ _
  let p : Inputs := {
    base := s.gpr .r3
    domain := s.gpr .r0
    publicValue := s.gpr .r0
    privateValue := 0
    output := 0
    entropy := 0
    len := (stackArg s 0).toNat
    k := (s.gpr .r2).toNat
    privateLength := 0
    hasQ := decide ((s.gpr .r1).toNat = 3 * (s.gpr .r2).toNat)
    dom := dom
    minLength := bounds.1
    maxLength := bounds.2
    space := space
    domainLength := by
      rw [domLength]
      simp only [decide_eq_true_eq]
      split
      · assumption
      · rcases domainLen with h | h
        · exact h
        · contradiction }
  exact ⟨p, rfl, rfl, rfl, rfl, rfl, rfl, input s original (p := p) rfl rfl rfl rfl rfl rfl⟩

/-- One imported-domain check for every shared Montgomery product. -/
def code (b : MontBackend) : Prog isa :=
  VG.Impl.Ffdh.Arm.SharedCheckDomain.code (mop b)

theorem correct (backend : MontBackend) (s : State) (pre : contract.pre s) :
    ∃ tr t, Exec isa (code backend) s tr t ∧ abiPreserved s t ∧ contract.post s t := by
  obtain ⟨p, _, domain, _, count, _, bytes, input⟩ := data s pre
  obtain ⟨tr, t, run, preserved, result⟩ := fn_ok backend s input
  refine ⟨tr, t, run, preserved, ?_⟩
  change (Spec.Ffdh.checkDomainContract abi 176).post s t
  sig_post [Spec.Ffdh.checkDomainContract, Spec.Ffdh.checkDomainSig, abi,
    argRegs, reduceClassify, Loc.val, State.addr]
  rw [BitVec.setWidth_append_eq_right, domain, count]
  change (t.gpr .r0).toNat = if Spec.Ffdh.domainValid p.k
    (Spec.Rsa.bytesAt s.mem (State.addr p.domain) (s.gpr .r1).toNat) then 1 else 0
  rw [bytes, result, checkedDomainFlag_spec]
  split <;> rfl

/-! ## Constant time -/

theorem qRange_ct {p : Inputs} {slots : List Nat}
    (stable : stableSlots slots = true) (h60 : 60 ∈ slots) (h32 : 32 ∈ slots) (hasQ : p.hasQ = true) :
    RelCT isa (fun s t => ImportAtInput p slots s ∧ ImportAtInput p slots t ∧ s.sp = t.sp)
      VG.Impl.Ffdh.Arm.Domain.CheckDomain.qRange (fun _ _ => True) := by
  let P := ArithmeticReady p.base p.len p.w
  have op1 : Operand 1 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have imported := importAt_ct (p := p) (slots := slots) (a := 1) (slot := 60) (countSlot := 32)
    (k := p.k) stable h60 h32 rfl (by decide)
  have wpImport (s : State) (h : ImportAtInput p slots s) :
      WP isa (VG.Impl.Ffdh.Arm.Domain.importAt 1 60 32) s P :=
    WP.mono (importAt_ok s 1 60 32 h.context stable h60 h32 h.ready (by decide) (by decide)
      (h.context.qBytes hasQ) (by rw [p.qLength hasQ]; have := p.minLength; omega)
      (by rw [p.qLength hasQ]; exact p.width.2.2.2.1)
      (by change BitVec.ofNat 32 p.k = _; rw [p.qLength hasQ])) fun _ j => j.2.1
  have save := saveFlag_ct.mono (P' := fun (s t : State) => P s ∧ P t ∧ s.sp = t.sp)
    (fun _ _ h => h.1.ptr.trans h.2.1.ptr.symm) (fun _ _ h => h)
  have finish := andFlag_ct.mono (P' := fun (s t : State) => P s ∧ P t ∧ s.sp = t.sp)
    (fun _ _ h => h.1.ptr.trans h.2.1.ptr.symm) (fun _ _ h => h)
  have wpRange (s : State) (h : P s) := inRange_ready s h op1 (by decide)
  have wpSave (s : State) (h : P s) := WP.mono (saveFlag_ok s h) fun _ j => j.1
  have wpOdd (s : State) (h : P s) := WP.mono (odd_ok s h (by decide : 1 < 8)) fun _ j => j.1
  unfold VG.Impl.Ffdh.Arm.Domain.CheckDomain.qRange
  exact relCT_chain imported wpImport wpImport (relCT_chain (inRange_ct op1 (by decide)) wpRange wpRange
    (relCT_chain save wpSave wpSave (relCT_chain (odd_ct (by decide : 1 < 8)) wpOdd wpOdd finish)))

/-- After a preparation for the modulus `M`, at the stack pointer `sp0`. -/
structure Prepared (p : Inputs) (slots : List Nat) (M : Nat) (sp0 : BitVec 32) (s : State) : Prop where
  context : Context p slots s
  ready : ArithmeticReady p.base p.len p.w s
  modulus : numAt s.mem (State.addr p.base) p.w 0 = M
  r2 : numAt s.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % M
  calls : DomainCallMemory p s
  sp : s.sp = sp0

/-- With one in array 7, before the reduction. -/
structure WithOne (p : Inputs) (M : Nat) (sp0 : BitVec 32) (s : State) : Prop where
  ready : ArithmeticReady p.base p.len p.w s
  modulus : numAt s.mem (State.addr p.base) p.w 0 = M
  r2 : numAt s.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % M
  one : numAt s.mem (State.addr p.base) p.w 7 = 1
  calls : DomainCallMemory p s
  sp : s.sp = sp0

theorem divides_ct (backend : MontBackend) {p : Inputs} {slots : List Nat}
    (stable : stableSlots slots = true) (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h32 : 32 ∈ slots)
    (h60 : 60 ∈ slots) (hasQ : p.hasQ = true) (large : 1 < p.Q) (odd : p.Q % 2 = 1) :
    RelCT isa (fun s t => (Context p slots s ∧ DomainCallMemory p s) ∧
      (Context p slots t ∧ DomainCallMemory p t) ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.SharedCheckDomain.divides (mop backend)) (fun _ _ => True) := by
  have op0 : Operand 0 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op1 : Operand 1 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op4 : Operand 4 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have family (sp0 : BitVec 32) :
      RelCT isa (fun s t => ((Context p slots s ∧ DomainCallMemory p s) ∧ s.sp = sp0) ∧
        ((Context p slots t ∧ DomainCallMemory p t) ∧ t.sp = sp0) ∧ s.sp = t.sp)
        (VG.Impl.Ffdh.Arm.SharedCheckDomain.divides (mop backend)) (fun _ _ => True) := by
    let correct := fun o a b ho ha hb v input => backend.correct v (base := p.base) (len := p.len)
      (w := p.w) (o := o) (a := a) (b := b) input ho ha hb
    let K := TwoExp.sharedMontgomery p.base sp0 p.len p.w backend.name backend.mul correct backend.stackOk
    have timing : TwoExp.MontgomeryTiming K :=
      TwoExp.sharedMontgomeryTiming p.base sp0 p.len p.w backend.name backend.mul correct backend.stackOk
        (fun _ _ _ ho ha hb => backend.rawCT ho ha hb)
    have prepare := (prepareQ_ct backend stable h0 h32 h60 hasQ large odd).mono
      (P' := fun (s t : State) => ((Context p slots s ∧ DomainCallMemory p s) ∧ s.sp = sp0) ∧
        ((Context p slots t ∧ DomainCallMemory p t) ∧ t.sp = sp0) ∧ s.sp = t.sp)
      (fun _ _ h => ⟨h.1.1, h.2.1.1, h.2.2⟩) (fun _ _ h => h)
    have wpPrep (s : State) (h : (Context p slots s ∧ DomainCallMemory p s) ∧ s.sp = sp0) :
        WP isa (VG.Impl.Ffdh.Arm.SharedPrepare.prepareAt (mop backend) 60) s (Prepared p slots p.Q sp0) :=
      WP.mono (prepareQ_ok backend s h.1.1 h.1.2 stable h0 h32 h60 hasQ large odd) fun _ j =>
        ⟨j.1, j.2.1, j.2.2.1, j.2.2.2.1, h.1.2.after j.2.2.2.2.2, j.2.2.2.2.2.sp.trans h.2⟩
    have imported := (importAt_ct (p := p) (a := 1) (slot := 24) (k := p.k)
      stable h24 h32 rfl (by decide)).mono
      (P' := fun (s t : State) => Prepared p slots p.Q sp0 s ∧ Prepared p slots p.Q sp0 t ∧ s.sp = t.sp)
      (fun _ _ h => ⟨⟨h.1.context, h.1.ready⟩, ⟨h.2.1.context, h.2.1.ready⟩, h.2.2⟩) (fun _ _ h => h)
    have wpImport (s : State) (h : Prepared p slots p.Q sp0 s) :
        WP isa (VG.Impl.Ffdh.Arm.Domain.importAt 1 24 32) s (Prepared p slots p.Q sp0) := by
      refine WP.mono (importAt_ok s 1 24 32 h.context stable h24 h32 h.ready (by decide) (by decide)
        h.context.pBytes (by rw [p.pLength]; have := p.minLength; omega) (by rw [p.pLength]; exact p.width.2.2.2.1)
        (by change BitVec.ofNat 32 p.k = _; rw [p.pLength])) ?_
      rintro u ⟨context, ready, _, keeps, _, rest⟩
      have fits : arrAt p.w 8 ≤ 8 * p.len := ready.width ▸ ready.layout.2.2.1
      exact ⟨context, ready, (keeps_array_num keeps fits op0 (by decide)).trans h.modulus,
        (keeps_array_num keeps fits op4 (by decide)).trans h.r2, h.calls.after rest, rest.sp.trans h.sp⟩
    have one := (smallConst_ct (base := p.base) (len := p.len) (w := p.w) 1
      (by decide : 7 < 8) (by decide) (by decide)).mono
      (P' := fun (s t : State) => Prepared p slots p.Q sp0 s ∧ Prepared p slots p.Q sp0 t ∧ s.sp = t.sp)
      (fun _ _ h => ⟨h.1.ready, h.2.1.ready, h.2.2⟩) (fun _ _ h => h)
    have wpOne (s : State) (h : Prepared p slots p.Q sp0 s) :
        WP isa (VG.Impl.Bignum.Arm.smallConst 7 1) s (WithOne p p.Q sp0) := by
      refine WP.mono (smallConst_ok s 1 h.ready (by decide : 7 < 8) (by decide) (by decide) (by decide)) ?_
      rintro u ⟨ready, one, _, keeps, _, rest⟩
      have fits : arrAt p.w 8 ≤ 8 * p.len := ready.width ▸ ready.layout.2.2.1
      exact ⟨ready, (keeps_array_num keeps fits op0 (by decide)).trans h.modulus,
        (keeps_array_num keeps fits op4 (by decide)).trans h.r2, one, h.calls.after rest, rest.sp.trans h.sp⟩
    have toReduce (s : State) (h : WithOne p p.Q sp0 s) :
        ReduceReady p.base p.len p.w (TwoExp.CallReady p.base sp0 p.len) s :=
      ⟨h.ready, ⟨h.calls.stack, h.sp⟩, by rw [h.r2, h.modulus]; exact Nat.mod_lt _ (by omega),
        by rw [h.one, h.modulus]; exact large⟩
    have reduce := (reduce_ct K timing op1 (by decide) (by decide)).mono
      (P' := fun (s t : State) => WithOne p p.Q sp0 s ∧ WithOne p p.Q sp0 t ∧ s.sp = t.sp)
      (fun s t h => ⟨toReduce s h.1, toReduce t h.2.1, h.2.2⟩) (fun _ _ h => h)
    have wpReduce (s : State) (h : WithOne p p.Q sp0 s) :
        WP isa (VG.Impl.Ffdh.Arm.SharedCheckDomain.reduce K.op 1) s (ArithmeticReady p.base p.len p.w) :=
      WP.mono (reduce_ok K s h.ready ⟨h.calls.stack, h.sp⟩ op1 (by decide) (by decide)
        h.modulus odd large h.r2 h.one) fun _ j => j.1
    unfold VG.Impl.Ffdh.Arm.SharedCheckDomain.divides
    exact relCT_chain prepare wpPrep wpPrep (relCT_chain imported wpImport wpImport
      (relCT_chain one wpOne wpOne (relCT_chain reduce wpReduce wpReduce (isOne_ct op1))))
  intro s t tr1 tr2 u v h e1 e2
  exact family s.sp s t tr1 tr2 u v ⟨⟨h.1, rfl⟩, ⟨h.2.1, h.2.2.symm⟩, h.2.2⟩ e1 e2

theorem generator_ct (backend : MontBackend) {p : Inputs} {slots : List Nat}
    (stable : stableSlots slots = true) (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h32 : 32 ∈ slots)
    (h56 : 56 ∈ slots) (h60 : 60 ∈ slots) (hasQ : p.hasQ = true) (large : 1 < p.P) (odd : p.P % 2 = 1) :
    RelCT isa (fun s t => (Context p slots s ∧ DomainCallMemory p s) ∧
      (Context p slots t ∧ DomainCallMemory p t) ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.SharedCheckDomain.generator (mop backend)) (fun _ _ => True) := by
  have wp (s : State) (h : Context p slots s ∧ DomainCallMemory p s) :
      WP isa (VG.Impl.Ffdh.Arm.SharedPrepare.prepareAt (mop backend) 24) s fun u =>
        SubgroupInput p slots 56 ((p.dom.drop p.k).take p.k) u ∧ DomainCallMemory p u := by
    refine WP.mono (domainSharedPrepareAt24_ok backend s h.1 h.2 stable h0 h24 h32 large odd) ?_
    rintro u ⟨context, ready, modulus, r2, _, rest⟩
    exact ⟨⟨context, ready, modulus, r2, context.gBytes⟩, h.2.after rest⟩
  unfold VG.Impl.Ffdh.Arm.SharedCheckDomain.generator
  exact relCT_chain (domainSharedPrepareAt24_ct backend stable h0 h24 h32 large odd) wp wp
    ((sharedCheckPublicSubgroup_ct backend stable h56 h60 h32 hasQ p.gLength odd).seq finishFlag_ct)

/-- With the status flag `flag` in r11. -/
structure Flagged (p : Inputs) (slots : List Nat) (flag : BitVec 32) (s : State) : Prop where
  context : Context p slots s
  calls : DomainCallMemory p s
  result : s.gpr .r11 = flag

theorem Flagged.after_mem {p : Inputs} {slots : List Nat} {flag : BitVec 32} {s t : State}
    (h : Flagged p slots flag s) (mem : t.mem = s.mem) (rest : Rest [] s t) : Flagged p slots flag t :=
  ⟨h.context.of_mem mem rest ((rest.gpr .r0 (by simp)).trans h.context.ptr), h.calls.after rest,
    (rest.gpr .r11 (by simp)).trans h.result⟩

theorem dividesThen_ct (backend : MontBackend) {p : Inputs} {slots : List Nat}
    (stable : stableSlots slots = true) (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h32 : 32 ∈ slots)
    (h56 : 56 ∈ slots) (h60 : 60 ∈ slots) (hasQ : p.hasQ = true)
    (large : 1 < p.P) (odd : p.P % 2 = 1) (qLarge : 1 < p.Q) (qOdd : p.Q % 2 = 1) :
    RelCT isa (fun s t => (Context p slots s ∧ DomainCallMemory p s) ∧
      (Context p slots t ∧ DomainCallMemory p t) ∧ s.sp = t.sp)
      (.seq (VG.Impl.Ffdh.Arm.SharedCheckDomain.divides (mop backend)) (VG.Impl.Ffdh.Arm.Domain.ifFlag
        (VG.Impl.Ffdh.Arm.SharedCheckDomain.generator (mop backend))
        (VG.Impl.Ffdh.Arm.Domain.ret 0))) (fun _ _ => True) := by
  let P := Flagged p slots (if p.P % p.Q = 1 then 1 else 0)
  have wp (s : State) (h : Context p slots s ∧ DomainCallMemory p s) :
      WP isa (VG.Impl.Ffdh.Arm.SharedCheckDomain.divides (mop backend)) s P :=
    WP.mono (divides_ok backend s h.1 h.2 stable h0 h24 h32 h60 hasQ qLarge qOdd) fun _ j =>
      ⟨j.1, h.2.after j.2.2.2, j.2.1⟩
  have branches : RelCT isa (fun s t => P s ∧ P t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.Domain.ifFlag (VG.Impl.Ffdh.Arm.SharedCheckDomain.generator (mop backend))
        (VG.Impl.Ffdh.Arm.Domain.ret 0)) (fun _ _ => True) := by
    apply ifFlag_known_ct (decide (p.P % p.Q = 1))
      (fun _ h => by simpa only [decide_eq_true_eq] using h.result)
      (fun _ _ h mem rest => h.after_mem mem rest)
    · intro _
      exact (generator_ct backend stable h0 h24 h32 h56 h60 hasQ large odd).mono
        (fun _ _ h => ⟨⟨h.1.context, h.1.calls⟩, ⟨h.2.1.context, h.2.1.calls⟩, h.2.2⟩) (fun _ _ h => h)
    · intro _
      exact (ret_ct 0).mono (fun _ _ _ => trivial) (fun _ _ h => h)
  exact relCT_chain (divides_ct backend stable h0 h24 h32 h60 hasQ qLarge qOdd) wp wp branches

theorem qChecks_ct (backend : MontBackend) {p : Inputs} {slots : List Nat}
    (stable : stableSlots slots = true) (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h32 : 32 ∈ slots)
    (h56 : 56 ∈ slots) (h60 : 60 ∈ slots) (hasQ : p.hasQ = true) (large : 1 < p.P) (odd : p.P % 2 = 1) :
    RelCT isa (fun s t => SharedSubgroupInput p slots 56 ((p.dom.drop p.k).take p.k) s ∧
      SharedSubgroupInput p slots 56 ((p.dom.drop p.k).take p.k) t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.SharedCheckDomain.qChecks (mop backend)) (fun _ _ => True) := by
  let P := SharedSubgroupInput p slots 56 ((p.dom.drop p.k).take p.k)
  let Q := Flagged p slots (qRangeFlag p)
  have ranges := (qRange_ct stable h60 h32 hasQ).mono
    (P' := fun (s t : State) => P s ∧ P t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨⟨h.1.context, h.1.ready⟩, ⟨h.2.1.context, h.2.1.ready⟩, h.2.2⟩) (fun _ _ h => h)
  have wp (s : State) (h : P s) : WP isa VG.Impl.Ffdh.Arm.Domain.CheckDomain.qRange s Q :=
    WP.mono (qRange_ok s h.context stable h60 h32 hasQ h.ready h.modulus odd h.r2) fun _ j =>
      ⟨j.1, h.calls.after j.2.2.2.2.2.2, j.2.2.1⟩
  have branches : RelCT isa (fun s t => Q s ∧ Q t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.Domain.ifFlag
        (.seq (VG.Impl.Ffdh.Arm.SharedCheckDomain.divides (mop backend)) (VG.Impl.Ffdh.Arm.Domain.ifFlag
          (VG.Impl.Ffdh.Arm.SharedCheckDomain.generator (mop backend))
          (VG.Impl.Ffdh.Arm.Domain.ret 0))) (VG.Impl.Ffdh.Arm.Domain.ret 0)) (fun _ _ => True) := by
    apply ifFlag_known_ct (decide (2 < p.Q ∧ p.Q < p.P - 1 ∧ p.Q % 2 = 1))
      (fun _ h => by simpa only [qRangeFlag, decide_eq_true_eq] using h.result)
      (fun _ _ h mem rest => h.after_mem mem rest)
    · intro valid
      have facts := of_decide_eq_true valid
      exact (dividesThen_ct backend stable h0 h24 h32 h56 h60 hasQ large odd (by omega) facts.2.2).mono
        (fun _ _ h => ⟨⟨h.1.context, h.1.calls⟩, ⟨h.2.1.context, h.2.1.calls⟩, h.2.2⟩) (fun _ _ h => h)
    · intro _
      exact (ret_ct 0).mono (fun _ _ _ => trivial) (fun _ _ h => h)
  unfold VG.Impl.Ffdh.Arm.SharedCheckDomain.qChecks
  exact relCT_chain ranges wp wp branches

theorem tail_ct (backend : MontBackend) {p : Inputs} {slots : List Nat}
    (stable : stableSlots slots = true) (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h28 : 28 ∈ slots)
    (h32 : 32 ∈ slots) (h56 : 56 ∈ slots) (h60 : 60 ∈ slots) (large : 1 < p.P) (odd : p.P % 2 = 1) :
    RelCT isa (fun s t => SharedSubgroupInput p slots 56 ((p.dom.drop p.k).take p.k) s ∧
      SharedSubgroupInput p slots 56 ((p.dom.drop p.k).take p.k) t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.Domain.withQ (VG.Impl.Ffdh.Arm.SharedCheckDomain.qChecks (mop backend))
        (VG.Impl.Ffdh.Arm.Domain.ret 1)) (fun _ _ => True) := by
  let P := SharedSubgroupInput p slots 56 ((p.dom.drop p.k).take p.k)
  let Q := fun s : State => P s ∧ s.z = !p.hasQ
  have trace := qTest_ct.mono (P' := fun (s t : State) => P s ∧ P t ∧ s.sp = t.sp)
    (fun _ _ h => h.2.2) (fun _ _ _ => trivial)
  have wp (s : State) (h : P s) : WP isa VG.Impl.Ffdh.Arm.Domain.qTest s Q := by
    refine WP.mono (qTest_ok s h.context h28 h32) ?_
    rintro u ⟨⟨zero, mem⟩, rest⟩
    exact ⟨⟨h.toSubgroupInput.after_mem stable mem rest ((rest.gpr .r0 (by simp)).trans h.context.ptr),
      h.calls.after rest⟩, zero⟩
  have branches : RelCT isa (fun s t => Q s ∧ Q t ∧ s.sp = t.sp)
      (.ite .ne (VG.Impl.Ffdh.Arm.SharedCheckDomain.qChecks (mop backend))
        (VG.Impl.Ffdh.Arm.Domain.ret 1)) (fun _ _ => True) := by
    apply iteKnown_ct p.hasQ (fun s h => by simp only [eval, h.2, Bool.not_not])
    · intro hasQ
      exact (qChecks_ct backend stable h0 h24 h32 h56 h60 hasQ large odd).mono
        (fun _ _ h => ⟨h.1.1, h.2.1.1, h.2.2⟩) (fun _ _ h => h)
    · intro _
      exact (ret_ct 1).mono (fun _ _ _ => trivial) (fun _ _ h => h)
  unfold VG.Impl.Ffdh.Arm.Domain.withQ
  exact relCT_chain trace wp wp branches

structure MainInput (p : Inputs) (slots : List Nat) (yb : List Byte) (s : State) : Prop where
  context : Context p slots s
  value : Octets p.base p.g p.len yb s
  separate : Region.Disjoint ⟨State.addr p.g, yb.length⟩ ⟨State.addr s.sp, 72⟩
  below : Region.Disjoint ⟨State.addr p.g, yb.length⟩ (belowA s.sp 48)
  calls : DomainCallMemory p s

structure Imported (p : Inputs) (slots : List Nat) (yb : List Byte) (s : State) : Prop extends
    SharedSubgroupInput p slots 56 yb s where
  value : numAt s.mem (State.addr p.base) p.w 1 = Spec.Rsa.os2ip yb

structure Ranged (p : Inputs) (slots : List Nat) (yb : List Byte) (s : State) : Prop extends
    SharedSubgroupInput p slots 56 yb s where
  flag : s.gpr .r11 = if 1 < Spec.Rsa.os2ip yb ∧ Spec.Rsa.os2ip yb < p.P - 1 then 1 else 0

theorem main_ct (backend : MontBackend) {p : Inputs} {slots : List Nat}
    (stable : stableSlots slots = true) (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h28 : 28 ∈ slots)
    (h32 : 32 ∈ slots) (h56 : 56 ∈ slots) (h60 : 60 ∈ slots)
    (large : 1 < p.P) (odd : p.P % 2 = 1) :
    RelCT isa (fun s t => MainInput p slots ((p.dom.drop p.k).take p.k) s ∧
      MainInput p slots ((p.dom.drop p.k).take p.k) t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.SharedCheckDomain.main (mop backend)) (fun _ _ => True) := by
  let yb := (p.dom.drop p.k).take p.k
  have length : yb.length = p.k := p.gLength
  have op0 : Operand 0 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op1 : Operand 1 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op4 : Operand 4 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have prep := (domainSharedPrepareAt24_ct backend stable h0 h24 h32 large odd).mono
    (P' := fun (s t : State) => MainInput p slots yb s ∧ MainInput p slots yb t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨⟨h.1.context, h.1.calls⟩, ⟨h.2.1.context, h.2.1.calls⟩, h.2.2⟩) (fun _ _ h => h)
  have wpPrep (s : State) (h : MainInput p slots yb s) :
      WP isa (VG.Impl.Ffdh.Arm.SharedPrepare.prepareAt (mop backend) 24) s
        (SharedSubgroupInput p slots 56 yb) := by
    refine WP.mono (domainSharedPrepareAt24_ok backend s h.context h.calls stable h0 h24 h32 large odd) ?_
    rintro u ⟨context, ready, modulus, r2, frame, rest⟩
    refine ⟨⟨context, ready, modulus, r2, h.value.after_frame frame rest ?_⟩, h.calls.after rest⟩
    intro r hr
    simp only [domainPrepareWrites, prepareAtWrites, prepareWrites, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl | rfl) | rfl
    · exact h.value.separate
    · exact h.separate.sub_right (Offset.sub_base _ (by decide))
    · exact h.separate.sub_right (Offset.sub_base _ (by decide))
    · exact h.below
  have imports := (importAt_ct (p := p) (a := 1) stable h56 h32
    (show p.slotValue 32 = BitVec.ofNat 32 yb.length by change BitVec.ofNat 32 p.k = _; rw [length]) (by decide)).mono
    (P' := fun (s t : State) => SharedSubgroupInput p slots 56 yb s ∧ SharedSubgroupInput p slots 56 yb t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨⟨h.1.context, h.1.ready⟩, ⟨h.2.1.context, h.2.1.ready⟩, h.2.2⟩) (fun _ _ h => h)
  have wpImport (s : State) (h : SharedSubgroupInput p slots 56 yb s) :
      WP isa (VG.Impl.Ffdh.Arm.Domain.importAt 1 56 32) s (Imported p slots yb) := by
    refine WP.mono (importAt_ok s 1 56 32 h.context stable h56 h32 h.ready (by decide) (by decide) h.source
      (by rw [length]; have := p.minLength; omega) (by rw [length]; exact p.width.2.2.2.1)
      (by change BitVec.ofNat 32 p.k = _; rw [length])) ?_
    rintro u ⟨context, ready, value, keeps, frame, rest⟩
    have fits : arrAt p.w 8 ≤ 8 * p.len := ready.width ▸ ready.layout.2.2.1
    exact ⟨⟨⟨context, ready, (keeps_array_num keeps fits op0 (by decide)).trans h.modulus,
      (keeps_array_num keeps fits op4 (by decide)).trans h.r2, h.source.after_workspace frame rest⟩,
      h.calls.after rest⟩, value⟩
  have range := (inRange_ct (base := p.base) (len := p.len) (w := p.w) op1 (by decide)).mono
    (P' := fun (s t : State) => Imported p slots yb s ∧ Imported p slots yb t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨h.1.ready, h.2.1.ready, h.2.2⟩) (fun _ _ h => h)
  have wpRange (s : State) (h : Imported p slots yb s) :
      WP isa (VG.Impl.Ffdh.Arm.inRange 1) s (Ranged p slots yb) := by
    refine WP.mono (inRange_ok s h.ready op1 (by decide) (by rw [h.modulus]; exact odd)) ?_
    rintro u ⟨ready, flag, arrays, frame, rest⟩
    rw [h.value, h.modulus] at flag
    exact ⟨⟨h.toSharedSubgroupInput.toSubgroupInput.after_workspace stable frame rest ready
      ((arrays 0 op0 (by decide)).trans h.modulus) ((arrays 4 op4 (by decide)).trans h.r2),
      h.calls.after rest⟩, flag⟩
  let valid : Prop := 1 < Spec.Rsa.os2ip yb ∧ Spec.Rsa.os2ip yb < p.P - 1
  let Q := fun s : State => SharedSubgroupInput p slots 56 yb s ∧ s.z = !decide valid
  have tests := testFlag_ct.mono
    (P' := fun (s t : State) => Ranged p slots yb s ∧ Ranged p slots yb t ∧ s.sp = t.sp)
    (fun _ _ _ => trivial) (fun _ _ h => h)
  have wpTest (s : State) (h : Ranged p slots yb s) :
      WP isa VG.Impl.Ffdh.Arm.Domain.testFlag s Q := by
    refine WP.mono (testFlag_ok s) ?_
    rintro u ⟨⟨zero, mem⟩, rest⟩
    refine ⟨⟨h.toSharedSubgroupInput.toSubgroupInput.after_mem stable mem rest
      ((rest.gpr .r0 (by simp)).trans h.context.ptr), h.calls.after rest⟩, ?_⟩
    rw [zero, h.flag]
    change ((if valid then (1#32) else 0#32) == 0#32) = !decide valid
    by_cases hv : valid
    · rw [ite_eq_left hv, decide_eq_true hv]; rfl
    · rw [ite_eq_right hv, decide_eq_false hv]; rfl
  have branches : RelCT isa (fun s t => Q s ∧ Q t ∧ s.sp = t.sp)
      (.ite .ne (VG.Impl.Ffdh.Arm.Domain.withQ
        (VG.Impl.Ffdh.Arm.SharedCheckDomain.qChecks (mop backend))
        (VG.Impl.Ffdh.Arm.Domain.ret 1)) (VG.Impl.Ffdh.Arm.Domain.ret 0)) (fun _ _ => True) := by
    apply iteKnown_ct (decide valid) (fun s h => by simp only [eval, h.2, Bool.not_not])
    · intro _
      exact (tail_ct backend stable h0 h24 h28 h32 h56 h60 large odd).mono
        (fun _ _ h => ⟨h.1.1, h.2.1.1, h.2.2⟩) (fun _ _ h => h)
    · intro _
      exact (ret_ct 0).mono (fun _ _ _ => trivial) (fun _ _ h => h)
  unfold VG.Impl.Ffdh.Arm.SharedCheckDomain.main VG.Impl.Ffdh.Arm.Domain.ifFlag
  exact relCT_chain prep wpPrep wpPrep (relCT_chain imports wpImport wpImport
    (relCT_chain range wpRange wpRange (relCT_chain tests wpTest wpTest branches)))

theorem head_ct (backend : MontBackend) {p : Inputs} {slots : List Nat}
    (stable : stableSlots slots = true) (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h28 : 28 ∈ slots)
    (h32 : 32 ∈ slots) :
    RelCT isa (fun s t => (Context p slots s ∧ DomainCallMemory p s) ∧
      (Context p slots t ∧ DomainCallMemory p t) ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.Domain.head (VG.Impl.Ffdh.Arm.SharedCheckDomain.main (mop backend)))
      (fun _ _ => True) := by
  let Q := fun s : State => (Context p (60 :: 56 :: slots) s ∧ DomainCallMemory p s) ∧
    s.z = Spec.Rsa.modulusValid p.P p.k
  have head := (VG.Proof.Ffdh.Arm.head_ct stable h0 h24 h32).mono
    (P' := fun (s t : State) => (Context p slots s ∧ DomainCallMemory p s) ∧
      (Context p slots t ∧ DomainCallMemory p t) ∧ s.sp = t.sp)
    (fun _ _ h => ⟨h.1.1, h.2.1.1, h.2.2⟩) (fun _ _ h => h)
  have wp (s : State) (h : Context p slots s ∧ DomainCallMemory p s) :
      WP isa (.seq (.block (VG.Impl.Ffdh.Arm.Domain.prepareArgs 24 ++ VG.Impl.Ffdh.Arm.Domain.domainPointers))
        (.block VG.Impl.Bignum.Arm.modulusCheck)) s Q :=
    WP.mono (VG.Proof.Ffdh.Arm.head_ok s h.1 stable h0 h24 h32) fun _ j => ⟨⟨j.1, h.2.after j.2.2.2⟩, j.2.1⟩
  have stable' : stableSlots (60 :: 56 :: slots) = true := by
    change (true && (true && stableSlots slots)) = true
    rw [Bool.true_and, Bool.true_and, stable]
  have gInput (s : State) (h : Context p (60 :: 56 :: slots) s ∧ DomainCallMemory p s) :
      MainInput p (60 :: 56 :: slots) ((p.dom.drop p.k).take p.k) s := by
    refine ⟨h.1, h.1.gBytes, ?_, ?_, h.2⟩
    · rw [p.gLength]
      exact h.1.toArgumentMemory.domainSliceStack (by have := p.minLength; omega_using [this])
        (by rw [p.domainLength]; split <;> omega_using [])
    · rw [p.gLength]
      exact h.2.domainSlice h.1 (by have := p.minLength; omega_using [this])
        (by rw [p.domainLength]; split <;> omega_using [])
  have branches : RelCT isa (fun s t => Q s ∧ Q t ∧ s.sp = t.sp)
      (.ite .eq (VG.Impl.Ffdh.Arm.SharedCheckDomain.main (mop backend)) (VG.Impl.Ffdh.Arm.Domain.ret 0))
      (fun _ _ => True) := by
    apply iteKnown_ct (Spec.Rsa.modulusValid p.P p.k) (fun s h => by change some s.z = _; rw [h.2])
    · intro valid
      have facts := VG.Proof.Bignum.valid_facts valid p.minLength
      exact (main_ct backend stable' (by simp [h0]) (by simp [h24]) (by simp [h28])
        (by simp [h32]) (by simp) (by simp) facts.2.1 facts.1).mono
        (fun s t h => ⟨gInput s h.1.1, gInput t h.2.1.1, h.2.2⟩) (fun _ _ h => h)
    · intro _
      exact (ret_ct 0).mono (fun _ _ _ => trivial) (fun _ _ h => h)
  unfold VG.Impl.Ffdh.Arm.Domain.head
  apply RelCT.assoc
  exact relCT_chain head wp wp branches

theorem body_ct (backend : MontBackend) {p : Inputs} {slots : List Nat}
    (stable : stableSlots slots = true) (h0 : 0 ∈ slots)
    (h24 : 24 ∈ slots) (h28 : 28 ∈ slots) (h32 : 32 ∈ slots) :
    RelCT isa (fun s t =>
      ((Context p slots s ∧ DomainCallMemory p s) ∧ VettedGroups.TableAt (s.syms tableSym) groups s) ∧
      ((Context p slots t ∧ DomainCallMemory p t) ∧ VettedGroups.TableAt (t.syms tableSym) groups t) ∧
      s.sp = t.sp ∧ s.syms tableSym = t.syms tableSym)
      (VG.Impl.Ffdh.Arm.SharedCheckDomain.body (mop backend)) (fun _ _ => True) := by
  let Q := fun s : State => (Context p slots s ∧ DomainCallMemory p s) ∧
    s.gpr .r11 = BitVec.ofNat 32 (recognize groups p.k p.dom)
  let R := fun s : State => (Context p slots s ∧ DomainCallMemory p s) ∧
    s.z = (BitVec.ofNat 32 (recognize groups p.k p.dom) == 0)
  have scan (s : State) (h : (Context p slots s ∧ DomainCallMemory p s) ∧
      VettedGroups.TableAt (s.syms tableSym) groups s) :
      WP isa VG.Impl.Ffdh.Arm.VettedGroups.code s Q :=
    WP.mono (VettedGroups.code_ok s h.1.1 h24 h28 h32 h.2) fun _ out =>
      ⟨⟨out.1, h.1.2.after out.2.2.2⟩, out.2.1⟩
  have recognition := (VettedGroups.recognition_ct (p := p) (slots := slots) h24 h28 h32).mono
    (P' := fun (s t : State) =>
      ((Context p slots s ∧ DomainCallMemory p s) ∧ VettedGroups.TableAt (s.syms tableSym) groups s) ∧
      ((Context p slots t ∧ DomainCallMemory p t) ∧ VettedGroups.TableAt (t.syms tableSym) groups t) ∧
      s.sp = t.sp ∧ s.syms tableSym = t.syms tableSym)
    (fun _ _ h => ⟨⟨h.1.1.1, h.1.2⟩, ⟨h.2.1.1.1, h.2.1.2⟩, h.2.2.1, h.2.2.2⟩) (fun _ _ h => h)
  have stage := (relCT_keep_sp recognition (fun _ _ h => h.2.2.1)).wp
    (fun s t h => ⟨scan s h.1, scan t h.2.1⟩)
  have test (s : State) (h : Q s) : WP isa VG.Impl.Ffdh.Arm.Domain.testFlag s R := by
    refine WP.mono (testFlag_ok s) ?_
    rintro t ⟨⟨zero, mem⟩, rest⟩
    exact ⟨⟨h.1.1.of_mem mem rest ((rest.gpr .r0 (by simp)).trans h.1.1.ptr), h.1.2.after rest⟩,
      by rw [zero, h.2]⟩
  have branches : RelCT isa (fun s t => R s ∧ R t ∧ s.sp = t.sp)
      (.ite .ne (VG.Impl.Ffdh.Arm.Domain.ret 1)
        (VG.Impl.Ffdh.Arm.Domain.head (VG.Impl.Ffdh.Arm.SharedCheckDomain.main (mop backend))))
      (fun _ _ => True) := by
    apply iteKnown_ct (!(BitVec.ofNat 32 (recognize groups p.k p.dom) == 0))
      (fun s h => by change some (!s.z) = _; rw [h.2])
    · intro _
      exact (ret_ct 1).mono (fun _ _ _ => trivial) (fun _ _ h => h)
    · intro _
      exact (head_ct backend stable h0 h24 h28 h32).mono
        (fun _ _ h => ⟨h.1.1, h.2.1.1, h.2.2⟩) (fun _ _ h => h)
  have tail := relCT_chain (testFlag_ct.mono (P' := fun (s t : State) => Q s ∧ Q t ∧ s.sp = t.sp)
    (fun _ _ _ => trivial) (fun _ _ h => h)) test test branches
  unfold VG.Impl.Ffdh.Arm.SharedCheckDomain.body
  exact stage.seq (tail.mono (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩) (fun _ _ h => h))

theorem fn_ct (backend : MontBackend) {p : Inputs} :
    RelCT isa (fun s t => Input p s ∧ Input p t ∧ s.sp = t.sp ∧
      s.syms tableSym = t.syms tableSym)
      (VG.Impl.Ffdh.Arm.SharedCheckDomain.code (mop backend)) (fun _ _ => True) := by
  let P := fun a : State => ∃ s, Input p s ∧ a = entered s
  let Q := fun a : State => (Context p [0, 32, 28, 24] a ∧ DomainCallMemory p a) ∧
    VettedGroups.TableAt (a.syms tableSym) groups a
  have wp (a : State) (h : P a) :
      WP isa (.block VG.Impl.Ffdh.Arm.Domain.CheckDomain.entry) a Q := by
    obtain ⟨s, input, rfl⟩ := h
    refine WP.mono_syms (withAllRest (domainEntry_ok (entered s) input.args
      input.domain input.domainLength input.count input.scratch)) ?_
    rintro u ⟨⟨context, frame⟩, rest⟩ syms
    have table := input.table.after_frame input.safe frame rest
    rw [← syms] at table
    exact ⟨⟨context, input.calls.after rest⟩, table⟩
  have entry : RelCT isa (fun s t => P s ∧ P t ∧ s.sp = t.sp ∧
      s.syms tableSym = t.syms tableSym)
      (.block VG.Impl.Ffdh.Arm.Domain.CheckDomain.entry)
      (fun s t => Q s ∧ Q t ∧ s.sp = t.sp ∧ s.syms tableSym = t.syms tableSym) := by
    intro s t tr1 tr2 u v h e1 e2
    have timing := domainEntry_ct s t tr1 tr2 u v h.2.2.1 e1 e2
    obtain ⟨_, u', eu, hu⟩ := wp s h.1
    obtain ⟨_, v', ev, hv⟩ := wp t h.2.1
    obtain ⟨_, rfl⟩ := Exec.det e1 eu
    obtain ⟨_, rfl⟩ := Exec.det e2 ev
    exact ⟨timing.1, hu, hv, by rw [(Exec.rdwr eu).2.2, (Exec.rdwr ev).2.2]; exact h.2.2.1,
      by rw [Exec.syms eu, Exec.syms ev]; exact h.2.2.2⟩
  have body := entry.seq (body_ct backend (by decide) (by decide) (by decide) (by decide) (by decide))
  unfold VG.Impl.Ffdh.Arm.SharedCheckDomain.code
  apply framed_ct (fun _ _ h => ⟨h.1.stackFits, h.2.1.stackFits⟩) (fun _ _ h => h.2.2.1)
  intro a b tr1 tr2 u v h e1 e2
  obtain ⟨s, t, related, rfl, rfl⟩ := h
  exact body _ _ _ _ _ _ ⟨⟨s, related.1, rfl⟩, ⟨t, related.2.1, rfl⟩,
    by rw [entered_sp, entered_sp, related.2.2.1], related.2.2.2⟩ e1 e2

theorem constantTime (backend : MontBackend) :
    ConstantTime isa contract.pre contract.pub (code backend) := by
  intro s t tr1 tr2 u v hs ht hp e1 e2
  obtain ⟨p, base, domain, publicValue, count, capacity, domainBytes, inputS⟩ := data s hs
  have relation : (Spec.Ffdh.checkDomainContract abi 176).pub s t ∧
      ∀ c ∈ tableConsts, symAddr s c.1 = symAddr t c.1 := pub_consts.mp hp
  have symbols := VettedGroups.consts_singleton_symEq relation.2
  have pubBase := relation.1
  sig_pub [Spec.Ffdh.checkDomainContract, Spec.Ffdh.checkDomainSig, abi, argRegs,
    reduceClassify, Loc.val, State.addr] at pubBase
  obtain ⟨sp, bytes, p0, p1, p2, p3, p4⟩ := pubBase
  have byteEq := congrArg (List.map (BitVec.ofNat 8)) bytes
  simp only [List.map_map, Function.comp_def, BitVec.ofNat_toNat,
    BitVec.setWidth_eq, List.map_id'] at byteEq
  rw [← p0, ← p1] at byteEq
  have inputT := input t ht (p := p)
    (p3.symm.trans base) (p0.symm.trans domain) publicValue
    (by change (t.gpr .r2).toNat = p.k; rw [← p2]; exact count)
    (by change (stackArg t 0).toNat = p.len; rw [← p4]; exact capacity) ?_
  · exact (fn_ct backend s t tr1 tr2 u v ⟨inputS, inputT, sp, symbols⟩ e1 e2).1
  · change Spec.Rsa.bytesAt t.mem (State.addr p.domain) (t.gpr .r1).toNat = p.dom
    rw [← p1, ← domain]
    change Spec.Rsa.bytesAt t.mem (BitVec.setWidth 64 (s.gpr .r0)) (s.gpr .r1).toNat = p.dom
    rw [← byteEq, domain]
    exact domainBytes

/-! ## Satisfiable, and verified -/

private def attemptBase : State where
  gpr r := match r with | .r0 => 0x1000 | .r1 => 128 | .r2 => 64 | .r3 => 0x3000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x8000 then 0x20 else if a = 0x8001 then 4 else 0
  rd := [⟨0x1000, 128⟩, ⟨0x8000, 4⟩]
  wr := [⟨0x3000, 8448⟩]

@[irreducible] private def attemptMem (W : List (BitVec 64)) : Mem := fun a =>
  if (a - 0x100000).toNat < 17744 then constMem 0x100000 W a else attemptBase.mem a

private def attemptSat (W : List (BitVec 64)) : State :=
  { attemptBase with
    mem := attemptMem W
    rd := attemptBase.rd ++ [⟨0x100000, 17744⟩]
    syms := fun _ => 0x100000 }

private theorem attemptMem_held (W : List (BitVec 64)) (length : W.length = 2218) (i : Nat) (hi : i < W.length) :
    (attemptMem W).readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = W.getD i 0 := by
  rw [← constMem_held 0x100000 W (by rw [length]; decide) i hi]
  apply Mem.readW_congr
  intro j hj
  unfold attemptMem
  refine ite_eq_left ?_
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
  rw [length] at hi
  omega_using [hi, hj]

private theorem attemptSat_arg (W : List (BitVec 64)) {i : Nat} (hi : i < 1) :
    stackArg (attemptSat W) i = stackArg attemptBase i := by
  apply Mem.readW_congr
  intro j hj
  change attemptMem W _ = attemptBase.mem _
  unfold attemptMem
  apply ite_eq_right
  have small : ∀ i < 1, ∀ j < 4,
      ¬ (stackArgAddr attemptBase i + BitVec.ofNat 64 j - 0x100000).toNat < 17744 := by decide
  exact small i hi j hj

private theorem satAux (W : List (BitVec 64)) (length : W.length = 2218) :
    ∃ s, (Spec.Ffdh.checkDomainContract (abi.withConsts [(tableSym, W)]) 176).pre s := by
  refine ⟨attemptSat W, pre_consts.mpr ⟨?_, ?_⟩⟩
  · have args (i : Nat) (hi : i < 1) := attemptSat_arg W hi
    sig_pre [Spec.Ffdh.checkDomainContract, Spec.Ffdh.checkDomainSig, Spec.Ffdh.pLenValid, Spec.Ffdh.domainLenValid, Spec.Rsa.scratchWords, abi,
      argRegs, reduceClassify, Loc.val, State.addr]
    simp only [show ∀ (K : List (String × List (BitVec 64))) (s : State) (i : Nat), stackArg (stripConsts K s) i = stackArg s i by intros; rfl]
    simp only [args 0 (by decide)]
    dsimp only [stackArgAddr, stripConsts, State.withRegions, attemptSat, attemptBase]
    repeat' apply And.intro
    all_goals first | rfl | decide | (apply Region.disjoint_of_sep; decide)
  · refine ⟨?_, ?_, ?_, fun r hr => by
      simp only [constRegs, Abi.constRegions, List.mem_map, List.mem_singleton] at hr
      obtain ⟨c, rfl, rfl⟩ := hr
      dsimp only [symAddr, attemptSat]
      decide⟩
    · simp only [attemptSat, attemptBase, constRegs, Abi.constRegions, symAddr, List.map_cons, List.map_nil, length]
      rfl
    · intro c hc i hi
      simp only [List.mem_singleton] at hc
      subst c
      exact attemptMem_held W length i hi
    · intro r hr
      simp only [constRegs, Abi.constRegions, List.mem_map, List.mem_singleton] at hr
      obtain ⟨c, rfl, rfl⟩ := hr
      rw [length]
      dsimp only [symAddr, attemptSat]
      refine ⟨by decide, ?_, ?_⟩
      · intro q hq
        change q ∈ ([⟨0x3000, 8448⟩] : List Region) at hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl
        all_goals first | contradiction | (apply Region.disjoint_of_sep; decide)
      · intro q hq
        simp only [abi, stackBelow, List.mem_singleton] at hq
        subst q
        exact Region.disjoint_of_sep (by decide)

theorem sat : ∃ s, contract.pre s :=
  satAux tableWords VettedGroups.tableWords_length

theorem verified (backend : MontBackend) : Verified target (code backend) contract :=
  ⟨correct backend, constantTime backend, sat⟩

/-- The code with the product's rewriting of its callers. -/
def calledCode (b : MontBackend) : Prog isa := b.caller.code (code b)

theorem called_verified (b : MontBackend) : Verified target (calledCode b) contract :=
  b.caller.verified (verified b)

end VG.Proof.Ffdh.Arm.SharedCheckDomain
