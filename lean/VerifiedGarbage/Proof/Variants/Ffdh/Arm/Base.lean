module

public import VerifiedGarbage.Proof.Ffdh.Arm.Backend
public import VerifiedGarbage.Proof.Ffdh.Arm.VettedValidation.Fn
public import VerifiedGarbage.Proof.Framework.Arm.StackScratchConsts
public import VerifiedGarbage.Spec.Ffdh.Contract
import VerifiedGarbage.Proof.Ffdh.Arm.DomainPre
import VerifiedGarbage.Proof.Ffdh.Arm.DomainSpec
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Ffdh.Arm.DomainFn
public import VerifiedGarbage.Proof.Ffdh.Arm.Context
public import VerifiedGarbage.Impl.Ffdh.Arm.Domain
import VerifiedGarbage.Proof.Ffdh.Arm.Entered
import VerifiedGarbage.Proof.Ffdh.Arm.VettedGroupsConsts
import VerifiedGarbage.Proof.Ffdh.Arm.VettedGroupsBytes
import VerifiedGarbage.Proof.Bignum.Arm.PcDimensions
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Ffdh.Arm.VettedValidation.Sat
import VerifiedGarbage.Proof.Ffdh.Arm.VettedValidation.RecognitionTiming
import VerifiedGarbage.Impl.Ffdh.Arm.VettedValidation
import VerifiedGarbage.Proof.Ffdh.Arm.VettedGroups
public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Ffdh.Arm.Head
import VerifiedGarbage.Proof.Ffdh.Arm.DomainBody
import VerifiedGarbage.Proof.Ffdh.Arm.HeadCT
import VerifiedGarbage.Proof.Ffdh.Arm.BranchCT
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Ffdh.Arm.ImportAt
import VerifiedGarbage.Proof.Ffdh.Arm.ImportAtCT
import VerifiedGarbage.Proof.Ffdh.Arm.RangeCT
import VerifiedGarbage.Proof.Ffdh.Arm.OddCT
import VerifiedGarbage.Proof.Ffdh.Arm.Odd
import VerifiedGarbage.Proof.Ffdh.Arm.CheckFlag
import VerifiedGarbage.Proof.Ffdh.Arm.EqualCT
import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
import VerifiedGarbage.Proof.Ffdh.Arm.PrepareAtCT
import VerifiedGarbage.Proof.Ffdh.Arm.ValueChecksCT
import VerifiedGarbage.Proof.Bignum.Arm.ReduceOperandCT
import VerifiedGarbage.Proof.Bignum.Arm.ReduceOperand
import VerifiedGarbage.Proof.Bignum.Arm.SmallConstCT
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Ffdh.Arm.SubgroupCT
import VerifiedGarbage.Proof.Ffdh.Arm.FlagCT
import VerifiedGarbage.Proof.Ffdh.Arm.QTest
import VerifiedGarbage.Proof.Ffdh.Arm.Range
import VerifiedGarbage.Proof.Ffdh.Arm.Branch
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Ffdh.Arm.SampleEnvironment
import VerifiedGarbage.Proof.Ffdh.Arm.VettedGroupsState
import VerifiedGarbage.Proof.Ffdh.Arm.DomainEntryCT
import VerifiedGarbage.Proof.Ffdh.Arm.FrameCT
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Syms
public import VerifiedGarbage.Proof.Ffdh.Arm.CheckPublicVerified
public import VerifiedGarbage.Proof.Ffdh.Arm.PrivateVerified
public import VerifiedGarbage.Proof.Ffdh.Arm.ExchangeVerified

/-! ### `Ffdh.Arm.VettedValidation.Verified`, which only this module used -/

section

/-! ### `Ffdh.Arm.VettedValidation.Input`, which only this module used -/

section

/-! ### `Ffdh.Arm.DomainCorrect`, which only this module used -/

section

/-! The callable domain check implements the shared FFDH parameter contract. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem domain_data (s : State) (pre : (Spec.Ffdh.checkDomainContract abi 128).pre s) :
    ∃ p : Inputs, s.gpr .r3 = p.base ∧ s.gpr .r0 = p.domain ∧
      (s.gpr .r2).toNat = p.k ∧ (stackArg s 0).toNat = p.len ∧
      Spec.Rsa.bytesAt s.mem (State.addr p.domain) (s.gpr .r1).toNat = p.dom ∧ DomainFnInput p s := by
  have original := pre
  sig_pre [Spec.Ffdh.checkDomainContract, Spec.Ffdh.checkDomainSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at pre
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, bounds, domainLen, space⟩ := pre
  let dom := Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat
  have domLength : dom.length = (s.gpr .r1).toNat := VG.Proof.Bignum.bytesAt_length _ _ _
  let p : Inputs := {
    base := s.gpr .r3
    domain := s.gpr .r0
    publicValue := 0
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
  exact ⟨p, rfl, rfl, rfl, rfl, rfl, domain_input s original rfl rfl rfl rfl rfl⟩

end VG.Proof.Ffdh.Arm

end

end


/-! The existing parameter signature supplies the original frame and read-only table. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.VettedValidation
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Impl.Ffdh.Arm.VettedGroups

def contract := Spec.Ffdh.checkDomainContract (abi.withConsts tableConsts) 128

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

theorem table_input {s : State} (hc : ConstsOk tableConsts 128 s)
    {p : Inputs} (input : DomainFnInput p s) :
    VettedGroups.TableAt ((entered s).syms tableSym) groups (entered s) ∧
    VettedGroups.TableSafe ((entered s).syms tableSym) groups
      [⟨State.addr (entered s).sp, 72⟩] := by
  have geometry := VettedGroups.consts_singleton_regions (name := tableSym) (words := tableWords) hc
  have fit := hc.fit (name := tableSym) (ws := tableWords) List.mem_cons_self
  rw [VettedGroups.tableWords_length] at geometry fit
  have span : tableBytes.length = 8 * 2218 := VettedGroups.tableBytes_length
  have reserved : (⟨State.addr (s.syms tableSym), tableBytes.length⟩ : Region).Disjoint
      (FrameStack.belowA s.sp 128) := by
    rw [span]
    apply geometry.2.2
    rw [FrameStack.belowA, FrameStack.addr_sub' input.stackFits]
    simp only [abi, stackBelow]
    exact List.mem_cons_self
  have bytes : Spec.Rsa.bytesAt (entered s).mem
      (State.addr ((entered s).syms tableSym)) tableBytes.length = tableBytes := by
    rw [VG.Proof.Bignum.Arm.rsa_bytes_frame (entered_frame s input.stackFits)
      (by rw [span]; omega_using []) (by
        intro r hr
        obtain rfl := List.mem_singleton.mp hr
        exact reserved.sub_right (saved_sub_reserved s input.stackFits))]
    exact VettedGroups.consts_table_bytes hc
  apply VettedGroups.tableOfBytes (entered s) ((entered s).syms tableSym) groups
    (by change ((entered s).syms tableSym).toNat + tableBytes.length ≤ 2 ^ 32; rw [span]; exact fit) (entered_read (VettedGroups.consts_table_read hc)) bytes
  · intro g hg
    simp only [groups, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact reserved.sub_right (locals_sub_reserved s input.stackFits)

theorem data (s : State) (pre : contract.pre s) :
    ∃ p : Inputs, s.gpr .r3 = p.base ∧ s.gpr .r0 = p.domain ∧
      (s.gpr .r2).toNat = p.k ∧ (stackArg s 0).toNat = p.len ∧
      Spec.Rsa.bytesAt s.mem (State.addr p.domain) (s.gpr .r1).toNat = p.dom ∧ Input p s := by
  have base : (Spec.Ffdh.checkDomainContract abi 128).pre (stripConsts tableConsts s) ∧
      ConstsOk tableConsts 128 s := pre_consts.mp pre
  obtain ⟨p, scratch, domain, count, capacity, bytes, input⟩ := domain_data
    (stripConsts tableConsts s) base.1
  have wide := input_widen input
  have table := table_input base.2 wide
  exact ⟨p, scratch, domain, count, capacity, bytes, wide, table.1, table.2⟩

end VG.Proof.Ffdh.Arm.VettedValidation

end

end

/-! ### `Ffdh.Arm.DomainBodyCT`, which only this module used -/

section

/-! The complete domain-validation body's trace depends only on the public domain. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/DomainQRangeCT.lean`, which only this module imported.
section

/-! The order's range and parity checks use fixed public addresses. -/

section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (Operand)

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

end VG.Proof.Ffdh.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/DomainDividesCT.lean`, which only this module imported.
section

/-! Divisibility checking reuses RSA's constant-time full-width reduction. -/

section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (numAt Operand arrAt)

structure DividesPrepared (p : Inputs) (slots : List Nat) (s : State) : Prop where
  context : Context p slots s
  ready : ArithmeticReady p.base p.len p.w s
  modulus : numAt s.mem (State.addr p.base) p.w 0 = p.Q
  r2 : numAt s.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % p.Q

structure DividesOne (p : Inputs) (s : State) : Prop where
  ready : ArithmeticReady p.base p.len p.w s
  modulus : numAt s.mem (State.addr p.base) p.w 0 = p.Q
  r2 : numAt s.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % p.Q
  one : numAt s.mem (State.addr p.base) p.w 7 = 1

theorem domainDivides_ct {p : Inputs} {slots : List Nat}
    (stable : stableSlots slots = true) (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h32 : 32 ∈ slots) (h60 : 60 ∈ slots)
    (hasQ : p.hasQ = true) (large : 1 < p.Q) (odd : p.Q % 2 = 1) :
    RelCT isa (fun s t => Context p slots s ∧ Context p slots t ∧ s.sp = t.sp)
      VG.Impl.Ffdh.Arm.Domain.CheckDomain.divides (fun _ _ => True) := by
  have op0 : Operand 0 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op1 : Operand 1 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op4 : Operand 4 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have qStack (s : State) (h : Context p slots s) :
      Region.Disjoint ⟨State.addr p.q, p.k⟩ ⟨State.addr s.sp, 72⟩ :=
    h.toArgumentMemory.domainSliceStack (by have := p.minLength; omega)
      (by rw [p.domainLength, hasQ]; simp only [ite_true]; omega)
  have prepare := (prepareAt_ct (p := p) (slot := 60) stable h60 h32 h0 (p.qLength hasQ) large odd).mono
    (P' := fun (s t : State) => Context p slots s ∧ Context p slots t ∧ s.sp = t.sp)
    (fun s t h => ⟨⟨h.1, h.1.qBytes hasQ, qStack s h.1⟩,
      ⟨h.2.1, h.2.1.qBytes hasQ, qStack t h.2.1⟩, h.2.2⟩) (fun _ _ h => h)
  have wpPrep (s : State) (h : Context p slots s) :
      WP isa (VG.Impl.Ffdh.Arm.Domain.prepareAt 60) s (DividesPrepared p slots) :=
    WP.mono (prepareAt_ok s 60 h stable h60 h32 h0 (h.qBytes hasQ) (p.qLength hasQ) (qStack s h) large odd)
      fun _ j => ⟨j.1, j.2.1, j.2.2.1, j.2.2.2.1⟩
  have imported := (importAt_ct (p := p) (a := 1) (slot := 24) (k := p.k)
    stable h24 h32 rfl (by decide)).mono
    (P' := fun (s t : State) => DividesPrepared p slots s ∧ DividesPrepared p slots t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨⟨h.1.context, h.1.ready⟩, ⟨h.2.1.context, h.2.1.ready⟩, h.2.2⟩) (fun _ _ h => h)
  have wpImport (s : State) (h : DividesPrepared p slots s) :
      WP isa (VG.Impl.Ffdh.Arm.Domain.importAt 1 24 32) s (DividesPrepared p slots) := by
    refine WP.mono (importAt_ok s 1 24 32 h.context stable h24 h32 h.ready (by decide) (by decide) h.context.pBytes
      (by rw [p.pLength]; have := p.minLength; omega) (by rw [p.pLength]; exact p.width.2.2.2.1)
      (by change BitVec.ofNat 32 p.k = _; rw [p.pLength])) ?_
    rintro u ⟨context, ready, _, keeps, _, _⟩
    have fits : arrAt p.w 8 ≤ 8 * p.len := ready.width ▸ ready.layout.2.2.1
    exact ⟨context, ready, (keeps_array_num keeps fits op0 (by decide)).trans h.modulus,
      (keeps_array_num keeps fits op4 (by decide)).trans h.r2⟩
  have one := (smallConst_ct (base := p.base) (len := p.len) (w := p.w) 1
    (by decide : 7 < 8) (by decide) (by decide)).mono
    (P' := fun (s t : State) => DividesPrepared p slots s ∧ DividesPrepared p slots t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨h.1.ready, h.2.1.ready, h.2.2⟩) (fun _ _ h => h)
  have wpOne (s : State) (h : DividesPrepared p slots s) :
      WP isa (VG.Impl.Bignum.Arm.smallConst 7 1) s (DividesOne p) := by
    refine WP.mono (smallConst_ok s 1 h.ready (by decide : 7 < 8) (by decide) (by decide) (by decide)) ?_
    rintro u ⟨ready, one, _, keeps, _, _⟩
    have fits : arrAt p.w 8 ≤ 8 * p.len := ready.width ▸ ready.layout.2.2.1
    exact ⟨ready, (keeps_array_num keeps fits op0 (by decide)).trans h.modulus,
      (keeps_array_num keeps fits op4 (by decide)).trans h.r2, one⟩
  have tableFit : arrAt p.w 3 + 32 ≤ 8 * p.len := by
    have := p.width.2.2.1; simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at *; omega
  have reduce := (reduceOperand_ct (o := 1) op1 (by decide) (by decide) tableFit).mono
    (P' := fun (s t : State) => DividesOne p s ∧ DividesOne p t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨⟨h.1.ready, by rw [h.1.r2, h.1.modulus]; exact Nat.mod_lt _ (by omega),
      by rw [h.1.one, h.1.modulus]; exact large⟩,
      ⟨h.2.1.ready, by rw [h.2.1.r2, h.2.1.modulus]; exact Nat.mod_lt _ (by omega),
      by rw [h.2.1.one, h.2.1.modulus]; exact large⟩, h.2.2⟩) (fun _ _ h => h)
  have wpReduce (s : State) (h : DividesOne p s) :=
    WP.mono (reduceOperand_ok s h.ready op1 (by decide) (by decide) h.modulus odd h.r2 h.one) fun _ j => j.1
  unfold VG.Impl.Ffdh.Arm.Domain.CheckDomain.divides
  exact relCT_chain prepare wpPrep wpPrep (relCT_chain imported wpImport wpImport
    (relCT_chain one wpOne wpOne (relCT_chain reduce wpReduce wpReduce (isOne_ct op1))))

end VG.Proof.Ffdh.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/DomainQChecksCT.lean`, which only this module imported.
section

/-! Order validation branches only on the documented public domain values. -/

section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

structure DomainFlagged (p : Inputs) (slots : List Nat) (flag : BitVec 32) (s : State) : Prop where
  context : Context p slots s
  result : s.gpr .r11 = flag

theorem DomainFlagged.after_mem {p : Inputs} {slots : List Nat} {flag : BitVec 32} {s t : State}
    (h : DomainFlagged p slots flag s) (mem : t.mem = s.mem) (rest : VG.Proof.X25519.Arm.Rest [] s t) :
    DomainFlagged p slots flag t :=
  ⟨h.context.of_mem mem rest ((rest.gpr .r0 (by simp)).trans h.context.ptr),
    (rest.gpr .r11 (by simp)).trans h.result⟩

theorem domainGenerator_ct {p : Inputs} {slots : List Nat}
    (stable : stableSlots slots = true) (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h32 : 32 ∈ slots)
    (h56 : 56 ∈ slots) (h60 : 60 ∈ slots) (hasQ : p.hasQ = true) (large : 1 < p.P) (odd : p.P % 2 = 1) :
    RelCT isa (fun s t => Context p slots s ∧ Context p slots t ∧ s.sp = t.sp)
      (.seq (VG.Impl.Ffdh.Arm.Domain.prepareAt 24)
        (.seq (VG.Impl.Ffdh.Arm.Domain.subgroup 56) VG.Impl.Ffdh.Arm.Domain.finishFlag)) (fun _ _ => True) := by
  have pStack (s : State) (h : Context p slots s) :
      Region.Disjoint ⟨State.addr p.domain, p.k⟩ ⟨State.addr s.sp, 72⟩ :=
    h.domainStack.sub_left (Region.sub_prefix (by rw [p.domainLength]; split <;> omega))
  have prepare := (prepareAt_ct (p := p) (slot := 24) stable h24 h32 h0 p.pLength large odd).mono
    (P' := fun (s t : State) => Context p slots s ∧ Context p slots t ∧ s.sp = t.sp)
    (fun s t h => ⟨⟨h.1, h.1.pBytes, pStack s h.1⟩,
      ⟨h.2.1, h.2.1.pBytes, pStack t h.2.1⟩, h.2.2⟩) (fun _ _ h => h)
  have wp (s : State) (h : Context p slots s) :
      WP isa (VG.Impl.Ffdh.Arm.Domain.prepareAt 24) s
        (SubgroupInput p slots 56 ((p.dom.drop p.k).take p.k)) := by
    refine WP.mono (prepareAt_ok s 24 h stable h24 h32 h0 h.pBytes p.pLength (pStack s h) large odd) ?_
    rintro u ⟨context, ready, modulus, r2, _⟩
    exact ⟨context, ready, modulus, r2, context.gBytes⟩
  exact relCT_chain prepare wp wp ((subgroup_ct stable h56 h60 h32 hasQ p.gLength odd).seq finishFlag_ct)

theorem domainDividesThen_ct {p : Inputs} {slots : List Nat}
    (stable : stableSlots slots = true) (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h32 : 32 ∈ slots)
    (h56 : 56 ∈ slots) (h60 : 60 ∈ slots) (hasQ : p.hasQ = true)
    (large : 1 < p.P) (odd : p.P % 2 = 1) (qLarge : 1 < p.Q) (qOdd : p.Q % 2 = 1) :
    RelCT isa (fun s t => Context p slots s ∧ Context p slots t ∧ s.sp = t.sp)
      (.seq VG.Impl.Ffdh.Arm.Domain.CheckDomain.divides (VG.Impl.Ffdh.Arm.Domain.ifFlag
        (.seq (VG.Impl.Ffdh.Arm.Domain.prepareAt 24)
          (.seq (VG.Impl.Ffdh.Arm.Domain.subgroup 56) VG.Impl.Ffdh.Arm.Domain.finishFlag))
        (VG.Impl.Ffdh.Arm.Domain.ret 0))) (fun _ _ => True) := by
  let P := DomainFlagged p slots (if p.P % p.Q = 1 then 1 else 0)
  have wp (s : State) (h : Context p slots s) :
      WP isa VG.Impl.Ffdh.Arm.Domain.CheckDomain.divides s P :=
    WP.mono (domainDivides_ok s h stable h0 h24 h32 h60 hasQ qLarge qOdd) fun _ j => ⟨j.1, j.2.1⟩
  have branches : RelCT isa (fun s t => P s ∧ P t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.Domain.ifFlag
        (.seq (VG.Impl.Ffdh.Arm.Domain.prepareAt 24)
          (.seq (VG.Impl.Ffdh.Arm.Domain.subgroup 56) VG.Impl.Ffdh.Arm.Domain.finishFlag))
        (VG.Impl.Ffdh.Arm.Domain.ret 0)) (fun _ _ => True) := by
    apply ifFlag_known_ct (decide (p.P % p.Q = 1))
      (fun _ h => by simpa only [decide_eq_true_eq] using h.result)
      (fun _ _ h mem rest => h.after_mem mem rest)
    · intro _
      exact (domainGenerator_ct stable h0 h24 h32 h56 h60 hasQ large odd).mono
        (fun _ _ h => ⟨h.1.context, h.2.1.context, h.2.2⟩) (fun _ _ h => h)
    · intro _
      exact (ret_ct 0).mono (fun _ _ _ => trivial) (fun _ _ h => h)
  exact relCT_chain (domainDivides_ct stable h0 h24 h32 h60 hasQ qLarge qOdd) wp wp branches

theorem domainQChecks_ct {p : Inputs} {slots : List Nat}
    (stable : stableSlots slots = true) (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h32 : 32 ∈ slots)
    (h56 : 56 ∈ slots) (h60 : 60 ∈ slots) (hasQ : p.hasQ = true) (large : 1 < p.P) (odd : p.P % 2 = 1) :
    RelCT isa (fun s t => SubgroupInput p slots 56 ((p.dom.drop p.k).take p.k) s ∧
      SubgroupInput p slots 56 ((p.dom.drop p.k).take p.k) t ∧ s.sp = t.sp)
      VG.Impl.Ffdh.Arm.Domain.CheckDomain.qChecks (fun _ _ => True) := by
  let P := SubgroupInput p slots 56 ((p.dom.drop p.k).take p.k)
  let Q := DomainFlagged p slots (qRangeFlag p)
  have ranges := (qRange_ct stable h60 h32 hasQ).mono
    (P' := fun (s t : State) => P s ∧ P t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨⟨h.1.context, h.1.ready⟩, ⟨h.2.1.context, h.2.1.ready⟩, h.2.2⟩) (fun _ _ h => h)
  have wp (s : State) (h : P s) : WP isa VG.Impl.Ffdh.Arm.Domain.CheckDomain.qRange s Q :=
    WP.mono (qRange_ok s h.context stable h60 h32 hasQ h.ready h.modulus odd h.r2) fun _ j => ⟨j.1, j.2.2.1⟩
  have branches : RelCT isa (fun s t => Q s ∧ Q t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.Domain.ifFlag
        (.seq VG.Impl.Ffdh.Arm.Domain.CheckDomain.divides (VG.Impl.Ffdh.Arm.Domain.ifFlag
          (.seq (VG.Impl.Ffdh.Arm.Domain.prepareAt 24)
            (.seq (VG.Impl.Ffdh.Arm.Domain.subgroup 56) VG.Impl.Ffdh.Arm.Domain.finishFlag))
          (VG.Impl.Ffdh.Arm.Domain.ret 0))) (VG.Impl.Ffdh.Arm.Domain.ret 0)) (fun _ _ => True) := by
    apply ifFlag_known_ct (decide (2 < p.Q ∧ p.Q < p.P - 1 ∧ p.Q % 2 = 1))
      (fun _ h => by simpa only [qRangeFlag, decide_eq_true_eq] using h.result)
      (fun _ _ h mem rest => h.after_mem mem rest)
    · intro valid
      have facts := of_decide_eq_true valid
      exact (domainDividesThen_ct stable h0 h24 h32 h56 h60 hasQ large odd (by omega) facts.2.2).mono
        (fun _ _ h => ⟨h.1.context, h.2.1.context, h.2.2⟩) (fun _ _ h => h)
    · intro _
      exact (ret_ct 0).mono (fun _ _ _ => trivial) (fun _ _ h => h)
  unfold VG.Impl.Ffdh.Arm.Domain.CheckDomain.qChecks
  exact relCT_chain ranges wp wp branches

end VG.Proof.Ffdh.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/DomainTailCT.lean`, which only this module imported.
section

/-! Optional order validation branches only on the public domain shape. -/

section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem domainTail_ct {p : Inputs} {slots : List Nat}
    (stable : stableSlots slots = true) (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h28 : 28 ∈ slots) (h32 : 32 ∈ slots)
    (h56 : 56 ∈ slots) (h60 : 60 ∈ slots) (large : 1 < p.P) (odd : p.P % 2 = 1) :
    RelCT isa (fun s t => SubgroupInput p slots 56 ((p.dom.drop p.k).take p.k) s ∧ SubgroupInput p slots 56 ((p.dom.drop p.k).take p.k) t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.Domain.withQ
        VG.Impl.Ffdh.Arm.Domain.CheckDomain.qChecks
        (VG.Impl.Ffdh.Arm.Domain.ret 1)) (fun _ _ => True) := by
  let P := SubgroupInput p slots 56 ((p.dom.drop p.k).take p.k)
  let Q := fun s : State => P s ∧ s.z = !p.hasQ
  have trace := qTest_ct.mono (P' := fun (s t : State) => P s ∧ P t ∧ s.sp = t.sp)
    (fun _ _ h => h.2.2) (fun _ _ _ => trivial)
  have wp (s : State) (h : P s) : WP isa VG.Impl.Ffdh.Arm.Domain.qTest s Q := by
    refine WP.mono (qTest_ok s h.context h28 h32) ?_
    rintro u ⟨⟨zero, mem⟩, rest⟩
    exact ⟨h.after_mem stable mem rest ((rest.gpr .r0 (by simp)).trans h.context.ptr), zero⟩
  have branches : RelCT isa (fun s t => Q s ∧ Q t ∧ s.sp = t.sp)
      (.ite .ne VG.Impl.Ffdh.Arm.Domain.CheckDomain.qChecks
        (VG.Impl.Ffdh.Arm.Domain.ret 1)) (fun _ _ => True) := by
    apply iteKnown_ct p.hasQ (fun s h => by simp only [eval, h.2, Bool.not_not])
    · intro hasQ
      exact (domainQChecks_ct stable h0 h24 h32 h56 h60 hasQ large odd).mono
        (fun _ _ h => ⟨h.1.1, h.2.1.1, h.2.2⟩) (fun _ _ h => h)
    · intro _
      exact (ret_ct 1).mono (fun _ _ _ => trivial) (fun _ _ h => h)
  unfold VG.Impl.Ffdh.Arm.Domain.withQ
  exact relCT_chain trace wp wp branches

end VG.Proof.Ffdh.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/DomainMainCT.lean`, which only this module imported.
section

/-! Generator and order checks branch only on the public domain. -/

section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt Operand arrAt)

structure DomainMainInput (p : Inputs) (slots : List Nat) (yb : List Byte) (s : State) : Prop where
  context : Context p slots s
  value : Octets p.base p.g p.len yb s
  separate : Region.Disjoint ⟨State.addr p.g, yb.length⟩ ⟨State.addr s.sp, 72⟩

structure DomainImported (p : Inputs) (slots : List Nat) (yb : List Byte) (s : State) : Prop extends
    SubgroupInput p slots 56 yb s where
  value : numAt s.mem (State.addr p.base) p.w 1 = Spec.Rsa.os2ip yb

structure DomainRanged (p : Inputs) (slots : List Nat) (yb : List Byte) (s : State) : Prop extends
    SubgroupInput p slots 56 yb s where
  flag : s.gpr .r11 = if 1 < Spec.Rsa.os2ip yb ∧ Spec.Rsa.os2ip yb < p.P - 1 then 1 else 0

theorem domainMain_ct {p : Inputs} {slots : List Nat}
    (stable : stableSlots slots = true) (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h28 : 28 ∈ slots)
    (h32 : 32 ∈ slots) (h56 : 56 ∈ slots) (h60 : 60 ∈ slots)
    (large : 1 < p.P) (odd : p.P % 2 = 1) :
    RelCT isa (fun s t => DomainMainInput p slots ((p.dom.drop p.k).take p.k) s ∧ DomainMainInput p slots ((p.dom.drop p.k).take p.k) t ∧ s.sp = t.sp)
      VG.Impl.Ffdh.Arm.Domain.CheckDomain.main (fun _ _ => True) := by
  let yb := (p.dom.drop p.k).take p.k
  have length : yb.length = p.k := p.gLength
  have op0 : Operand 0 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op1 : Operand 1 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op4 : Operand 4 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have pStack (s : State) (h : DomainMainInput p slots yb s) :
      Region.Disjoint ⟨State.addr p.domain, p.k⟩ ⟨State.addr s.sp, 72⟩ :=
    h.context.domainStack.sub_left (Region.sub_prefix (by rw [p.domainLength]; split <;> omega))
  have prep := (prepareAt_ct (p := p) (slot := 24) stable h24 h32 h0 p.pLength large odd).mono
    (P' := fun (s t : State) => DomainMainInput p slots yb s ∧ DomainMainInput p slots yb t ∧ s.sp = t.sp)
    (fun s t h => ⟨⟨h.1.context, h.1.context.pBytes, pStack s h.1⟩,
      ⟨h.2.1.context, h.2.1.context.pBytes, pStack t h.2.1⟩, h.2.2⟩) (fun _ _ h => h)
  have wpPrep (s : State) (h : DomainMainInput p slots yb s) :
      WP isa (VG.Impl.Ffdh.Arm.Domain.prepareAt 24) s (SubgroupInput p slots 56 yb) := by
    refine WP.mono (prepareAt_ok s 24 h.context stable h24 h32 h0 h.context.pBytes p.pLength (pStack s h) large odd) ?_
    rintro u ⟨context, ready, modulus, r2, frame, rest⟩
    exact ⟨context, ready, modulus, r2, h.value.after_frame frame rest (by
      intro r hr
      simp only [prepareAtWrites, prepareWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h.value.separate
      · exact h.separate.sub_right (Offset.sub_base _ (by decide))
      · exact h.separate.sub_right (Offset.sub_base _ (by decide)))⟩
  have imports := (importAt_ct (p := p) (a := 1) stable h56 h32
    (show p.slotValue 32 = BitVec.ofNat 32 yb.length by change BitVec.ofNat 32 p.k = _; rw [length]) (by decide)).mono
    (P' := fun (s t : State) => SubgroupInput p slots 56 yb s ∧ SubgroupInput p slots 56 yb t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨⟨h.1.context, h.1.ready⟩, ⟨h.2.1.context, h.2.1.ready⟩, h.2.2⟩) (fun _ _ h => h)
  have wpImport (s : State) (h : SubgroupInput p slots 56 yb s) :
      WP isa (VG.Impl.Ffdh.Arm.Domain.importAt 1 56 32) s (DomainImported p slots yb) := by
    refine WP.mono (importAt_ok s 1 56 32 h.context stable h56 h32 h.ready (by decide) (by decide) h.source
      (by rw [length]; have := p.minLength; omega) (by rw [length]; exact p.width.2.2.2.1)
      (by change BitVec.ofNat 32 p.k = _; rw [length])) ?_
    rintro u ⟨context, ready, value, keeps, frame, rest⟩
    have fits : arrAt p.w 8 ≤ 8 * p.len := ready.width ▸ ready.layout.2.2.1
    exact ⟨⟨context, ready, (keeps_array_num keeps fits op0 (by decide)).trans h.modulus,
      (keeps_array_num keeps fits op4 (by decide)).trans h.r2, h.source.after_workspace frame rest⟩, value⟩
  have range := (inRange_ct (base := p.base) (len := p.len) (w := p.w) op1 (by decide)).mono
    (P' := fun (s t : State) => DomainImported p slots yb s ∧ DomainImported p slots yb t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨h.1.ready, h.2.1.ready, h.2.2⟩) (fun _ _ h => h)
  have wpRange (s : State) (h : DomainImported p slots yb s) :
      WP isa (VG.Impl.Ffdh.Arm.inRange 1) s (DomainRanged p slots yb) := by
    refine WP.mono (inRange_ok s h.ready op1 (by decide) (by rw [h.modulus]; exact odd)) ?_
    rintro u ⟨ready, flag, arrays, frame, rest⟩
    rw [h.value, h.modulus] at flag
    exact ⟨h.toSubgroupInput.after_workspace stable frame rest ready
      ((arrays 0 op0 (by decide)).trans h.modulus) ((arrays 4 op4 (by decide)).trans h.r2), flag⟩
  let valid : Prop := 1 < Spec.Rsa.os2ip yb ∧ Spec.Rsa.os2ip yb < p.P - 1
  let Q := fun s : State => SubgroupInput p slots 56 yb s ∧ s.z = !decide valid
  have tests := testFlag_ct.mono
    (P' := fun (s t : State) => DomainRanged p slots yb s ∧ DomainRanged p slots yb t ∧ s.sp = t.sp)
    (fun _ _ _ => trivial) (fun _ _ h => h)
  have wpTest (s : State) (h : DomainRanged p slots yb s) :
      WP isa VG.Impl.Ffdh.Arm.Domain.testFlag s Q := by
    refine WP.mono (testFlag_ok s) ?_
    rintro u ⟨⟨zero, mem⟩, rest⟩
    refine ⟨h.toSubgroupInput.after_mem stable mem rest ((rest.gpr .r0 (by simp)).trans h.context.ptr), ?_⟩
    rw [zero, h.flag]
    change ((if valid then (1#32) else 0#32) == 0#32) = !decide valid
    by_cases hv : valid
    · rw [ite_eq_left hv, decide_eq_true hv]; rfl
    · rw [ite_eq_right hv, decide_eq_false hv]; rfl
  have branches : RelCT isa (fun s t => Q s ∧ Q t ∧ s.sp = t.sp)
      (.ite .ne (VG.Impl.Ffdh.Arm.Domain.withQ
        VG.Impl.Ffdh.Arm.Domain.CheckDomain.qChecks
        (VG.Impl.Ffdh.Arm.Domain.ret 1)) (VG.Impl.Ffdh.Arm.Domain.ret 0)) (fun _ _ => True) := by
    apply iteKnown_ct (decide valid) (fun s h => by simp only [eval, h.2, Bool.not_not])
    · intro _
      exact (domainTail_ct stable h0 h24 h28 h32 h56 h60 large odd).mono
        (fun _ _ h => ⟨h.1.1, h.2.1.1, h.2.2⟩) (fun _ _ h => h)
    · intro _
      exact (ret_ct 0).mono (fun _ _ _ => trivial) (fun _ _ h => h)
  unfold VG.Impl.Ffdh.Arm.Domain.CheckDomain.main VG.Impl.Ffdh.Arm.Domain.ifFlag
  exact relCT_chain prep wpPrep wpPrep (relCT_chain imports wpImport wpImport
    (relCT_chain range wpRange wpRange (relCT_chain tests wpTest wpTest branches)))

end VG.Proof.Ffdh.Arm
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem domainBody_ct {p : Inputs} {slots : List Nat}
    (stable : stableSlots slots = true) (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h28 : 28 ∈ slots) (h32 : 32 ∈ slots) :
    RelCT isa (fun s t => Context p slots s ∧ Context p slots t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.Domain.head VG.Impl.Ffdh.Arm.Domain.CheckDomain.main) (fun _ _ => True) := by
  let Q := fun s : State => Context p (60 :: 56 :: slots) s ∧ s.z = Spec.Rsa.modulusValid p.P p.k
  have wp (s : State) (h : Context p slots s) :
      WP isa (.seq (.block (VG.Impl.Ffdh.Arm.Domain.prepareArgs 24 ++ VG.Impl.Ffdh.Arm.Domain.domainPointers))
        (.block VG.Impl.Bignum.Arm.modulusCheck)) s Q :=
    WP.mono (head_ok s h stable h0 h24 h32) fun _ j => ⟨j.1, j.2.1⟩
  have stable' : stableSlots (60 :: 56 :: slots) = true := by
    change (true && (true && stableSlots slots)) = true
    rw [Bool.true_and, Bool.true_and, stable]
  have gInput (s : State) (h : Context p (60 :: 56 :: slots) s) :
      DomainMainInput p (60 :: 56 :: slots) ((p.dom.drop p.k).take p.k) s := by
    refine ⟨h, h.gBytes, ?_⟩
    rw [p.gLength]
    exact h.toArgumentMemory.domainSliceStack (by have := p.minLength; omega_using [this])
      (by rw [p.domainLength]; split <;> omega_using [])
  have branches : RelCT isa (fun s t => Q s ∧ Q t ∧ s.sp = t.sp)
      (.ite .eq VG.Impl.Ffdh.Arm.Domain.CheckDomain.main (VG.Impl.Ffdh.Arm.Domain.ret 0)) (fun _ _ => True) := by
    apply iteKnown_ct (Spec.Rsa.modulusValid p.P p.k) (fun s h => by change some s.z = _; rw [h.2])
    · intro valid
      have facts := VG.Proof.Bignum.valid_facts valid p.minLength
      exact (domainMain_ct stable' (by simp [h0]) (by simp [h24]) (by simp [h28])
        (by simp [h32]) (by simp) (by simp) facts.2.1 facts.1).mono
        (fun s t h => ⟨gInput s h.1.1, gInput t h.2.1.1, h.2.2⟩) (fun _ _ h => h)
    · intro _
      exact (ret_ct 0).mono (fun _ _ _ => trivial) (fun _ _ h => h)
  unfold VG.Impl.Ffdh.Arm.Domain.head
  apply RelCT.assoc
  exact relCT_chain (head_ct stable h0 h24 h32) wp wp branches

end VG.Proof.Ffdh.Arm

end

end

/-! Standard-domain recognition and the complete general fallback are verified. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/VettedValidation/Correct.lean`, which only this module imported.
section

/-! The fast path and fallback implement the unchanged shared parameter contract. -/

section
namespace VG.Proof.Ffdh.Arm.VettedValidation
open VG VG.Arm

theorem correct (s : State) (pre : contract.pre s) :
    ∃ tr t, Exec isa VG.Impl.Ffdh.Arm.VettedValidation.code s tr t ∧
      abiPreserved s t ∧ contract.post s t := by
  obtain ⟨p, _, domain, count, _, bytes, input⟩ := data s pre
  obtain ⟨tr, t, run, preserved, result⟩ := fn_ok s input
  refine ⟨tr, t, run, preserved, ?_⟩
  change (Spec.Ffdh.checkDomainContract abi 128).post s t
  sig_post [Spec.Ffdh.checkDomainContract, Spec.Ffdh.checkDomainSig, abi,
    argRegs, reduceClassify, Loc.val, State.addr]
  rw [BitVec.setWidth_append_eq_right, domain, count]
  change (t.gpr .r0).toNat = if Spec.Ffdh.domainValid p.k
    (Spec.Rsa.bytesAt s.mem (State.addr p.domain) (s.gpr .r1).toNat) then 1 else 0
  rw [bytes, result, checkedDomainFlag_spec]
  split <;> rfl

end VG.Proof.Ffdh.Arm.VettedValidation
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/VettedValidation/BodyTiming.lean`, which only this module imported.
section

/-! The recognition decision depends only on public domain bytes. -/

section
namespace VG.Proof.Ffdh.Arm.VettedValidation
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Impl.Ffdh.Arm.VettedGroups (groups recognize tableSym)

theorem body_ct {p : Inputs} {slots : List Nat}
    (stable : stableSlots slots = true) (h0 : 0 ∈ slots)
    (h24 : 24 ∈ slots) (h28 : 28 ∈ slots) (h32 : 32 ∈ slots) :
    RelCT isa (fun s t =>
      (Context p slots s ∧ VettedGroups.TableAt (s.syms tableSym) groups s) ∧
      (Context p slots t ∧ VettedGroups.TableAt (t.syms tableSym) groups t) ∧
      s.sp = t.sp ∧ s.syms tableSym = t.syms tableSym)
      VG.Impl.Ffdh.Arm.VettedValidation.body (fun _ _ => True) := by
  let P := fun s : State => Context p slots s ∧ VettedGroups.TableAt (s.syms tableSym) groups s
  let Q := fun s : State => Context p slots s ∧
    s.gpr .r11 = BitVec.ofNat 32 (recognize groups p.k p.dom)
  let R := fun s : State => Context p slots s ∧
    s.z = (BitVec.ofNat 32 (recognize groups p.k p.dom) == 0)
  have scan (s : State) (h : P s) : WP isa VG.Impl.Ffdh.Arm.VettedGroups.code s Q :=
    WP.mono (VettedGroups.code_ok s h.1 h24 h28 h32 h.2) fun _ out => ⟨out.1, out.2.1⟩
  have stage := (relCT_keep_sp (VettedGroups.recognition_ct h24 h28 h32)
    (fun _ _ h => h.2.2.1)).wp (fun s t h => ⟨scan s h.1, scan t h.2.1⟩)
  have test (s : State) (h : Q s) : WP isa VG.Impl.Ffdh.Arm.Domain.testFlag s R := by
    refine WP.mono (testFlag_ok s) ?_
    rintro t ⟨⟨zero, mem⟩, rest⟩
    exact ⟨h.1.of_mem mem rest ((rest.gpr .r0 (by simp)).trans h.1.ptr),
      by rw [zero, h.2]⟩
  have branches : RelCT isa (fun s t => R s ∧ R t ∧ s.sp = t.sp)
      (.ite .ne (VG.Impl.Ffdh.Arm.Domain.ret 1)
        (VG.Impl.Ffdh.Arm.Domain.head VG.Impl.Ffdh.Arm.Domain.CheckDomain.main)) (fun _ _ => True) := by
    apply iteKnown_ct (!(BitVec.ofNat 32 (recognize groups p.k p.dom) == 0))
      (fun s h => by change some (!s.z) = _; rw [h.2])
    · intro _
      exact (ret_ct 1).mono (fun _ _ _ => trivial) (fun _ _ h => h)
    · intro _
      exact (domainBody_ct stable h0 h24 h28 h32).mono
        (fun _ _ h => ⟨h.1.1, h.2.1.1, h.2.2⟩) (fun _ _ h => h)
  have tail := relCT_chain (testFlag_ct.mono (P' := fun (s t : State) => Q s ∧ Q t ∧ s.sp = t.sp)
    (fun _ _ _ => trivial) (fun _ _ h => h)) test test branches
  unfold VG.Impl.Ffdh.Arm.VettedValidation.body
  exact stage.seq (tail.mono (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩) (fun _ _ h => h))

end VG.Proof.Ffdh.Arm.VettedValidation
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/VettedValidation/FnTiming.lean`, which only this module imported.
section

/-! The frame and recognition introduce no secret-dependent trace. -/

section
namespace VG.Proof.Ffdh.Arm.VettedValidation
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Impl.Ffdh.Arm.VettedGroups (tableSym groups)

theorem fn_ct {p : Inputs} :
    RelCT isa (fun s t => Input p s ∧ Input p t ∧ s.sp = t.sp ∧
      s.syms tableSym = t.syms tableSym)
      VG.Impl.Ffdh.Arm.VettedValidation.code (fun _ _ => True) := by
  let P := fun a : State => ∃ s, Input p s ∧ a = entered s
  let Q := fun a : State => Context p [0, 32, 28, 24] a ∧
    VettedGroups.TableAt (a.syms tableSym) groups a
  have wp (a : State) (h : P a) :
      WP isa (.block VG.Impl.Ffdh.Arm.Domain.CheckDomain.entry) a Q := by
    obtain ⟨s, input, rfl⟩ := h
    refine WP.mono_syms (withAllRest (domainEntry_ok (entered s) input.args
      input.domain input.domainLength input.count input.scratch)) ?_
    rintro u ⟨⟨context, frame⟩, rest⟩ syms
    have table := input.table.after_frame input.safe frame rest
    rw [← syms] at table
    exact ⟨context, table⟩
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
  have body := entry.seq (body_ct (by decide) (by decide) (by decide) (by decide) (by decide))
  unfold VG.Impl.Ffdh.Arm.VettedValidation.code
  apply framed_ct (fun _ _ h => ⟨h.1.stackFits, h.2.1.stackFits⟩) (fun _ _ h => h.2.2.1)
  intro a b tr1 tr2 u v h e1 e2
  obtain ⟨s, t, related, rfl, rfl⟩ := h
  exact body _ _ _ _ _ _ ⟨⟨s, related.1, rfl⟩, ⟨t, related.2.1, rfl⟩,
    by rw [entered_sp, entered_sp, related.2.2.1], related.2.2.2⟩ e1 e2

end VG.Proof.Ffdh.Arm.VettedValidation
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/VettedValidation/Timing.lean`, which only this module imported.
section

/-! Parameter imports reveal only the already-public domain and table addresses. -/

section
namespace VG.Proof.Ffdh.Arm.VettedValidation
open VG VG.Arm
open VG.Impl.Ffdh.Arm.VettedGroups (tableConsts)

theorem constantTime : ConstantTime isa contract.pre contract.pub
    VG.Impl.Ffdh.Arm.VettedValidation.code := by
  intro s t tr1 tr2 u v hs ht hp e1 e2
  obtain ⟨p, base, domain, count, capacity, domainBytes, inputS⟩ := data s hs
  have relation : (Spec.Ffdh.checkDomainContract abi 128).pub s t ∧
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
  have preT : (Spec.Ffdh.checkDomainContract abi 128).pre (stripConsts tableConsts t) ∧
      ConstsOk tableConsts 128 t := pre_consts.mp ht
  have inputT := domain_input (stripConsts tableConsts t) preT.1 (p := p)
    (p3.symm.trans base) (p0.symm.trans domain)
    (by change (t.gpr .r2).toNat = p.k; rw [← p2]; exact count)
    (by change (stackArg t 0).toNat = p.len; rw [← p4]; exact capacity) ?_
  · have wide := input_widen inputT
    have table := table_input preT.2 wide
    exact (fn_ct s t tr1 tr2 u v ⟨inputS, ⟨wide, table.1, table.2⟩, sp, symbols⟩ e1 e2).1
  · change Spec.Rsa.bytesAt t.mem (State.addr p.domain) (t.gpr .r1).toNat = p.dom
    rw [← p1, ← domain]
    change Spec.Rsa.bytesAt t.mem (BitVec.setWidth 64 (s.gpr .r0)) (s.gpr .r1).toNat = p.dom
    rw [← byteEq, domain]
    exact domainBytes

end VG.Proof.Ffdh.Arm.VettedValidation
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm.VettedValidation
open VG VG.Arm

theorem verified : Verified target VG.Impl.Ffdh.Arm.VettedValidation.code contract :=
  ⟨correct, constantTime, sat⟩

end VG.Proof.Ffdh.Arm.VettedValidation

end

end


/-! Baseline ARMv7 FFDH with RSA's fixed-window arithmetic. -/

@[expose] public section
namespace VG.Proof.Variants.Ffdh.Arm.Base

def variant : VG.Proof.Ffdh.Arm.Backend where
  checkDomain := VG.Impl.Ffdh.Arm.VettedValidation.code
  checkDomain_verified := VG.Proof.Ffdh.Arm.VettedValidation.verified
  checkPublic := VG.Impl.Ffdh.Arm.Domain.CheckPublic.code
  checkPublic_verified := VG.Proof.Ffdh.Arm.checkPublic_verified
  checkPrivate := VG.Impl.Ffdh.Arm.Domain.CheckPrivate.code
  checkPrivate_verified := VG.Proof.Ffdh.Arm.private_verified
  exchange := VG.Impl.Ffdh.Arm.Domain.Exchange.code
  exchange_verified := VG.Proof.Ffdh.Arm.exchange_verified
  suffix := ""
  features := []

end VG.Proof.Variants.Ffdh.Arm.Base
