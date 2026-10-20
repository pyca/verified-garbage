module

import VerifiedGarbage.Proof.Ffdh.Arm.DomainQChecks
public import VerifiedGarbage.Proof.Ffdh.Arm.SubgroupCT
import VerifiedGarbage.Proof.Ffdh.Arm.DomainQRangeCT
import VerifiedGarbage.Proof.Ffdh.Arm.DomainDividesCT
import VerifiedGarbage.Proof.Ffdh.Arm.PrepareAtCT
import VerifiedGarbage.Proof.Ffdh.Arm.FlagCT
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Ffdh.Arm.BranchCT

/-! Order validation branches only on the documented public domain values. -/

@[expose] public section
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
