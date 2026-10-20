module

import VerifiedGarbage.Proof.Ffdh.Arm.ImportAt
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
import VerifiedGarbage.Proof.Ffdh.Arm.DomainDivides
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Ffdh.Arm.PrepareAtCT
import VerifiedGarbage.Proof.Ffdh.Arm.ImportAtCT
import VerifiedGarbage.Proof.Ffdh.Arm.ValueChecksCT
import VerifiedGarbage.Proof.Bignum.Arm.ReduceOperandCT
import VerifiedGarbage.Proof.Bignum.Arm.ReduceOperand
import VerifiedGarbage.Proof.Bignum.Arm.SmallConstCT
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack
public import VerifiedGarbage.Impl.Ffdh.Arm.Domain

/-! Divisibility checking reuses RSA's constant-time full-width reduction. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Spec.Rsa.Mont (numAt Operand arrAt)

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
  have op0 : Operand 0 := by simp [Operand, Spec.Rsa.Mont.aAcc, Spec.Rsa.Mont.aTmp]
  have op1 : Operand 1 := by simp [Operand, Spec.Rsa.Mont.aAcc, Spec.Rsa.Mont.aTmp]
  have op4 : Operand 4 := by simp [Operand, Spec.Rsa.Mont.aAcc, Spec.Rsa.Mont.aTmp]
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
    have := p.width.2.2.1; simp only [arrAt, Spec.Rsa.Mont.hdrBytes] at *; omega
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
