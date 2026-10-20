module

public import VerifiedGarbage.Impl.Ffdh.Arm.Domain
import VerifiedGarbage.Proof.Ffdh.Arm.Head
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Ffdh.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.ModulusCheckCT
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Impl.Ffdh.Arm.Domain
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack
meta import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack
meta import VerifiedGarbage.Proof.Bignum.Arm.RoundState

/-! The common native head accesses only public domain and local-frame addresses. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

structure ModulusArgs (p : Inputs) (s : State) : Prop where
  source : s.gpr .r4 = p.domain
  count : s.gpr .r6 = BitVec.ofNat 32 p.k

theorem headPrefix_ct {p : Inputs} {slots : List Nat}
    (stable : stableSlots slots = true) (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h32 : 32 ∈ slots) :
    RelCT isa (fun s t => Context p slots s ∧ Context p slots t ∧ s.sp = t.sp)
      (.block (VG.Impl.Ffdh.Arm.Domain.prepareArgs 24 ++ VG.Impl.Ffdh.Arm.Domain.domainPointers))
      (fun _ _ => True) := by
  have args := (prepareArgs_ct 24).mono
    (P' := fun (s t : State) => Context p slots s ∧ Context p slots t ∧ s.sp = t.sp)
    (fun _ _ h => h.2.2) (fun _ _ h => h)
  have wp (s : State) (h : Context p slots s) :
      WP isa (.block (VG.Impl.Ffdh.Arm.Domain.prepareArgs 24)) s (fun t => t.gpr .r12 = t.sp) :=
    by
      refine WP.mono (prepareArgs_ok s 24 h stable h24 h32 h0) ?_
      rintro t ⟨_, _, _, _, stack, _, rest⟩
      exact stack.trans rest.sp.symm
  have pointers : RelCT isa (fun s t => s.gpr .r12 = s.sp ∧ t.gpr .r12 = t.sp ∧ s.sp = t.sp)
      (.block VG.Impl.Ffdh.Arm.Domain.domainPointers) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r12]) _ (by taint_decide)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h.1.trans (h.2.2.trans h.2.1.symm)
  exact RelCT.block_append (relCT_chain args wp wp pointers)

theorem head_ct {p : Inputs} {slots : List Nat}
    (stable : stableSlots slots = true) (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h32 : 32 ∈ slots) :
    RelCT isa (fun s t => Context p slots s ∧ Context p slots t ∧ s.sp = t.sp)
      (.seq (.block (VG.Impl.Ffdh.Arm.Domain.prepareArgs 24 ++ VG.Impl.Ffdh.Arm.Domain.domainPointers))
        (.block VG.Impl.Bignum.Arm.modulusCheck)) (fun _ _ => True) := by
  have wp (s : State) (h : Context p slots s) :
      WP isa (.block (VG.Impl.Ffdh.Arm.Domain.prepareArgs 24 ++ VG.Impl.Ffdh.Arm.Domain.domainPointers)) s
        (ModulusArgs p) := by
    refine WP.mono (headPrefix_ok s h stable h0 h24 h32) ?_
    rintro t ⟨_, source, count, _⟩
    exact ⟨source, count⟩
  have modulus : RelCT isa (fun s t => ModulusArgs p s ∧ ModulusArgs p t ∧ s.sp = t.sp)
      (.block VG.Impl.Bignum.Arm.modulusCheck) (fun _ _ => True) := by
    intro s t tr1 tr2 u v h e1 e2
    exact ⟨modulusCheck_ct s t tr1 tr2 u v trivial trivial
      ⟨h.1.source.trans h.2.1.source.symm, h.1.count.trans h.2.1.count.symm⟩ e1 e2, trivial⟩
  exact relCT_chain (headPrefix_ct stable h0 h24 h32) wp wp modulus

end VG.Proof.Ffdh.Arm
