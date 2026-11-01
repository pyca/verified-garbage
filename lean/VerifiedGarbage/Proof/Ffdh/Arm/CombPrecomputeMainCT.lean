module

import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputePrefixCT
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeTableCT
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeMontgomeryOutCT
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
meta import VerifiedGarbage.Impl.Ffdh.Arm.CombPrecompute
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
meta import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
public import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeCTState
meta import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeCTState
public import VerifiedGarbage.Proof.Ffdh.Arm.VettedBoundInstance
meta import VerifiedGarbage.Proof.Ffdh.Arm.VettedBoundInstance
public import VerifiedGarbage.Impl.Ffdh.Arm.CombPrecompute
public import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
meta import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
public import VerifiedGarbage.Proof.Ffdh.Arm.Context
meta import VerifiedGarbage.Proof.Ffdh.Arm.Context
import VerifiedGarbage.Proof.Ffdh.Arm.CachedSamplePolicy
meta import VerifiedGarbage.Proof.Ffdh.Arm.CachedSamplePolicy
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeMontgomeryOut
meta import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeMontgomeryOut

/-! The complete public comb precomputation trace depends only on public inputs. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.CombBuilder
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont

theorem main_ct (backend : MontBackend) {p : Inputs} {sp : BitVec 32}
    (valid : Spec.Ffdh.domainValid p.k p.dom=true) :
    RelCT isa (fun s t => EnterInput p sp s ∧ EnterInput p sp t ∧
      VettedGroups.environment.publicRel s t ∧ s.sp=t.sp)
      (VG.Impl.Ffdh.Arm.CombPrecompute.main
        (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul) VettedBound.code) (fun _ _ => True) := by
  have params : Spec.Ffdh.parametersValid (Spec.Ffdh.domainOf p.k p.dom)=true := by
    have h := valid
    unfold Spec.Ffdh.domainValid at h
    simp only [Bool.and_eq_true] at h
    exact h.1
  have positiveBits : 0<bits p := CachedSample.generation_positive params
  have bitsBound : bits p≤8192 := CachedSample.bits_bound p
  have positive : 0<Spec.Rsa.FixedBaseComb.rows (bits p) := by
    unfold Spec.Rsa.FixedBaseComb.rows Spec.Rsa.FixedBaseComb.teeth
    omega
  have fits : Spec.Rsa.FixedBaseComb.rows (bits p)<2^32 := by
    unfold Spec.Rsa.FixedBaseComb.rows Spec.Rsa.FixedBaseComb.teeth
    omega
  have odd : p.P%2=1 := by
    have modulus := Proof.Ffdh.domainValid_mod valid
    change Spec.Rsa.modulusValid p.P p.k=true at modulus
    exact (Proof.Bignum.valid_facts modulus p.minLength).1
  have prefixWP (s : State) (h : EnterInput p sp s) : WP isa (prefixCode backend) s (InitialInput p sp) := by
    refine WP.mono (prefix_ok backend s h.context h.environment h.calls h.output
      h.workspaceSeparate h.domainSeparate (by rw [h.fixed]; exact h.localSeparate)
      (by rw [h.fixed]; exact h.callSeparate) valid) ?_
    rintro t ⟨memory,_,modulus,r2,_,_⟩
    exact ⟨by simpa only [h.fixed] using memory,modulus,r2⟩
  have prefixTrace := (relCT_keep_sp (prefix_ct backend (p:=p) (sp:=sp) valid) (fun _ _ h => h.2.2.2)).wpDep
    (fun s t h => ⟨prefixWP s h.1,prefixWP t h.2.1⟩)
  have prefixStage : RelCT isa (fun s t => EnterInput p sp s ∧ EnterInput p sp t ∧
      VettedGroups.environment.publicRel s t ∧ s.sp=t.sp) (prefixCode backend)
      (fun s t => InitialInput p sp s ∧ InitialInput p sp t ∧ s.sp=t.sp) := by
    apply prefixTrace.mono (fun _ _ h => h)
    intro s t h
    obtain ⟨spEq,_a,_b,_old,left,right⟩ := h
    exact ⟨left,right,spEq⟩
  have serialized (s : State) (h : InitialInput p sp s) :
      WP isa VG.Impl.Ffdh.Arm.CombPrecompute.montgomeryOut s (InitialInput p sp) := by
    refine WP.mono (montgomeryOut_ok s h.1) ?_
    rintro t ⟨memory,ws,_,_,_,_⟩
    have fit := h.1.ready.width ▸ h.1.ready.layout.2.2.1
    exact ⟨memory,(ws.number fit (by decide : 0<8)).trans h.2.1,
      (ws.number fit (by decide : 4<8)).trans h.2.2⟩
  have done : RelCT isa (fun _ _ => True) (VG.Impl.Ffdh.Arm.Domain.ret 1) (fun _ _ => True) := by
    apply RelCT.taint (A:=taint) (Taint.ofRegs []) _ (by taint_decide)
    intro s t _
    exact Taint.agree_ofRegs (by simp)
  have tail := relCT_chain (montgomeryOut_ct.mono
    (fun _ _ h => ⟨h.1.1,h.2.1.1,h.2.2⟩) (fun _ _ h => h)) serialized serialized
    ((table_ct backend odd positive fits).seq done)
  have grouped := prefixStage.seq tail
  intro s t tr1 tr2 u v h e1 e2
  unfold VG.Impl.Ffdh.Arm.CombPrecompute.main at e1 e2
  cases e1 with
  | seq prepare1 tail1 =>
    cases tail1 with
    | seq bound1 tail1 =>
      cases tail1 with
      | seq metadata1 tail1 =>
        cases e2 with
        | seq prepare2 tail2 =>
          cases tail2 with
          | seq bound2 tail2 =>
            cases tail2 with
            | seq metadata2 tail2 =>
              simpa only [List.append_assoc] using grouped _ _ _ _ _ _ h
                (.seq (.seq prepare1 (.seq bound1 metadata1)) tail1)
                (.seq (.seq prepare2 (.seq bound2 metadata2)) tail2)

end VG.Proof.Ffdh.Arm.CombBuilder
