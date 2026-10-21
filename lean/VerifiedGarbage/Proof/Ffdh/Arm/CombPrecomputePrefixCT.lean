module

public import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeCTState
public import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputePrefix
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeMetadataCT
import VerifiedGarbage.Proof.Ffdh.Arm.NormalizedPrepareAtCT
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Framework.Arm.Syms
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ffdh.Arm.CachedSampleBound
import VerifiedGarbage.Proof.Ffdh.Arm.CachedSamplePolicy
import VerifiedGarbage.Proof.Ffdh.Arm.NormalizedPrepareAt

/-! Public recognition and policy metadata fix the precomputation schedule. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.CombBuilder
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont

private def Prepared (p : Inputs) (s : State) : Prop :=
  Context p slots s ∧ VettedGroups.environment.holds p s

private def Bounded (p : Inputs) (s : State) : Prop :=
  Locals p.base p.len s ∧ s.mem.readW (off (State.addr s.sp) 4) 32=p.output ∧
    s.mem.readW (off (State.addr s.sp) 20) 32=BitVec.ofNat 32 (Proof.Ffdh.ScalarWidth.width (bits p)) ∧
    s.mem.readW (off (State.addr s.sp) 68) 32=(Proof.Ffdh.ScalarWidth.mask (bits p)).setWidth 32

theorem prefix_ct (backend : MontBackend) {p : Inputs} {sp : BitVec 32}
    (valid : Spec.Ffdh.domainValid p.k p.dom=true) :
    RelCT isa (fun s t => EnterInput p sp s ∧ EnterInput p sp t ∧
      VettedGroups.environment.publicRel s t ∧ s.sp=t.sp)
      (prefixCode backend) (fun _ _ => True) := by
  have modulusValid := Proof.Ffdh.domainValid_mod valid
  change Spec.Rsa.modulusValid p.P p.k=true at modulusValid
  have facts := Proof.Bignum.valid_facts modulusValid p.minLength
  have params : Spec.Ffdh.parametersValid (Spec.Ffdh.domainOf p.k p.dom)=true := by
    have h := valid
    unfold Spec.Ffdh.domainValid at h
    simp only [Bool.and_eq_true] at h
    exact h.1
  have positive : 0<bits p := CachedSample.generation_positive params
  have bound : bits p≤8192 := CachedSample.bits_bound p
  have prepare (s : State) (h : EnterInput p sp s) :
      WP isa (VG.Impl.Ffdh.Arm.NormalizedPrepare.prepareAt
        (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul) 24) s (Prepared p) := by
    refine WP.mono_syms (normalizedPrepareAt24_ok backend s h.context h.calls (by decide)
      (by decide) (by decide) (by decide) facts.2.1 facts.1 facts.2.2) ?_
    rintro u ⟨context,_,_,_,frame,rest⟩ syms
    refine ⟨context,VettedGroups.environment.stable h.environment (frame.sub ?_) rest syms⟩
    intro r hr
    simp only [keyPrepareWrites,prepareAtWrites,prepareWrites,List.mem_append,List.mem_cons,
      List.not_mem_nil,or_false,or_assoc] at hr
    rcases hr with rfl|rfl|rfl|rfl
    · exact ⟨_,by simp [keyCallWrites,keyWrites],fun _ h => h⟩
    · exact ⟨⟨State.addr s.sp,72⟩,by simp [keyCallWrites,keyWrites],Offset.sub_base _ (by decide)⟩
    · exact ⟨⟨State.addr s.sp,72⟩,by simp [keyCallWrites,keyWrites],Offset.sub_base _ (by decide)⟩
    · exact ⟨_,by simp [keyCallWrites,keyWrites],fun _ h => h⟩
  have bounded (s : State) (h : Prepared p s) : WP isa VettedBound.code s (Bounded p) := by
    refine WP.mono (VettedBound.law.correct s h.1 h.2 facts.2.2 facts.1
      (by decide) (by intro d hd; revert d; decide) (by decide) (by decide) (by decide) (by decide)) ?_
    rintro t ⟨context,width,mask,_,_⟩
    have widthEq : (ScalarLayout.vetted p).width=Proof.Ffdh.ScalarWidth.width (bits p) := by
      have value := CachedSample.layout_width p positive
      unfold Proof.Ffdh.ScalarWidth.width
      change (ScalarLayout.vetted p).width=max 1 ((bits p+7)/8)
      rw [Nat.max_eq_right (by omega)]
      exact value
    rw [widthEq] at width
    exact ⟨context.locals,context.saved 4 (by simp [slots]),width,mask⟩
  have prepareTrace := normalizedPrepareAt24_ct backend (p:=p) (slots:=slots)
    (by decide) (by decide) (by decide) (by decide) facts.2.1 facts.1 facts.2.2
  have preparedCT := prepareTrace.mono
    (P':=fun (s t : State) => EnterInput p sp s ∧ EnterInput p sp t ∧ VettedGroups.environment.publicRel s t ∧ s.sp=t.sp)
    (fun _ _ h => ⟨⟨h.1.context,h.1.calls⟩,⟨h.2.1.context,h.2.1.calls⟩,h.2.2.2⟩) (fun _ _ _ => trivial)
  have stage := (relCT_keep_sp preparedCT (fun _ _ h => h.2.2.2)).wpDep
    (fun s t h => ⟨prepare s h.1,prepare t h.2.1⟩)
  have preserved : RelCT isa (fun s t => EnterInput p sp s ∧ EnterInput p sp t ∧
      VettedGroups.environment.publicRel s t ∧ s.sp=t.sp)
      (VG.Impl.Ffdh.Arm.NormalizedPrepare.prepareAt
        (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul) 24)
      (fun s t => Prepared p s ∧ Prepared p t ∧ VettedGroups.environment.publicRel s t ∧ s.sp=t.sp) := by
    intro s t tr1 tr2 u v h e1 e2
    obtain ⟨trace,_sp,_a,_b,_eq,left,right⟩ := stage _ _ _ _ _ _ h e1 e2
    exact ⟨trace,left,right,VettedGroups.environment.public_stable h.2.2.1 (Exec.syms e1) (Exec.syms e2),
      (Exec.rdwr e1).2.2.trans (h.2.2.2.trans (Exec.rdwr e2).2.2.symm)⟩
  have boundTrace := (VettedBound.law.ct (p:=p) (slots:=slots) (by decide)
    (by intro d hd; revert d; decide) facts.2.2 facts.1 (by decide) (by decide) (by decide) (by decide)).mono
      (P':=fun (s t : State) => Prepared p s ∧ Prepared p t ∧ VettedGroups.environment.publicRel s t ∧ s.sp=t.sp)
      (fun _ _ h => h) (fun _ _ _ => trivial)
  have boundStage := (relCT_keep_sp boundTrace (fun _ _ h => h.2.2.2)).wpDep
    (fun s t h => ⟨bounded s h.1,bounded t h.2.1⟩)
  have boundedCT : RelCT isa (fun s t => Prepared p s ∧ Prepared p t ∧
      VettedGroups.environment.publicRel s t ∧ s.sp=t.sp) VettedBound.code
      (fun s t => Bounded p s ∧ Bounded p t ∧ s.sp=t.sp) := by
    apply boundStage.mono (fun _ _ h => h)
    intro s t h
    obtain ⟨spEq,_a,_b,_old,left,right⟩ := h
    exact ⟨left,right,spEq⟩
  unfold prefixCode
  exact preserved.seq (boundedCT.seq (combMetadata_ct positive bound))

end VG.Proof.Ffdh.Arm.CombBuilder
