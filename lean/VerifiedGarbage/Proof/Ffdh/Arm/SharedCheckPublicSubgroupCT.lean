module

public import VerifiedGarbage.Proof.Ffdh.Arm.SubgroupCT
public import VerifiedGarbage.Proof.Ffdh.Arm.DomainCallMemory
public import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
public import VerifiedGarbage.Impl.Ffdh.Arm.SharedCheckPublic
import VerifiedGarbage.Proof.Ffdh.Arm.SharedCheckPublicPublicPowerCT
import VerifiedGarbage.Proof.Ffdh.Arm.SharedCheckPublicPublicPower
import VerifiedGarbage.Proof.Ffdh.Arm.ValueChecksCT
import VerifiedGarbage.Proof.Bignum.Arm.TwoExpSharedCT
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT

/-! Public subgroup checking calls the shared Montgomery window. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Spec.Rsa.Mont (Operand)

theorem sharedCheckPublicSubgroup_ct (backend : MontBackend) {p : Inputs} {slots : List Nat}
    {slot : Nat} {bb : List Byte} (stable : stableSlots slots = true)
    (hb : slot ∈ slots) (h60 : 60 ∈ slots) (h32 : 32 ∈ slots)
    (hasQ : p.hasQ = true) (baseLength : bb.length = p.k) (odd : p.P % 2 = 1) :
    RelCT isa (fun s t => (SubgroupInput p slots slot bb s ∧ DomainCallMemory p s) ∧
      (SubgroupInput p slots slot bb t ∧ DomainCallMemory p t) ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.SharedCheckPublic.subgroup
        (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul) slot) (fun _ _ => True) := by
  have positive : 0 < ((p.dom.drop (2*p.k)).take p.k).length := by
    rw [p.qLength hasQ]; have := p.minLength; omega
  have fits : ((p.dom.drop (2*p.k)).take p.k).length < 2^32 := by
    rw [p.qLength hasQ]; have := p.maxLength; omega
  have count : p.slotValue 32 = BitVec.ofNat 32 ((p.dom.drop (2*p.k)).take p.k).length := by
    change BitVec.ofNat 32 p.k = _; rw [p.qLength hasQ]
  have family (sp0 : BitVec 32) :
      RelCT isa (fun s t => (SubgroupInput p slots slot bb s ∧ DomainCallMemory p s ∧ s.sp = sp0) ∧
        (SubgroupInput p slots slot bb t ∧ DomainCallMemory p t ∧ t.sp = sp0) ∧ s.sp = t.sp)
        (VG.Impl.Ffdh.Arm.SharedCheckPublic.subgroup
          (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul) slot) (fun _ _ => True) := by
    intro s t tr1 tr2 u v initial run1 run2
    let correct := fun o a b ho ha hb v input => backend.correct v (base := p.base) (len := p.len)
      (w := p.w) (o := o) (a := a) (b := b) input ho ha hb
    let K := TwoExp.sharedMontgomery p.base sp0 p.len p.w backend.name backend.mul correct backend.stackOk
    have timing : TwoExp.MontgomeryTiming K :=
      TwoExp.sharedMontgomeryTiming p.base sp0 p.len p.w backend.name backend.mul correct backend.stackOk
        (fun _ _ _ ho ha hb => backend.rawCT ho ha hb)
    have below (s : State) (h : SubgroupInput p slots slot bb s ∧ DomainCallMemory p s ∧ s.sp = sp0) :
        Region.Disjoint ⟨State.addr (p.slotValue 60), ((p.dom.drop (2*p.k)).take p.k).length⟩
          (FrameStack.belowA sp0 48) := by
      change Region.Disjoint ⟨State.addr p.q, _⟩ _
      rw [p.qLength hasQ, ←h.2.2]
      exact h.2.1.domainSlice h.1.context (by have := p.minLength; omega)
        (by rw [p.domainLength,hasQ]; simp only [ite_true]; omega)
    have separate : ∀ r ∈ [⟨State.addr p.base,8*p.len⟩,FrameStack.belowA sp0 48],
        Region.Disjoint ⟨State.addr (p.slotValue 60), ((p.dom.drop (2*p.k)).take p.k).length⟩ r := by
      intro r hr
      rcases List.mem_cons.mp hr with hr | hr
      · subst r
        exact (initial.1.1.context.qBytes hasQ).separate
      · have eq := List.mem_singleton.mp hr; subst r
        exact below s initial.1
    have powers := sharedCheckPublicPublicPower_ct K timing stable hb h60 h32 h32
      baseLength positive fits count odd separate
    have wp (s : State) (h : SubgroupInput p slots slot bb s ∧ DomainCallMemory p s ∧ s.sp = sp0) :=
      WP.mono (sharedCheckPublicPublicPower_ok backend s slot 60 32 h.1.context h.2.1 stable hb h60 h32 h32
        h.1.ready h.1.modulus odd h.1.r2 h.1.source baseLength (h.1.context.qBytes hasQ)
        positive fits count (by rw [h.2.2]; exact below s h)) fun _ j => j.2.1
    exact (relCT_chain (powers.mono (fun _ _ h =>
      ⟨⟨⟨h.1.1.context,h.1.1.ready,h.1.1.modulus,h.1.1.r2,h.1.1.source,h.1.1.context.qBytes hasQ⟩,
          h.1.2.1.stack,h.1.2.2⟩,
        ⟨⟨h.2.1.1.context,h.2.1.1.ready,h.2.1.1.modulus,h.2.1.1.r2,h.2.1.1.source,h.2.1.1.context.qBytes hasQ⟩,
          h.2.1.2.1.stack,h.2.1.2.2⟩,h.2.2⟩) (fun _ _ h => h)) wp wp
      (isOne_ct (by simp [Operand,Spec.Rsa.Mont.aAcc,Spec.Rsa.Mont.aTmp] : Operand 6)))
      s t tr1 tr2 u v initial run1 run2
  intro s t tr1 tr2 u v h e1 e2
  exact family s.sp s t tr1 tr2 u v
    ⟨⟨h.1.1,h.1.2,rfl⟩,⟨h.2.1.1,h.2.1.2,h.2.2.symm⟩,h.2.2⟩ e1 e2

end VG.Proof.Ffdh.Arm
