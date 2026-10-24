module

public import VerifiedGarbage.Proof.Dsa.X86_64.ParametersCT
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.DomainCall
import VerifiedGarbage.Proof.Framework.X86_64.CallBody

/-! # Call the existing domain checker with public packed bytes and pointers -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Dsa.X86_64

structure DomainCallPublic where
  input : ParametersInput
  pointer : Addr

def DomainCallBefore (p : DomainCallPublic) (s : State) : Prop :=
  ParametersPre p.input s ∧ s.gpr .rdi = p.pointer

theorem domainCall_related {s t : State} (h : Two DomainCallBefore s t) : Two ParametersStart s t := by
  obtain ⟨p, ⟨hs, hp⟩, ⟨ht, hq⟩⟩ := h
  let a : ParametersCall := ⟨p.input, s, hs⟩
  let b : ParametersCall := ⟨p.input, t, ht⟩
  have fields : checkFieldValues t p.input.accepted = checkFieldValues s p.input.accepted := by
    funext f
    cases f <;> simp only [checkFieldValues, hp, hq, hs.pLength, ht.pLength, hs.qLength, ht.qLength]
  have layout : b.layout = a.layout := by
    change p.input.layout t ht.pLength ht.qLength = p.input.layout s hs.pLength hs.qLength
    simp only [ParametersInput.layout, fields]
  exact ⟨a, ⟨a, ⟨rfl, rfl⟩, rfl⟩, ⟨b, ⟨layout, rfl⟩, rfl⟩⟩

theorem domainCall_ct (M : Mont) (Sq : MontS) :
    RelCT isa (Two DomainCallBefore) (Generate.checkParameters Sq.mm M.mm) (fun _ _ => True) :=
  (parametersMain_ct M Sq).mono (fun _ _ h => domainCall_related h) (fun _ _ h => h)


def DomainCalledBefore (p : DomainCallPublic × Addr) (s : State) : Prop :=
  DomainCallBefore p.1 s ∧ s.gpr .rsp = p.2 ∧
  (domainReturn s).Disjoint ⟨p.1.input.base, Impl.Dsa.Layout.usedBytes⟩ ∧
  (domainReturn s).Disjoint ⟨s.gpr .rdi, p.1.input.params.length⟩

theorem domainCall_called_ct (M : Mont) (Sq : MontS) (name : String) :
    RelCT isa (Two DomainCalledBefore)
      (.call name (Generate.checkParameters Sq.mm M.mm)) (fun _ _ => True) := by
  apply RelCT.callBody (domainCall_ct M Sq)
  · rintro s t ⟨p, hs, ht⟩
    refine ⟨p.1, ⟨parameters_callEntry hs.1.1 hs.2.2.2, ?_⟩,
      ⟨parameters_callEntry ht.1.1 ht.2.2.2, ?_⟩⟩
    · exact (State.callEntry_gpr s (by decide)).trans hs.1.2
    · exact (State.callEntry_gpr t (by decide)).trans ht.1.2
  · rintro s t ⟨p, hs, ht⟩
    exact hs.2.1.trans ht.2.1.symm

end VG.Proof.Dsa.X86_64.Generation
