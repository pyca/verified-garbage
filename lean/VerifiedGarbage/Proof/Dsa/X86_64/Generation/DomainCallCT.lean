module

public import VerifiedGarbage.Proof.Dsa.X86_64.ParametersCT

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

end VG.Proof.Dsa.X86_64.Generation
