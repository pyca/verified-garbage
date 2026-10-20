module

public import VerifiedGarbage.Proof.Ffdh.Arm.Output
public import VerifiedGarbage.Proof.Ffdh.Arm.Context

/-! The two caller-owned key encodings are disjoint from arithmetic, domain,
and local stack storage. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm
open VG.Proof.X25519.Arm (Rest)

structure KeyOutputs (p : Inputs) (s : State) : Prop where
  privateBuffer : OutputBuffer p.privateValue p.k s
  publicBuffer : OutputBuffer p.publicValue p.k s
  privateDomain : Region.Disjoint ⟨State.addr p.domain, p.dom.length⟩ ⟨State.addr p.privateValue, p.k⟩
  publicDomain : Region.Disjoint ⟨State.addr p.domain, p.dom.length⟩ ⟨State.addr p.publicValue, p.k⟩
  privateStack : Region.Disjoint ⟨State.addr s.sp, 72⟩ ⟨State.addr p.privateValue, p.k⟩
  publicStack : Region.Disjoint ⟨State.addr s.sp, 72⟩ ⟨State.addr p.publicValue, p.k⟩
  privateWorkspace : Region.Disjoint ⟨State.addr p.privateValue, p.k⟩ ⟨State.addr p.base, 8 * p.len⟩
  publicWorkspace : Region.Disjoint ⟨State.addr p.publicValue, p.k⟩ ⟨State.addr p.base, 8 * p.len⟩
  separate : Region.Disjoint ⟨State.addr p.privateValue, p.k⟩ ⟨State.addr p.publicValue, p.k⟩

theorem KeyOutputs.after {p : Inputs} {s t : State} {rs : List Reg}
    (h : KeyOutputs p s) (rest : Rest rs s t) : KeyOutputs p t :=
  ⟨h.privateBuffer.after rest, h.publicBuffer.after rest, h.privateDomain, h.publicDomain,
    by rw [rest.sp]; exact h.privateStack, by rw [rest.sp]; exact h.publicStack,
    h.privateWorkspace, h.publicWorkspace, h.separate⟩

end VG.Proof.Ffdh.Arm
