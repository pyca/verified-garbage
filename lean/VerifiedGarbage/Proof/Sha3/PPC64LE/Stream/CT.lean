module

public import VerifiedGarbage.Proof.Sha3.PPC64LE.Contract
public import VerifiedGarbage.Impl.Sha3.PPC64LE.Stream
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Sha3.PPC64LE.Stream.Lit
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Sha3.PPC64LE.Contract
meta import VerifiedGarbage.Impl.Sha3.PPC64LE.Stream
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Sha3.PPC64LE.Stream.Lit
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# The SHA-3 sponge on PPC64LE: constant time

The taint analysis of `absorb`, `pad` and `squeeze` (the permutation they
call included), from the public arguments: the pointers, `rate`, `pos` and
the lengths, and the stack pointer.
-/

@[expose] public section

namespace VG.Proof.Sha3.PPC64LE.Stream

open VG VG.PPC64LE

theorem absorb_agree {s₁ s₂ : State} (hpub : Proof.Sha3.absorbPPC64LE.pub s₁ s₂) :
    PPC64LE.Taint.Agree (PPC64LE.Taint.ofRegs [.r3, .r4, .r5, .r6, .r7, .r8]) s₁ s₂ := by
  obtain ⟨p1, p2, p3, p4, p5, p6, hsp⟩ := hpub
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [PPC64LE.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem pad_agree {s₁ s₂ : State} (hpub : Proof.Sha3.padPPC64LE.pub s₁ s₂) :
    PPC64LE.Taint.Agree (PPC64LE.Taint.ofRegs [.r3, .r4, .r5, .r7]) s₁ s₂ := by
  obtain ⟨p1, p2, p3, p4, hsp⟩ := hpub
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [PPC64LE.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem squeeze_agree {s₁ s₂ : State} (hpub : Proof.Sha3.squeezePPC64LE.pub s₁ s₂) :
    PPC64LE.Taint.Agree (PPC64LE.Taint.ofRegs [.r3, .r4, .r5, .r6, .r7, .r8]) s₁ s₂ := by
  obtain ⟨p1, p2, p3, p4, p5, p6, hsp⟩ := hpub
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [PPC64LE.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem absorb_ct : ConstantTime isa Proof.Sha3.absorbPPC64LE.pre Proof.Sha3.absorbPPC64LE.pub
    Impl.Sha3.PPC64LE.Stream.absorb :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7, .r8])
    (fun _ _ _ _ hp => absorb_agree hp) (by taint_decide)

theorem pad_ct : ConstantTime isa Proof.Sha3.padPPC64LE.pre Proof.Sha3.padPPC64LE.pub
    Impl.Sha3.PPC64LE.Stream.pad :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r7])
    (fun _ _ _ _ hp => pad_agree hp) (by taint_decide)

theorem squeeze_ct : ConstantTime isa Proof.Sha3.squeezePPC64LE.pre Proof.Sha3.squeezePPC64LE.pub
    Impl.Sha3.PPC64LE.Stream.squeeze :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7, .r8])
    (fun _ _ _ _ hp => squeeze_agree hp) (by taint_decide)

end VG.Proof.Sha3.PPC64LE.Stream
