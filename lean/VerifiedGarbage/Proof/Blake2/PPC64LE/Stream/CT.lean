module

public import VerifiedGarbage.Proof.Blake2.PPC64LE.Stream.Common
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Blake2.PPC64LE.Stream.Lit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Blake2.PPC64LE.Stream.Common
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Blake2.PPC64LE.Stream.Lit
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# Streaming BLAKE2 on PPC64LE: constant time

The taint analysis of `init`, `update` and `finalize` (the compression
function they call included), from the public arguments: the pointers,
`outlen`, `keylen`, `count` and `len`, and the stack pointer.
-/

@[expose] public section

namespace VG.Proof.Blake2.PPC64LE.Stream

open VG VG.PPC64LE VG.Spec.Blake2

theorem init_agree {w : Nat} {P : Params w} {s₁ s₂ : State} (hpub : (initPPC64LE P).pub s₁ s₂) :
    PPC64LE.Taint.Agree (PPC64LE.Taint.ofRegs [.r3, .r4, .r5, .r6]) s₁ s₂ := by
  obtain ⟨p1, p2, p3, p4, hsp⟩ := hpub
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [PPC64LE.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem update_agree {w : Nat} {P : Params w} {s₁ s₂ : State} (hpub : (updatePPC64LE P).pub s₁ s₂) :
    PPC64LE.Taint.Agree (PPC64LE.Taint.ofRegs [.r3, .r4, .r5, .r6, .r7]) s₁ s₂ := by
  obtain ⟨p1, p2, p3, p4, p5, hsp⟩ := hpub
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [PPC64LE.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem finalize_agree {w : Nat} {P : Params w} {s₁ s₂ : State}
    (hpub : (finalizePPC64LE P).pub s₁ s₂) :
    PPC64LE.Taint.Agree (PPC64LE.Taint.ofRegs [.r3, .r4, .r5, .r6]) s₁ s₂ := by
  obtain ⟨p1, p2, p3, p4, hsp⟩ := hpub
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [PPC64LE.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem okB : Ok Spec.Blake2.b := ⟨by decide, .inl rfl⟩
theorem okS : Ok Spec.Blake2.s := ⟨by decide, .inr rfl⟩

theorem initB_ct : ConstantTime isa (initPPC64LE b).pre (initPPC64LE b).pub
    (Impl.Blake2.PPC64LE.Stream.init b) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6])
    (fun _ _ _ _ hp => init_agree hp) (by taint_decide)

theorem initS_ct : ConstantTime isa (initPPC64LE s).pre (initPPC64LE s).pub
    (Impl.Blake2.PPC64LE.Stream.init s) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6])
    (fun _ _ _ _ hp => init_agree hp) (by taint_decide)

theorem updateB_ct : ConstantTime isa (updatePPC64LE b).pre (updatePPC64LE b).pub
    (Impl.Blake2.PPC64LE.Stream.update b) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7])
    (fun _ _ _ _ hp => update_agree hp) (by taint_decide)

theorem updateS_ct : ConstantTime isa (updatePPC64LE s).pre (updatePPC64LE s).pub
    (Impl.Blake2.PPC64LE.Stream.update s) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7])
    (fun _ _ _ _ hp => update_agree hp) (by taint_decide)

theorem finalizeB_ct : ConstantTime isa (finalizePPC64LE b).pre (finalizePPC64LE b).pub
    (Impl.Blake2.PPC64LE.Stream.finalize b) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6])
    (fun _ _ _ _ hp => finalize_agree hp) (by taint_decide)

theorem finalizeS_ct : ConstantTime isa (finalizePPC64LE s).pre (finalizePPC64LE s).pub
    (Impl.Blake2.PPC64LE.Stream.finalize s) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6])
    (fun _ _ _ _ hp => finalize_agree hp) (by taint_decide)

end VG.Proof.Blake2.PPC64LE.Stream
