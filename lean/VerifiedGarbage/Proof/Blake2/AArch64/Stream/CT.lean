module

public import VerifiedGarbage.Proof.Blake2.AArch64.Stream.Lit
meta import VerifiedGarbage.Proof.Blake2.AArch64.Stream.Lit
public import VerifiedGarbage.Proof.Blake2.AArch64.Stream.Common
meta import VerifiedGarbage.Proof.Blake2.AArch64.Stream.Common
public import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Blake2.Spec
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.MdStream.AArch64.Common
import VerifiedGarbage.Proof.Sha256.Stream
meta import VerifiedGarbage.Proof.Blake2.Spec
meta import VerifiedGarbage.Proof.Framework.AArch64.Call
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.MdStream.AArch64.Common
meta import VerifiedGarbage.Proof.Sha256.Stream

/-!
# Streaming BLAKE2 on AArch64: constant time

The taint analysis of `init`, `update` and `finalize` (the compression
function they call included), from the public arguments: the pointers,
`outlen`, `keylen`, `count` and `len`, and the stack pointer.
-/

@[expose] public section

namespace VG.Proof.Blake2.AArch64.Stream

open VG VG.AArch64 VG.Spec.Blake2

theorem init_agree {w : Nat} {P : Params w} {s₁ s₂ : State} (hpub : (initAArch64 P).pub s₁ s₂) :
    AArch64.Taint.Agree (AArch64.Taint.ofRegs [.x0, .x1, .x2, .x3]) s₁ s₂ := by
  obtain ⟨p1, p2, p3, p4, hsp⟩ := hpub
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> assumption

theorem update_agree {w : Nat} {P : Params w} {s₁ s₂ : State} (hpub : (updateAArch64 P).pub s₁ s₂) :
    AArch64.Taint.Agree (AArch64.Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) s₁ s₂ := by
  obtain ⟨p1, p2, p3, p4, p5, hsp⟩ := hpub
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> assumption

theorem finalize_agree {w : Nat} {P : Params w} {s₁ s₂ : State}
    (hpub : (finalizeAArch64 P).pub s₁ s₂) :
    AArch64.Taint.Agree (AArch64.Taint.ofRegs [.x0, .x1, .x2, .x3]) s₁ s₂ := by
  obtain ⟨p1, p2, p3, p4, hsp⟩ := hpub
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> assumption

theorem okB : Ok Spec.Blake2.b := ⟨by decide, .inl rfl⟩
theorem okS : Ok Spec.Blake2.s := ⟨by decide, .inr rfl⟩

theorem initB_ct : ConstantTime isa (initAArch64 b).pre (initAArch64 b).pub
    (Impl.Blake2.AArch64.Stream.init b) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3])
    (fun _ _ _ _ hp => init_agree hp) (by taint_decide)

theorem initS_ct : ConstantTime isa (initAArch64 s).pre (initAArch64 s).pub
    (Impl.Blake2.AArch64.Stream.init s) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3])
    (fun _ _ _ _ hp => init_agree hp) (by taint_decide)

theorem updateB_ct : ConstantTime isa (updateAArch64 b).pre (updateAArch64 b).pub
    (Impl.Blake2.AArch64.Stream.update b) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4])
    (fun _ _ _ _ hp => update_agree hp) (by taint_decide)

theorem updateS_ct : ConstantTime isa (updateAArch64 s).pre (updateAArch64 s).pub
    (Impl.Blake2.AArch64.Stream.update s) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4])
    (fun _ _ _ _ hp => update_agree hp) (by taint_decide)

theorem finalizeB_ct : ConstantTime isa (finalizeAArch64 b).pre (finalizeAArch64 b).pub
    (Impl.Blake2.AArch64.Stream.finalize b) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3])
    (fun _ _ _ _ hp => finalize_agree hp) (by taint_decide)

theorem finalizeS_ct : ConstantTime isa (finalizeAArch64 s).pre (finalizeAArch64 s).pub
    (Impl.Blake2.AArch64.Stream.finalize s) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3])
    (fun _ _ _ _ hp => finalize_agree hp) (by taint_decide)

end VG.Proof.Blake2.AArch64.Stream
