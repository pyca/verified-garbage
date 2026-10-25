module

public import VerifiedGarbage.Proof.Blake2.RISCV64.Stream.Common
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.Blake2.RISCV64.Stream.Lit
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Blake2.RISCV64.Stream.Common
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Blake2.RISCV64.Stream.Lit
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# Streaming BLAKE2 on RISC-V: constant time

The taint analysis of `init`, `update` and `finalize` (the compression
function they call included), from the public arguments: the pointers,
`outlen`, `keylen`, `count` and `len`, and the stack pointer.
-/

@[expose] public section

namespace VG.Proof.Blake2.RISCV64.Stream

open VG VG.RISCV64 VG.Spec.Blake2

theorem agree4 {s₁ s₂ : State} (h0 : s₁.gpr .a0 = s₂.gpr .a0) (h1 : s₁.gpr .a1 = s₂.gpr .a1)
    (h2 : s₁.gpr .a2 = s₂.gpr .a2) (h3 : s₁.gpr .a3 = s₂.gpr .a3) (hsp : s₁.sp = s₂.sp) :
    taint.Agree (Taint.ofRegs [.a0, .a1, .a2, .a3]) s₁ s₂ := by
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  exacts [h0, h1, h2, h3]

theorem agree5 {s₁ s₂ : State} (h0 : s₁.gpr .a0 = s₂.gpr .a0) (h1 : s₁.gpr .a1 = s₂.gpr .a1)
    (h2 : s₁.gpr .a2 = s₂.gpr .a2) (h3 : s₁.gpr .a3 = s₂.gpr .a3) (h4 : s₁.gpr .a4 = s₂.gpr .a4)
    (hsp : s₁.sp = s₂.sp) :
    taint.Agree (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4]) s₁ s₂ := by
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  exacts [h0, h1, h2, h3, h4]

theorem okB : Ok Spec.Blake2.b := ⟨by decide, .inl rfl⟩
theorem okS : Ok Spec.Blake2.s := ⟨by decide, .inr rfl⟩

theorem initB_ct : ConstantTime isa (initRISCV64 b).pre (initRISCV64 b).pub
    (Impl.Blake2.RISCV64.Stream.init b) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3])
    (fun _ _ _ _ ⟨h0, h1, h2, h3, hsp⟩ => agree4 h0 h1 h2 h3 hsp) (by taint_decide)

theorem initS_ct : ConstantTime isa (initRISCV64 s).pre (initRISCV64 s).pub
    (Impl.Blake2.RISCV64.Stream.init s) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3])
    (fun _ _ _ _ ⟨h0, h1, h2, h3, hsp⟩ => agree4 h0 h1 h2 h3 hsp) (by taint_decide)

theorem updateScratchB_ct : ConstantTime isa (updateRISCV64 b).pre (updateRISCV64 b).pub
    (Impl.Blake2.RISCV64.Stream.updateScratch b) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4])
    (fun _ _ _ _ ⟨h0, h1, h2, h3, h4, hsp⟩ => agree5 h0 h1 h2 h3 h4 hsp) (by taint_decide)

theorem updateB_ct : ConstantTime isa (updateFramedRISCV64 b).pre (updateFramedRISCV64 b).pub
    (Impl.Blake2.RISCV64.Stream.update b) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3])
    (fun _ _ _ _ ⟨h0, h1, h2, h3, hsp⟩ => agree4 h0 h1 h2 h3 hsp) (by taint_decide)

theorem updateS_ct : ConstantTime isa (updateFramedRISCV64 s).pre (updateFramedRISCV64 s).pub
    (Impl.Blake2.RISCV64.Stream.update s) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3])
    (fun _ _ _ _ ⟨h0, h1, h2, h3, hsp⟩ => agree4 h0 h1 h2 h3 hsp) (by taint_decide)

theorem finalizeScratchB_ct : ConstantTime isa (finalizeRISCV64 b).pre (finalizeRISCV64 b).pub
    (Impl.Blake2.RISCV64.Stream.finalizeScratch b) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3])
    (fun _ _ _ _ ⟨h0, h1, h2, h3, hsp⟩ => agree4 h0 h1 h2 h3 hsp) (by taint_decide)

theorem finalizeB_ct : ConstantTime isa (finalizeFramedRISCV64 b).pre (finalizeFramedRISCV64 b).pub
    (Impl.Blake2.RISCV64.Stream.finalize b) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2])
    (fun _ _ _ _ ⟨h0, h1, h2, hsp⟩ => by
      refine ⟨hsp, fun r hr => ?_⟩
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [h0, h1, h2]) (by taint_decide)

theorem finalizeS_ct : ConstantTime isa (finalizeFramedRISCV64 s).pre (finalizeFramedRISCV64 s).pub
    (Impl.Blake2.RISCV64.Stream.finalize s) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2])
    (fun _ _ _ _ ⟨h0, h1, h2, hsp⟩ => by
      refine ⟨hsp, fun r hr => ?_⟩
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [h0, h1, h2]) (by taint_decide)

end VG.Proof.Blake2.RISCV64.Stream
