module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.RISCV64.Contract
public import VerifiedGarbage.Impl.ChaCha20Poly1305.RISCV64
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.RISCV64.Contract
meta import VerifiedGarbage.Impl.ChaCha20Poly1305.RISCV64
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Poly1305.RISCV64.Lit
meta import VerifiedGarbage.Proof.Poly1305.RISCV64.Lit

/-!
# ChaCha20-Poly1305 on RISC-V: constant time

The taint analysis of the whole of each function, through its callees: the
values it keeps in `s7`–`s11`, which no callee writes, and the context in
`a0`, which no callee writes either, stay public across the calls.
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.RISCV64

open VG VG.RISCV64

theorem agree₀ {s₁ s₂ : State} (hpub : pubRISCV64 s₁ s₂) :
    VG.RISCV64.Taint.Agree (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7]) s₁ s₂ := by
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, hsp⟩ := hpub
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem seal_ct :
    ConstantTime isa sealRISCV64.pre sealRISCV64.pub Impl.ChaCha20Poly1305.RISCV64.«seal» :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7])
    (fun _ _ _ _ hp => agree₀ hp) (by taint_decide)

theorem open_ct :
    ConstantTime isa openRISCV64.pre openRISCV64.pub Impl.ChaCha20Poly1305.RISCV64.«open» :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7])
    (fun _ _ _ _ hp => agree₀ hp) (by taint_decide)

end VG.Proof.ChaCha20Poly1305.RISCV64
