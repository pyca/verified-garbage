module

import VerifiedGarbage.Proof.Ed25519.RISCV64.ScalarMulAdd
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RISCV64.Keep
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Impl.Ed25519.RISCV64.Scalar
public import VerifiedGarbage.Spec.Ed25519.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Ed25519.RISCV64.ScalarReduce
import VerifiedGarbage.Proof.Framework.RISCV64.Taint

/-!
# Ed25519's scalar functions on RISC-V, verified

Each function meets its shared contract of `Spec/Ed25519/Contract.lean`: the
proof against a contract by register (`reduceRISCV64`, `mulAddRISCV64`),
which the shared one implies, and a state satisfying it. The functions call
no function and write only caller-saved registers (`WP.keep`), so the ABI's
obligations hold of every execution.
-/

@[expose] public section

namespace VG.Proof.Ed25519.RISCV64

open VG VG.RISCV64

/-- `scalarReduceContract` by register. -/
def reduceRISCV64 : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .a0, 32⟩
    let wide : Region := ⟨s.gpr .a1, 64⟩
    let ws : Region := ⟨s.gpr .a2, 8192⟩
    s.rd = [wide] ∧ s.wr = [out, ws] ∧ out.Disjoint wide ∧ out.Disjoint ws ∧ wide.Disjoint ws
  post s s' := Spec.Ed25519.bytesAt s'.mem (s.gpr .a0) 32 =
    Spec.Ed25519.scalarReduce (Spec.Ed25519.bytesAt s.mem (s.gpr .a1) 64)
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.sp = s₂.sp

theorem reduce_ok' (s : State) (hs : reduceRISCV64.pre s) :
    ∃ t s', VG.Exec isa Impl.Ed25519.RISCV64.scalarReduce s t s' ∧ abiPreserved s s' ∧
      reduceRISCV64.post s s' := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hs
  obtain ⟨t, s', he, hb, hk⟩ := WP.keep [.a1, .a2, .a3, .a4, .a5, .a6, .a7, .t0, .t1, .t2, .t3, .t4, .t5, .t6]
    (reduce_ok ⟨h1, h2, h3, h4, h5⟩) (by decide +kernel)
  exact ⟨t, s', he, abiPreserved_of_keep he hk (by decide) (by decide), hb⟩

/-- `scalarMulAddContract` by register. -/
def mulAddRISCV64 : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .a0, 32⟩
    let r : Region := ⟨s.gpr .a1, 32⟩
    let k : Region := ⟨s.gpr .a2, 32⟩
    let a : Region := ⟨s.gpr .a3, 32⟩
    let ws : Region := ⟨s.gpr .a4, 8192⟩
    s.rd = [r, k, a] ∧ s.wr = [out, ws] ∧ out.Disjoint ws ∧ r.Disjoint ws ∧ k.Disjoint ws ∧ a.Disjoint ws
  post s s' := Spec.Ed25519.bytesAt s'.mem (s.gpr .a0) 32 =
    Spec.Ed25519.scalarMulAdd (Spec.Ed25519.bytesAt s.mem (s.gpr .a1) 32)
      (Spec.Ed25519.bytesAt s.mem (s.gpr .a2) 32) (Spec.Ed25519.bytesAt s.mem (s.gpr .a3) 32)
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.sp = s₂.sp

theorem mulAdd_ok' (s : State) (hs : mulAddRISCV64.pre s) :
    ∃ t s', VG.Exec isa Impl.Ed25519.RISCV64.scalarMulAdd s t s' ∧ abiPreserved s s' ∧
      mulAddRISCV64.post s s' := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hs
  obtain ⟨t, s', he, hb, hk⟩ := WP.keep [.a1, .a2, .a3, .a4, .a5, .a6, .a7, .t0, .t1, .t2, .t3, .t4, .t5, .t6]
    (mulAdd_ok ⟨h1, h2, h3, h4, h5, h6⟩) (by decide +kernel)
  exact ⟨t, s', he, abiPreserved_of_keep he hk (by decide) (by decide), hb⟩

end VG.Proof.Ed25519.RISCV64
