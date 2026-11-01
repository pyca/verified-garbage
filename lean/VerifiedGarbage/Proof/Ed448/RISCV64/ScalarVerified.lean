module

import VerifiedGarbage.Proof.Ed448.RISCV64.ScalarMulAdd
import VerifiedGarbage.Proof.Ed448.RISCV64.ScalarCT
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RISCV64.Keep
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Impl.Ed448.RISCV64.Scalar
public import VerifiedGarbage.Spec.Ed448.Contract
public import VerifiedGarbage.Proof.Ed448.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Ed448.RISCV64.ScalarReduce

/-!
# Ed448's scalar functions on RISC-V, verified

Each function meets its shared contract of `Spec/Ed448/Contract.lean`: the
proof against a contract by register (`reduceRISCV64`, `mulAddRISCV64`),
which the shared one implies, and a state satisfying it. The functions call
no function and write only caller-saved registers (`WP.keep`), so the ABI's
obligations hold of every execution.
-/

@[expose] public section

namespace VG.Proof.Ed448.RISCV64

open VG VG.RISCV64

/-- `scalarReduceContract` by register. -/
def reduceRISCV64 : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .a0, 57⟩
    let wide : Region := ⟨s.gpr .a1, 114⟩
    let ws : Region := ⟨s.gpr .a2, 8192⟩
    s.rd = [wide] ∧ s.wr = [out, ws] ∧ out.Disjoint wide ∧ out.Disjoint ws ∧ wide.Disjoint ws
  post s s' := Spec.Ed448.bytesAt s'.mem (s.gpr .a0) 57 =
    Spec.Ed448.scalarReduce (Spec.Ed448.bytesAt s.mem (s.gpr .a1) 114)
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.sp = s₂.sp

theorem reduce_ok' (s : State) (hs : reduceRISCV64.pre s) :
    ∃ t s', VG.Exec isa Impl.Ed448.RISCV64.scalarReduce s t s' ∧ abiPreserved s s' ∧
      reduceRISCV64.post s s' := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hs
  obtain ⟨t, s', he, hb, hk⟩ := WP.keep [.a2, .a3, .a4, .a5, .a6, .a7, .t0, .t3, .t4, .t5]
    (reduce_ok ⟨h1, h2, h3, h4, h5⟩) (by decide +kernel)
  exact ⟨t, s', he, abiPreserved_of_keep he hk (by decide) (by decide), hb⟩

/-- A state satisfying the precondition. -/
def reduceSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a2 => 0x4000 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x2000, 114⟩]
  wr := [⟨0x1000, 57⟩, ⟨0x4000, 8192⟩]

theorem scalarReduce_verified :
    Verified RISCV64.target Impl.Ed448.RISCV64.scalarReduce (Proof.Ed448.scalarReduceContract RISCV64.abi) :=
  Verified.of_correct reduce_ok' (scalarReduce_ct fun _ _ _ _ ⟨h3, h4, h5, hsp⟩ => ⟨hsp, fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> with_reducible assumption⟩) (by
    contract_implies [Proof.Ed448.scalarReduceContract, Proof.Ed448.scalarReduceSig, reduceRISCV64,
      Spec.Ed448.scratchWords, RISCV64.abi, RISCV64.argRegs] [reduceSat] using reduceSat)

/-- `scalarMulAddContract` by register. -/
def mulAddRISCV64 : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .a0, 57⟩
    let r : Region := ⟨s.gpr .a1, 57⟩
    let k : Region := ⟨s.gpr .a2, 57⟩
    let a : Region := ⟨s.gpr .a3, 57⟩
    let ws : Region := ⟨s.gpr .a4, 8192⟩
    s.rd = [r, k, a] ∧ s.wr = [out, ws] ∧ out.Disjoint ws ∧ r.Disjoint ws ∧ k.Disjoint ws ∧ a.Disjoint ws
  post s s' := Spec.Ed448.bytesAt s'.mem (s.gpr .a0) 57 =
    Spec.Ed448.scalarMulAdd (Spec.Ed448.bytesAt s.mem (s.gpr .a1) 57)
      (Spec.Ed448.bytesAt s.mem (s.gpr .a2) 57) (Spec.Ed448.bytesAt s.mem (s.gpr .a3) 57)
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.sp = s₂.sp

theorem mulAdd_ok' (s : State) (hs : mulAddRISCV64.pre s) :
    ∃ t s', VG.Exec isa Impl.Ed448.RISCV64.scalarMulAdd s t s' ∧ abiPreserved s s' ∧
      mulAddRISCV64.post s s' := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hs
  obtain ⟨t, s', he, hb, hk⟩ := WP.keep [.a1, .a2, .a3, .a4, .a5, .a6, .a7, .t0, .t2, .t3, .t4, .t5, .t6]
    (mulAdd_ok ⟨h1, h2, h3, h4, h5, h6⟩) (by decide +kernel)
  exact ⟨t, s', he, abiPreserved_of_keep he hk (by decide) (by decide), hb⟩

/-- A state satisfying the precondition. -/
def mulAddSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a2 => 0x2100 | .a3 => 0x2200 | .a4 => 0x4000 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x2000, 57⟩, ⟨0x2100, 57⟩, ⟨0x2200, 57⟩]
  wr := [⟨0x1000, 57⟩, ⟨0x4000, 8192⟩]

theorem scalarMulAdd_verified :
    Verified RISCV64.target Impl.Ed448.RISCV64.scalarMulAdd (Proof.Ed448.scalarMulAddContract RISCV64.abi) :=
  Verified.of_correct mulAdd_ok' (scalarMulAdd_ct fun _ _ _ _ ⟨h3, h4, h5, h6, h7, hsp⟩ => ⟨hsp, fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption⟩) (by
    contract_implies [Proof.Ed448.scalarMulAddContract, Proof.Ed448.scalarMulAddSig, mulAddRISCV64,
      Spec.Ed448.scratchWords, RISCV64.abi, RISCV64.argRegs] [mulAddSat] using mulAddSat)

end VG.Proof.Ed448.RISCV64
