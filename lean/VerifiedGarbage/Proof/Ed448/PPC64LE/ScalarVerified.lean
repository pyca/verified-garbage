module

import VerifiedGarbage.Proof.Ed448.PPC64LE.ScalarMulAdd
import VerifiedGarbage.Proof.Ed448.PPC64LE.ScalarCT
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Impl.Ed448.PPC64LE.Scalar
public import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
public import VerifiedGarbage.Spec.Ed448.Contract
public import VerifiedGarbage.Proof.Ed448.Contract
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Ed448.PPC64LE.ScalarReduce

/-!
# `vg_ed25519_scalar_reduce` and `vg_ed25519_scalar_mul_add` on PPC64LE, verified

Each function meets its contract of `Spec/Ed448/Contract.lean`, with no
stack: the proof against the contract's facts by register (`reducePPC`,
`mulAddPPC`), which it implies, and a state satisfying it. The functions save
and restore the nonvolatile registers they write (`reduce_ok`, `mulAdd_ok`),
and never write the link register or call another.
-/

@[expose] public section

namespace VG.Proof.Ed448.PPC64LE

open VG VG.PPC64LE

/-- `scalarReduceContract` by register. -/
def reducePPC : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .r3, 57⟩
    let wide : Region := ⟨s.gpr .r4, 114⟩
    let ws : Region := ⟨s.gpr .r5, 8192⟩
    s.rd = [wide] ∧ s.wr = [out, ws] ∧ out.Disjoint wide ∧ out.Disjoint ws ∧ wide.Disjoint ws
  post s s' := Spec.Ed448.bytesAt s'.mem (s.gpr .r3) 57 =
    Spec.Ed448.scalarReduce (Spec.Ed448.bytesAt s.mem (s.gpr .r4) 114)
  pub s₁ s₂ := s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.sp = s₂.sp

theorem reduce_ok' (s : State) (hs : reducePPC.pre s) :
    ∃ t s', VG.Exec isa Impl.Ed448.PPC64LE.scalarReduce s t s' ∧ abiPreserved s s' ∧
      reducePPC.post s s' := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hs
  obtain ⟨t, s', he, hg, hsp, hb⟩ := reduce_ok ⟨h1, h2, h3, h4, h5⟩
  exact ⟨t, s', he, ⟨hg, hsp, Exec.lr he (by decide +kernel) (by rw [← Code.allInstrs_eq]; decide +kernel)⟩, hb⟩

/-- A state satisfying the precondition. -/
def reduceSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 0x4000 | _ => 0
  lr := 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x2000, 114⟩]
  wr := [⟨0x1000, 57⟩, ⟨0x4000, 8192⟩]

theorem scalarReduce_verified :
    Verified PPC64LE.target Impl.Ed448.PPC64LE.scalarReduce (Proof.Ed448.scalarReduceContract PPC64LE.abi) :=
  Verified.of_correct reduce_ok' (scalarReduce_ct fun _ _ _ _ ⟨h3, h4, h5, hsp⟩ => ⟨hsp, fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> with_reducible assumption⟩) (by
    contract_implies [Proof.Ed448.scalarReduceContract, Proof.Ed448.scalarReduceSig, reducePPC,
      Spec.Ed448.scratchWords,
      PPC64LE.abi, PPC64LE.argRegs] [reduceSat] using reduceSat)

/-- `scalarMulAddContract` by register. -/
def mulAddPPC : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .r3, 57⟩
    let r : Region := ⟨s.gpr .r4, 57⟩
    let k : Region := ⟨s.gpr .r5, 57⟩
    let a : Region := ⟨s.gpr .r6, 57⟩
    let ws : Region := ⟨s.gpr .r7, 8192⟩
    s.rd = [r, k, a] ∧ s.wr = [out, ws] ∧ out.Disjoint ws ∧ r.Disjoint ws ∧ k.Disjoint ws ∧ a.Disjoint ws
  post s s' := Spec.Ed448.bytesAt s'.mem (s.gpr .r3) 57 =
    Spec.Ed448.scalarMulAdd (Spec.Ed448.bytesAt s.mem (s.gpr .r4) 57)
      (Spec.Ed448.bytesAt s.mem (s.gpr .r5) 57) (Spec.Ed448.bytesAt s.mem (s.gpr .r6) 57)
  pub s₁ s₂ := s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.sp = s₂.sp

theorem mulAdd_ok' (s : State) (hs : mulAddPPC.pre s) :
    ∃ t s', VG.Exec isa Impl.Ed448.PPC64LE.scalarMulAdd s t s' ∧ abiPreserved s s' ∧
      mulAddPPC.post s s' := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hs
  obtain ⟨t, s', he, hg, hsp, hb⟩ := mulAdd_ok ⟨h1, h2, h3, h4, h5, h6⟩
  exact ⟨t, s', he, ⟨hg, hsp, Exec.lr he (by decide +kernel) (by rw [← Code.allInstrs_eq]; decide +kernel)⟩, hb⟩

/-- A state satisfying the precondition. -/
def mulAddSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 0x2100 | .r6 => 0x2200 | .r7 => 0x4000 | _ => 0
  lr := 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x2000, 57⟩, ⟨0x2100, 57⟩, ⟨0x2200, 57⟩]
  wr := [⟨0x1000, 57⟩, ⟨0x4000, 8192⟩]

theorem scalarMulAdd_verified :
    Verified PPC64LE.target Impl.Ed448.PPC64LE.scalarMulAdd (Proof.Ed448.scalarMulAddContract PPC64LE.abi) :=
  Verified.of_correct mulAdd_ok' (scalarMulAdd_ct fun _ _ _ _ ⟨h3, h4, h5, h6, h7, hsp⟩ => ⟨hsp, fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption⟩) (by
    contract_implies [Proof.Ed448.scalarMulAddContract, Proof.Ed448.scalarMulAddSig, mulAddPPC,
      Spec.Ed448.scratchWords, PPC64LE.abi, PPC64LE.argRegs] [mulAddSat] using mulAddSat)

end VG.Proof.Ed448.PPC64LE
