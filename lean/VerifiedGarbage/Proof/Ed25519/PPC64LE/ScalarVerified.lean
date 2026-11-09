module

import VerifiedGarbage.Proof.Ed25519.PPC64LE.ScalarMulAdd
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Impl.Ed25519.PPC64LE.Scalar
public import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
public import VerifiedGarbage.Spec.Ed25519.Contract
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Framework.PPC64LE.Taint

/-!
# `vg_ed25519_scalar_reduce` and `vg_ed25519_scalar_mul_add` on PPC64LE, verified

Each function meets its contract of `Spec/Ed25519/Contract.lean`, with no
stack: the proof against the contract's facts by register (`reducePPC`,
`mulAddPPC`), which it implies, and a state satisfying it. The functions save
and restore the nonvolatile registers they write (`reduce_ok`, `mulAdd_ok`),
and never write the link register or call another.
-/

@[expose] public section

namespace VG.Proof.Ed25519.PPC64LE

open VG VG.PPC64LE

/-- `scalarReduceContract` by register. -/
def reducePPC : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .r3, 32⟩
    let wide : Region := ⟨s.gpr .r4, 64⟩
    let ws : Region := ⟨s.gpr .r5, 8192⟩
    s.rd = [wide] ∧ s.wr = [out, ws] ∧ out.Disjoint wide ∧ out.Disjoint ws ∧ wide.Disjoint ws
  post s s' := Spec.Ed25519.bytesAt s'.mem (s.gpr .r3) 32 =
    Spec.Ed25519.scalarReduce (Spec.Ed25519.bytesAt s.mem (s.gpr .r4) 64)
  pub s₁ s₂ := s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.sp = s₂.sp

theorem reduce_ok' (s : State) (hs : reducePPC.pre s) :
    ∃ t s', VG.Exec isa Impl.Ed25519.PPC64LE.scalarReduce s t s' ∧ abiPreserved s s' ∧
      reducePPC.post s s' := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hs
  obtain ⟨t, s', he, hg, hsp, hb⟩ := reduce_ok ⟨h1, h2, h3, h4, h5⟩
  exact ⟨t, s', he, ⟨hg, hsp, Exec.lr he (by decide +kernel) (by rw [← Code.allInstrs_eq]; decide +kernel)⟩, hb⟩

/-- `scalarMulAddContract` by register. -/
def mulAddPPC : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .r3, 32⟩
    let r : Region := ⟨s.gpr .r4, 32⟩
    let k : Region := ⟨s.gpr .r5, 32⟩
    let a : Region := ⟨s.gpr .r6, 32⟩
    let ws : Region := ⟨s.gpr .r7, 8192⟩
    s.rd = [r, k, a] ∧ s.wr = [out, ws] ∧ out.Disjoint ws ∧ r.Disjoint ws ∧ k.Disjoint ws ∧ a.Disjoint ws
  post s s' := Spec.Ed25519.bytesAt s'.mem (s.gpr .r3) 32 =
    Spec.Ed25519.scalarMulAdd (Spec.Ed25519.bytesAt s.mem (s.gpr .r4) 32)
      (Spec.Ed25519.bytesAt s.mem (s.gpr .r5) 32) (Spec.Ed25519.bytesAt s.mem (s.gpr .r6) 32)
  pub s₁ s₂ := s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.sp = s₂.sp

theorem mulAdd_ok' (s : State) (hs : mulAddPPC.pre s) :
    ∃ t s', VG.Exec isa Impl.Ed25519.PPC64LE.scalarMulAdd s t s' ∧ abiPreserved s s' ∧
      mulAddPPC.post s s' := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hs
  obtain ⟨t, s', he, hg, hsp, hb⟩ := mulAdd_ok ⟨h1, h2, h3, h4, h5, h6⟩
  exact ⟨t, s', he, ⟨hg, hsp, Exec.lr he (by decide +kernel) (by rw [← Code.allInstrs_eq]; decide +kernel)⟩, hb⟩

end VG.Proof.Ed25519.PPC64LE
