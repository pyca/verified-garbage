module

import VerifiedGarbage.Proof.Ed25519.PPC64LE.ScalarBase
import VerifiedGarbage.Proof.Ed25519.PPC64LE.ScalarBaseCT
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Impl.Ed25519.PPC64LE.ScalarBase
public import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
public import VerifiedGarbage.Spec.Ed25519.Contract
public import VerifiedGarbage.Proof.Ed25519.Contract
public import VerifiedGarbage.TCB.PPC64LE.Target

/-!
# `vg_ed25519_scalar_base` on PPC64LE, verified

The function meets its contract of `Spec/Ed25519/Contract.lean`, with no
stack: the proof against the contract's facts by register (`basePPC`), which
it implies, and a state satisfying it. The function saves and restores the
nonvolatile registers it writes, and the link register, which its calls
overwrite (`scalarBase_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.PPC64LE

open VG VG.PPC64LE

/-- `scalarBaseContract` by register. -/
def basePPC : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .r3, 32⟩
    let sc : Region := ⟨s.gpr .r4, 32⟩
    let ws : Region := ⟨s.gpr .r5, 8192⟩
    s.rd = [sc] ∧ s.wr = [out, ws] ∧ out.Disjoint ws ∧ sc.Disjoint ws
  post s s' := Spec.Ed25519.bytesAt s'.mem (s.gpr .r3) 32 =
    Spec.Ed25519.scalarBase (Spec.Ed25519.bytesAt s.mem (s.gpr .r4) 32)
  pub s₁ s₂ := s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.sp = s₂.sp

theorem base_ok' (s : State) (hs : basePPC.pre s) :
    ∃ t s', VG.Exec isa Impl.Ed25519.PPC64LE.scalarBase s t s' ∧ abiPreserved s s' ∧
      basePPC.post s s' := by
  obtain ⟨h1, h2, h3, h4⟩ := hs
  obtain ⟨t, s', he, hg, hsp, hlr, hb⟩ := scalarBase_ok ⟨h1, h2, h3, h4⟩
  exact ⟨t, s', he, ⟨hg, hsp, hlr⟩, hb⟩

/-- A state satisfying the precondition. -/
def baseSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 0x4000 | _ => 0
  lr := 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x2000, 32⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x4000, 8192⟩]

theorem scalarBase_verified :
    Verified PPC64LE.target Impl.Ed25519.PPC64LE.scalarBase (Proof.Ed25519.scalarBaseContract PPC64LE.abi) :=
  Verified.of_correct base_ok' (scalarBase_ct fun _ _ _ _ ⟨h3, h4, h5, hsp⟩ => ⟨hsp, fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> with_reducible assumption⟩) (by
    contract_implies [Proof.Ed25519.scalarBaseContract, Proof.Ed25519.scalarBaseSig, basePPC,
      Spec.Ed25519.scratchWords, PPC64LE.abi, PPC64LE.argRegs] [baseSat] using baseSat)

end VG.Proof.Ed25519.PPC64LE
