module

import VerifiedGarbage.Proof.Ed448.PPC64LE.VMain
public import VerifiedGarbage.Spec.Ed448.Contract
public import VerifiedGarbage.Proof.Ed448.Contract
import VerifiedGarbage.Proof.Ed448.PPC64LE.VCT
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Impl.Ed448.PPC64LE.VerifyEquation
public import VerifiedGarbage.Proof.Ed448.Ref
public import VerifiedGarbage.Proof.X448.PPC64LE.Ladder
public import VerifiedGarbage.TCB.PPC64LE.Target

/-!
# `vg_ed448_verify_equation` on PPC64LE, verified

The function meets its contract of `Spec/Ed448/Contract.lean`, with no
stack: the proof against `verifyPPC`, which it implies, and a state
satisfying it. The code writes no nonvolatile register and never writes the
link register or calls a function, so the ABI's obligations hold of every
execution. It is constant time with only the pointers public, which the
contract's public inputs imply.
-/

@[expose] public section

namespace VG.Proof.Ed448.PPC64LE

open VG VG.PPC64LE

/-- `verifyEquationContract` by register. -/
def verifyPPC : Contract isa where
  pre s :=
    let pk : Region := ⟨s.gpr .r3, 57⟩
    let sig : Region := ⟨s.gpr .r4, 114⟩
    let ch : Region := ⟨s.gpr .r5, 57⟩
    let ws : Region := ⟨s.gpr .r6, 8192⟩
    s.rd = [pk, sig, ch] ∧ s.wr = [ws] ∧ pk.Disjoint ws ∧ sig.Disjoint ws ∧ ch.Disjoint ws
  post s s' := (s'.gpr .r3).setWidth 32 = if Spec.Ed448.verifyEquation (Spec.Ed448.bytesAt s.mem (s.gpr .r3) 57)
    (Spec.Ed448.bytesAt s.mem (s.gpr .r4) 114) (Spec.Ed448.bytesAt s.mem (s.gpr .r5) 57) then 1 else 0
  pub s₁ s₂ := s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.sp = s₂.sp ∧
    (Spec.Ed448.bytesAt s₁.mem (s₁.gpr .r3) 57 ++ Spec.Ed448.bytesAt s₁.mem (s₁.gpr .r4) 114 ++
      Spec.Ed448.bytesAt s₁.mem (s₁.gpr .r5) 57).map (·.toNat) =
    (Spec.Ed448.bytesAt s₂.mem (s₂.gpr .r3) 57 ++ Spec.Ed448.bytesAt s₂.mem (s₂.gpr .r4) 114 ++
      Spec.Ed448.bytesAt s₂.mem (s₂.gpr .r5) 57).map (·.toNat)

theorem verifyEquation_ok (hR : Proof.Ed448.RecoverOk) (hV : Proof.Ed448.VerifyEq4Ok) (s : State)
    (hs : verifyPPC.pre s) :
    ∃ t s', Exec isa Impl.Ed448.PPC64LE.verifyEquation s t s' ∧ abiPreserved s s' ∧ verifyPPC.post s s' := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hs
  obtain ⟨t, s', he, h⟩ := verifyEquation_correct hR hV ⟨h1, h2, h3, h4, h5⟩
  have hd : ∀ r ∈ preserved, ∀ i ∈ instrs Impl.Ed448.PPC64LE.verifyEquation, dstOf i ≠ some r := by
    have h : ((instrs Impl.Ed448.PPC64LE.verifyEquation).all fun i =>
        preserved.all fun r => dstOf i != some r) = true := by
      rw [← Code.allInstrs_eq]; decide +kernel
    intro r hr i hi
    have := List.all_eq_true.mp (List.all_eq_true.mp h i hi) r hr
    simpa using this
  exact ⟨t, s', he, ⟨fun r hr => Exec.gpr (hd r hr) he (.inl (by decide +kernel)), Exec.sp he,
    Exec.lr he (by decide +kernel) (by rw [← Code.allInstrs_eq]; decide +kernel)⟩, h⟩

/-- A state satisfying the precondition. -/
def verifySat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 0x3000 | .r6 => 0x4000 | _ => 0
  lr := 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x1000, 57⟩, ⟨0x2000, 114⟩, ⟨0x3000, 57⟩]
  wr := [⟨0x4000, 8192⟩]

theorem verifyEquation_verified (hR : Proof.Ed448.RecoverOk) (hV : Proof.Ed448.VerifyEq4Ok) :
    Verified PPC64LE.target Impl.Ed448.PPC64LE.verifyEquation (Proof.Ed448.verifyEquationContract PPC64LE.abi) :=
  Verified.of_correct (verifyEquation_ok hR hV)
    (verifyEquation_ct fun _ _ _ _ ⟨h3, h4, h5, h6, hsp, _⟩ => ⟨hsp, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption⟩) (by
    contract_implies [Proof.Ed448.verifyEquationContract, Proof.Ed448.verifyEquationSig, verifyPPC,
      Spec.Ed448.scratchWords, PPC64LE.abi, PPC64LE.argRegs] [verifySat] using verifySat)

end VG.Proof.Ed448.PPC64LE
