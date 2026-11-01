module

import VerifiedGarbage.Proof.Ed448.RISCV64.VMain
public import VerifiedGarbage.Spec.Ed448.Contract
public import VerifiedGarbage.Proof.Ed448.Contract
import VerifiedGarbage.Proof.Ed448.RISCV64.VCT
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RISCV64.Keep
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Impl.Ed448.RISCV64.VerifyEquation
public import VerifiedGarbage.Proof.Ed448.Ref
public import VerifiedGarbage.TCB.RISCV64.Target

/-!
# `vg_ed448_verify_equation` on RISC-V, verified

The function meets its contract of `Spec/Ed448/Contract.lean`, with no
stack: the proof against `verifyRISCV64`, which it implies, and a state
satisfying it. The code calls no function and writes only caller-saved
registers (`WP.keep`), so the ABI's obligations hold of every execution. It
is constant time with only the pointers public, which the contract's public
inputs imply.
-/

@[expose] public section

namespace VG.Proof.Ed448.RISCV64

open VG VG.RISCV64

/-- `verifyEquationContract` by register. -/
def verifyRISCV64 : Contract isa where
  pre s :=
    let pk : Region := ⟨s.gpr .a0, 57⟩
    let sig : Region := ⟨s.gpr .a1, 114⟩
    let ch : Region := ⟨s.gpr .a2, 57⟩
    let ws : Region := ⟨s.gpr .a3, 8192⟩
    s.rd = [pk, sig, ch] ∧ s.wr = [ws] ∧ pk.Disjoint ws ∧ sig.Disjoint ws ∧ ch.Disjoint ws
  post s s' := (s'.gpr .a0).setWidth 32 = if Spec.Ed448.verifyEquation (Spec.Ed448.bytesAt s.mem (s.gpr .a0) 57)
    (Spec.Ed448.bytesAt s.mem (s.gpr .a1) 114) (Spec.Ed448.bytesAt s.mem (s.gpr .a2) 57) then 1 else 0
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.sp = s₂.sp ∧
    (Spec.Ed448.bytesAt s₁.mem (s₁.gpr .a0) 57 ++ Spec.Ed448.bytesAt s₁.mem (s₁.gpr .a1) 114 ++
      Spec.Ed448.bytesAt s₁.mem (s₁.gpr .a2) 57).map (·.toNat) =
    (Spec.Ed448.bytesAt s₂.mem (s₂.gpr .a0) 57 ++ Spec.Ed448.bytesAt s₂.mem (s₂.gpr .a1) 114 ++
      Spec.Ed448.bytesAt s₂.mem (s₂.gpr .a2) 57).map (·.toNat)

theorem verifyEquation_ok (hR : Proof.Ed448.RecoverOk) (hV : Proof.Ed448.VerifyEq4Ok) (s : State)
    (hs : verifyRISCV64.pre s) :
    ∃ t s', Exec isa Impl.Ed448.RISCV64.verifyEquation s t s' ∧ abiPreserved s s' ∧ verifyRISCV64.post s s' := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hs
  obtain ⟨t, s', he, h, hk⟩ := WP.keep [.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7, .t0, .t1, .t2, .t3, .t4, .t5, .t6]
    (verifyEquation_correct hR hV ⟨h1, h2, h3, h4, h5⟩) (by decide +kernel)
  exact ⟨t, s', he, abiPreserved_of_keep he hk (by decide) (by decide), h⟩

/-- A state satisfying the precondition. -/
def verifySat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a2 => 0x3000 | .a3 => 0x4000 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x1000, 57⟩, ⟨0x2000, 114⟩, ⟨0x3000, 57⟩]
  wr := [⟨0x4000, 8192⟩]

theorem verifyEquation_verified (hR : Proof.Ed448.RecoverOk) (hV : Proof.Ed448.VerifyEq4Ok) :
    Verified RISCV64.target Impl.Ed448.RISCV64.verifyEquation (Proof.Ed448.verifyEquationContract RISCV64.abi) :=
  Verified.of_correct (verifyEquation_ok hR hV)
    (verifyEquation_ct fun _ _ _ _ ⟨h3, h4, h5, h6, hsp, _⟩ => ⟨hsp, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption⟩) (by
    contract_implies [Proof.Ed448.verifyEquationContract, Proof.Ed448.verifyEquationSig, verifyRISCV64,
      Spec.Ed448.scratchWords, RISCV64.abi, RISCV64.argRegs] [verifySat] using verifySat)

end VG.Proof.Ed448.RISCV64
