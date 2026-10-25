module

import VerifiedGarbage.Proof.TripleDes.RISCV64.Key.Body
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Spec.TripleDes.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Framework.RISCV64.Keep
public import VerifiedGarbage.Impl.TripleDes.RISCV64.ExpandKey
import VerifiedGarbage.Proof.TripleDes.KeyMemory
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.TripleDes.RISCV64.FunctionsLit
meta import VerifiedGarbage.Proof.TripleDes.RISCV64.Key.Body
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Spec.TripleDes.Contract
meta import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.Proof.Framework.RISCV64.Keep
meta import VerifiedGarbage.Impl.TripleDes.RISCV64.ExpandKey
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.TripleDes.RISCV64.FunctionsLit

/-!
# Triple DES key expansion on RISC-V, verified

The code writes only temporaries and argument registers and needs no
working space, so it is verified against `expandKeyContract` with no stack.
-/

@[expose] public section

namespace VG.Proof.TripleDes.RISCV64.Key

open VG VG.RISCV64

def contract : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .a0, (s.gpr .a1).toNat⟩
    let output : Region := ⟨s.gpr .a2, 384⟩
    s.rd = [key] ∧ s.wr = [output] ∧ key.Disjoint output ∧
      Spec.TripleDes.validKey (s.gpr .a1).toNat
  post s s' := Spec.TripleDes.scheduleAt s'.mem (s.gpr .a2) =
    Spec.TripleDes.expandKey (Spec.TripleDes.bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat)
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.sp = s₂.sp

/-- The registers the code writes: temporaries and argument registers. -/
def written : List Reg := [.t0, .t1, .t2, .t3, .t4, .a3, .a4, .a5, .a6]

theorem expand_wp (s : State) (hs : contract.pre s) :
    WP isa Impl.TripleDes.RISCV64.Key.expandKey s (contract.post s) := by
  obtain ⟨hrd, hwr, keyOutput, valid⟩ := hs
  have hp : Permissions s := by
    constructor
    · intro offset hoff
      rw [hrd, hwr]
      exact ⟨⟨s.gpr .a0, (s.gpr .a1).toNat⟩, by simp,
        Offset.contains_base _ hoff (by
          have bound := BitVec.isLt (s.gpr .a1)
          omega_using [hoff, bound])⟩
    · intro offset hoff
      rw [hwr]
      exact ⟨⟨s.gpr .a2, 384⟩, by simp, Offset.contains_base _ hoff (by omega_using [hoff])⟩
    · exact keyOutput
    · exact valid
  apply WP.mono (body_ok s s hp ⟨fun _ h => by omega, rfl, rfl, rfl, fun _ _ => rfl,
    Frame.refl _ _⟩)
  intro s₂ h₂
  have result := h₂.schedule
  rw [← VG.Proof.TripleDes.expandKey_memory s.mem (s.gpr .a0) (s.gpr .a1).toNat valid] at result
  exact result

theorem correct (hw : writesOnly written Impl.TripleDes.RISCV64.Key.expandKey = true)
    (hn : callFree Impl.TripleDes.RISCV64.Key.expandKey = true) (s : State) (hs : contract.pre s) :
    ∃ t s', Exec isa Impl.TripleDes.RISCV64.Key.expandKey s t s' ∧ abiPreserved s s' ∧
      contract.post s s' := by
  obtain ⟨t, s', he, hp, hk⟩ := WP.keep written (expand_wp s hs) hw hn
  exact ⟨t, s', he, abiPreserved_of_keep he hk (by decide) (by decide), hp⟩

theorem key_agree : ∀ s₁ s₂, contract.pre s₁ → contract.pre s₂ → contract.pub s₁ s₂ →
    taint.Agree (Taint.ofRegs [.a0, .a1, .a2]) s₁ s₂ := by
  intro s₁ s₂ _ _ h
  refine ⟨h.2.2.2, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1

theorem constantTime : ConstantTime isa contract.pre contract.pub
    Impl.TripleDes.RISCV64.Key.expandKey :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2]) key_agree (by taint_decide)

def satState : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 16 | .a2 => 0x2000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 384⟩]

theorem verified : Verified RISCV64.target Impl.TripleDes.RISCV64.Key.expandKey
    (Spec.TripleDes.expandKeyContract RISCV64.abi) := by
  refine Verified.of_correct (k := contract) (correct (by lit_decide) (by lit_decide)) constantTime ?_
  contract_implies [Spec.TripleDes.expandKeyContract, Spec.TripleDes.expandKeySig,
    Spec.TripleDes.expandKeyPre, Spec.TripleDes.expandKeyPost, Spec.TripleDes.validKey,
    RISCV64.abi, RISCV64.argRegs, contract] [satState] using satState

end VG.Proof.TripleDes.RISCV64.Key
