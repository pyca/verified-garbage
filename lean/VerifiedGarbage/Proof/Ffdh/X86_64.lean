module

public import VerifiedGarbage.Spec.Ffdh.Contract
import VerifiedGarbage.Proof.Ffdh.Choose
import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Impl.Ffdh.X86_64
import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

@[expose] public section

namespace VG.Proof.Ffdh.X86_64
open VG VG.X86_64 VG.Proof.MlKem.X86_64

def contract : Contract isa where
  pre _ := True
  post s t := t.gpr .rax = Spec.Ffdh.choose (s.gpr .rdi) (s.gpr .rsi) (s.gpr .rdx) ∧ t.mem = s.mem
  pub _ _ := True

theorem correct (s : State) (_ : contract.pre s) :
    ∃ tr t, Exec isa Impl.Ffdh.X86_64.choose s tr t ∧ abiPreserved s t ∧ contract.post s t := by
  have h : WP isa Impl.Ffdh.X86_64.choose s (fun t =>
      t.gpr .rax = Spec.Ffdh.choose (s.gpr .rdi) (s.gpr .rsi) (s.gpr .rdx) ∧ t.mem = s.mem) := by
    unfold Impl.Ffdh.X86_64.choose Spec.Ffdh.choose
    xrun []
    exact BitVec.xor_comm _ _
  obtain ⟨tr, t, he, ho, hk⟩ := WP.keep [.rax, .rdx, .rcx] h (by rfl)
  refine ⟨tr, t, he, abiPreserved_of_exec (by decide +kernel) he ?_, ho⟩
  exact ⟨fun r hr => hk.gpr (by revert r; decide), by rw [ho.2]⟩

theorem ct : ConstantTime isa contract.pre contract.pub Impl.Ffdh.X86_64.choose := by
  refine ConstantTime.of_silent fun s tr t _ h => ?_
  rw [Impl.Ffdh.X86_64.choose, Exec.block_iff] at h
  cases h
  rfl

def sat : State where
  gpr _ := 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := []
  wr := []

theorem verified : Verified target Impl.Ffdh.X86_64.choose (Spec.Ffdh.chooseContract abi) :=
  Verified.of_correct correct ct (by
    sig_implies [Spec.Ffdh.chooseContract, Spec.Ffdh.chooseSig, contract, abi, argRegs] [sat] using sat)

/-- The mask expression really selects by the low bit, for all words. -/
theorem choose_low_bit (a b bit : BitVec 64) :
    Spec.Ffdh.choose a b bit = if bit &&& 1 = 0 then a else b :=
  VG.Proof.Ffdh.choose_low_bit a b bit
end VG.Proof.Ffdh.X86_64
