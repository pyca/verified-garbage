import VerifiedGarbage.Proof.Idea.X86_64.Ecb
import VerifiedGarbage.Proof.Idea.Scratch
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
import VerifiedGarbage.Impl.StackScratch.X86_64

/-!
# Verified IDEA ECB on x86-64

`ecb_verified` against the contract with the scratch buffer as an argument,
and `ecb_framed` against the shared contract, with the buffer in a frame of
24 bytes on the stack (8 for the return address the scratch contract keeps
out of its buffers, 16 for `rbx` and `rbp`). The buffer only ever holds the
caller's `rbx` and `rbp`, so it is not zeroed.
-/

namespace VG.Proof.Idea.X86_64

open VG VG.X86_64 VG.Impl.Idea.X86_64

theorem ecb_correct (s : State) (hs : contract.pre s) :
    ∃ t s', Exec isa ecb s t s' ∧ abiPreserved s s' ∧ contract.post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := ecb_wp s hs
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he ha, hp⟩

def satState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 1 | .rcx => 0x3000 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 104⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, 16⟩]

theorem publicRegs_four (s₁ s₂ : State) : PublicRegs [.rdi, .rsi, .rdx, .rcx] s₁ s₂ ↔
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx := by
  simp [PublicRegs]

theorem ecb_verified : Verified target ecb (Proof.Idea.ecbScratchContract abi) := by
  refine Verified.of_correct ecb_correct (ecb_constantTime _) ?_
  sig_implies [Proof.Idea.ecbScratchContract, Proof.Idea.ecbScratchSig, Spec.Idea.ecbPost, abi,
    argRegs, contract, publicRegs_four] [satState] using satState

theorem ecb_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratch 24 .rcx ecb)
      (Spec.Idea.ecbContract X86_64.abi 24) :=
  X86_64.Verified.stackScratch (sig := Spec.Idea.ecbSig) (nm := "scratch") (e := .u64) (n := 2)
    (post := Spec.Idea.ecbPost X86_64.abi.ptrBits) (wa := false) (stack := 0) (bytes := 24)
    ecb_verified (by decide) (by decide) (by decide) (Code.all_of_allInstrs (by lit_decide))
    (by lit_decide)
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

end VG.Proof.Idea.X86_64
