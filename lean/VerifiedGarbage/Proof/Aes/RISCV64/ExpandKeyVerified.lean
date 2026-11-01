module

public import VerifiedGarbage.Proof.Aes.RISCV64.ExpandKey
public import VerifiedGarbage.Spec.Aes.Contract
public import VerifiedGarbage.Proof.Aes.Contract
meta import VerifiedGarbage.Proof.Aes.Contract
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.Aes.RISCV64.CodeLit
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Aes.RISCV64.ExpandKey
meta import VerifiedGarbage.Proof.Aes.RISCV64.CodeLit
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Aes.Contract
meta import VerifiedGarbage.TCB.RISCV64.Target

/-!
# The AES key expansion on RISC-V: `Verified`

Correctness (`ExpandKey.lean`), constant time (by taint tracking,
`taint_decide`: only the pointers, `key_len` and what is computed from them
reach addresses and branches), and a state satisfying the precondition,
against `Proof.Aes.expandKeyRISCV64`, then moved to the shared contract of
`Spec/Aes/Contract.lean`.
-/

@[expose] public section

namespace VG.Proof.Aes.RISCV64

open VG VG.RISCV64 VG.Impl.Aes.RISCV64 VG.Proof.Aes

theorem expandKey_correct (s : State) (hs : Proof.Aes.expandKeyRISCV64.pre s) :
    ∃ t s', Exec isa expandKey s t s' ∧ abiPreserved s s' ∧ Proof.Aes.expandKeyRISCV64.post s s' := by
  obtain ⟨t, s', he, h₁, hra, h₂⟩ := ek_correct hs
  exact ⟨t, s', he, ⟨h₁, Exec.sp he, hra⟩, h₂⟩

theorem expandKey_ct : ConstantTime isa Proof.Aes.expandKeyRISCV64.pre Proof.Aes.expandKeyRISCV64.pub
    expandKey := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3]) ?_ (by taint_decide)
  rintro s₁ s₂ - - ⟨h0, h1, h2, h3, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  exacts [h0, h1, h2, h3]

/-- A state satisfying the precondition. -/
def ekSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 16 | .a2 => 0x2000 | .a3 => 0x3000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 240⟩, ⟨0x3000, 512⟩]

theorem expandKey_verified :
    Verified RISCV64.target expandKey (Proof.Aes.expandKeyScratchContract RISCV64.abi) :=
  Verified.of_correct expandKey_correct expandKey_ct (by
    sig_implies [Proof.Aes.expandKeyScratchContract, Proof.Aes.expandKeyScratchSig,
      Proof.Aes.expandKeyRISCV64, RISCV64.abi, RISCV64.argRegs] [ekSat] using ekSat)

end VG.Proof.Aes.RISCV64
