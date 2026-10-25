module

public import VerifiedGarbage.Proof.Aes.RISCV64.Blocks
public import VerifiedGarbage.Spec.Aes.Contract
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.Aes.RISCV64.CodeLit
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Aes.RISCV64.Blocks
meta import VerifiedGarbage.Proof.Aes.RISCV64.CodeLit
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Aes.Contract
meta import VerifiedGarbage.TCB.RISCV64.Target

/-!
# AES on whole blocks on RISC-V: `Verified`

Correctness (`Blocks.lean`), constant time (by taint tracking,
`taint_decide`: only the pointers, `rounds`, `n` and what is computed from
them reach addresses and branches), and a state satisfying the
precondition, against `Proof.Aes.blocksRISCV64`, then moved to the shared
contracts of `Spec/Aes/Contract.lean`.
-/

@[expose] public section

namespace VG.Proof.Aes.RISCV64

open VG VG.RISCV64 VG.Impl.Aes.RISCV64 VG.Proof.Aes

theorem encryptBlocks_correct (s : State) (hs : (Proof.Aes.blocksRISCV64 Spec.Aes.cipher).pre s) :
    ∃ t s', Exec isa encryptBlocks s t s' ∧ abiPreserved s s' ∧
      (Proof.Aes.blocksRISCV64 Spec.Aes.cipher).post s s' := by
  obtain ⟨t, s', he, h₁, hra, h₂⟩ := correct_blocks encrypt4_cryptOk hs
  exact ⟨t, s', he, ⟨h₁, Exec.sp he, hra⟩, h₂⟩

theorem decryptBlocks_correct (s : State) (hs : (Proof.Aes.blocksRISCV64 Spec.Aes.invCipher).pre s) :
    ∃ t s', Exec isa decryptBlocks s t s' ∧ abiPreserved s s' ∧
      (Proof.Aes.blocksRISCV64 Spec.Aes.invCipher).post s s' := by
  obtain ⟨t, s', he, h₁, hra, h₂⟩ := correct_blocks decrypt4_cryptOk hs
  exact ⟨t, s', he, ⟨h₁, Exec.sp he, hra⟩, h₂⟩

theorem blocks_agree (f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State) :
    ∀ s₁ s₂, (Proof.Aes.blocksRISCV64 f).pre s₁ → (Proof.Aes.blocksRISCV64 f).pre s₂ →
      (Proof.Aes.blocksRISCV64 f).pub s₁ s₂ →
      taint.Agree (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4]) s₁ s₂ := by
  rintro s₁ s₂ - - ⟨h0, h1, h2, h3, h4, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  exacts [h0, h1, h2, h3, h4]

theorem encryptBlocks_ct : ConstantTime isa (Proof.Aes.blocksRISCV64 Spec.Aes.cipher).pre
    (Proof.Aes.blocksRISCV64 Spec.Aes.cipher).pub encryptBlocks :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4]) (blocks_agree _)
    (by taint_decide)

theorem decryptBlocks_ct : ConstantTime isa (Proof.Aes.blocksRISCV64 Spec.Aes.invCipher).pre
    (Proof.Aes.blocksRISCV64 Spec.Aes.invCipher).pub decryptBlocks :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4]) (blocks_agree _)
    (by taint_decide)

/-- A state satisfying the precondition (one block). -/
def blocksSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 10 | .a2 => 0x3000 | .a3 => 1 | .a4 => 0x4000
    | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 240⟩]
  wr := [⟨0x3000, 16⟩, ⟨0x4000, 2048⟩]

theorem encryptBlocks_verified :
    Verified RISCV64.target encryptBlocks (Spec.Aes.encryptBlocksContract RISCV64.abi) :=
  Verified.of_correct encryptBlocks_correct encryptBlocks_ct (by
    sig_implies [Spec.Aes.encryptBlocksContract, Spec.Aes.blocksSig, Proof.Aes.blocksRISCV64,
      RISCV64.abi, RISCV64.argRegs] [blocksSat] using blocksSat)

theorem decryptBlocks_verified :
    Verified RISCV64.target decryptBlocks (Spec.Aes.decryptBlocksContract RISCV64.abi) :=
  Verified.of_correct decryptBlocks_correct decryptBlocks_ct (by
    sig_implies [Spec.Aes.decryptBlocksContract, Spec.Aes.blocksSig, Proof.Aes.blocksRISCV64,
      RISCV64.abi, RISCV64.argRegs] [blocksSat] using blocksSat)

end VG.Proof.Aes.RISCV64
