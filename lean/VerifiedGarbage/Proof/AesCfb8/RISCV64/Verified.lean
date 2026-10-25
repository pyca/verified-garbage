module

public import VerifiedGarbage.Impl.AesCfb8.RISCV64
public import VerifiedGarbage.Proof.AesCfb8.RISCV64.Loop
public import VerifiedGarbage.Spec.Cfb8.Contract
import VerifiedGarbage.Proof.AesCfb8.RISCV64.Body
import VerifiedGarbage.Proof.AesCfb8.RISCV64.CT
import VerifiedGarbage.Proof.AesCbc.RISCV64.Verified
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RISCV64.Exec

/-!
# AES-CFB8 on RISC-V: `Verified`

Correctness (`whole_wp`) and constant time (`whole_ct`, `CT.lean`), a state
satisfying the precondition, and the shared contracts of
`Spec/Cfb8/Contract.lean` (with no stack: a call stores nothing in memory,
and the return address is saved in the scratch buffer), as on PPC64LE
(`Proof/AesCfb8/PPC64LE/Verified.lean`).
-/

@[expose] public section

namespace VG.Proof.AesCfb8.RISCV64

open VG VG.RISCV64 VG.Impl.AesCfb8.RISCV64
open VG.Proof.AesCbc.RISCV64 (sat)

theorem encrypt_correct (s : State) (hs : (cfb8RISCV64 true).pre s) :
    ∃ t s', Exec isa encrypt s t s' ∧ abiPreserved s s' ∧ (cfb8RISCV64 true).post s s' := by
  obtain ⟨t, s', he, hg, hra, hp⟩ := whole_wp encBody_ok hs
  exact ⟨t, s', he, ⟨hg, Exec.sp he, hra⟩, hp⟩

theorem decrypt_correct (s : State) (hs : (cfb8RISCV64 false).pre s) :
    ∃ t s', Exec isa decrypt s t s' ∧ abiPreserved s s' ∧ (cfb8RISCV64 false).post s s' := by
  obtain ⟨t, s', he, hg, hra, hp⟩ := whole_wp decBody_ok hs
  exact ⟨t, s', he, ⟨hg, Exec.sp he, hra⟩, hp⟩

theorem encrypt_verified : Verified RISCV64.target encrypt (Spec.Cfb8.aesEncryptContract RISCV64.abi) :=
  Verified.of_correct encrypt_correct (whole_ct encBody_ok encPost_taint) (by
    sig_implies [Spec.Cfb8.aesEncryptContract, Spec.Cfb8.aesSig, cfb8RISCV64, cfb8, cts, inK, RISCV64.abi,
      RISCV64.argRegs] [sat] using sat)

theorem decrypt_verified : Verified RISCV64.target decrypt (Spec.Cfb8.aesDecryptContract RISCV64.abi) :=
  Verified.of_correct decrypt_correct (whole_ct decBody_ok decPost_taint) (by
    sig_implies [Spec.Cfb8.aesDecryptContract, Spec.Cfb8.aesSig, cfb8RISCV64, cfb8, cts, inK, RISCV64.abi,
      RISCV64.argRegs] [sat] using sat)

end VG.Proof.AesCfb8.RISCV64
