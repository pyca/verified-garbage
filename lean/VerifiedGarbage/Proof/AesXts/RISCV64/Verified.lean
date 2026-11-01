module

public import VerifiedGarbage.Impl.AesXts.RISCV64
public import VerifiedGarbage.Proof.AesCbc.RISCV64.Call
public import VerifiedGarbage.Proof.AesXts.Spec
public import VerifiedGarbage.Spec.Xts.Contract
public import VerifiedGarbage.Proof.Xts.Contract
import VerifiedGarbage.Proof.AesXts.RISCV64.Body
import VerifiedGarbage.Proof.AesXts.RISCV64.Lit
import VerifiedGarbage.Proof.AesCbc.RISCV64.CT
import VerifiedGarbage.Proof.AesCbc.RISCV64.Verified
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.RISCV64.Exec

/-!
# XTS-AES on RISC-V: `Verified`

Correctness (`whole_wp`) and constant time (`whole_ct`), a state satisfying
the precondition, and the shared contracts of `Spec/Xts/Contract.lean` (with
no stack: a call stores nothing in memory, and the return address is saved
in the scratch buffer), as on PPC64LE (`Proof/AesXts/PPC64LE/Verified.lean`).
-/

@[expose] public section

namespace VG.Proof.AesXts.RISCV64

open VG VG.RISCV64 VG.Impl.AesXts.RISCV64
open VG.Proof.AesCbc (ciphOf)
open VG.Proof.AesCbc.RISCV64

theorem encrypt_correct (s : State) (hs : (modeRISCV64 (AesXts.xtsMode true)).pre s) :
    ∃ t s', Exec isa encrypt s t s' ∧ abiPreserved s s' ∧ (modeRISCV64 (AesXts.xtsMode true)).post s s' := by
  obtain ⟨t, s', he, hg, hra, hp⟩ := whole_wp encBody_ok hs
  exact ⟨t, s', he, ⟨hg, Exec.sp he, hra⟩, hp⟩

theorem decrypt_correct (s : State) (hs : (modeRISCV64 (AesXts.xtsMode false)).pre s) :
    ∃ t s', Exec isa decrypt s t s' ∧ abiPreserved s s' ∧ (modeRISCV64 (AesXts.xtsMode false)).post s s' := by
  obtain ⟨t, s', he, hg, hra, hp⟩ := whole_wp decBody_ok hs
  exact ⟨t, s', he, ⟨hg, Exec.sp he, hra⟩, hp⟩

theorem encrypt_ct : ConstantTime isa (modeRISCV64 (AesXts.xtsMode true)).pre
    (modeRISCV64 (AesXts.xtsMode true)).pub encrypt :=
  whole_ct encBody_ok encBody_ct

theorem decrypt_ct : ConstantTime isa (modeRISCV64 (AesXts.xtsMode false)).pre
    (modeRISCV64 (AesXts.xtsMode false)).pub decrypt :=
  whole_ct decBody_ok decBody_ct

theorem encrypt_noFrames : encrypt.noFrames = true := by lit_decide

theorem decrypt_noFrames : decrypt.noFrames = true := by lit_decide

theorem encrypt_verified : Verified RISCV64.target encrypt (Proof.Xts.aesEncryptContract RISCV64.abi) :=
  Verified.of_correct encrypt_correct encrypt_ct (by
    sig_implies [Proof.Xts.aesEncryptContract, Proof.Xts.aesSig, modeRISCV64, AesXts.xtsMode,
      ciphOf, RISCV64.abi, RISCV64.argRegs, VG.Proof.AesCbc.length_blocksAt] [sat] using sat)

theorem decrypt_verified : Verified RISCV64.target decrypt (Proof.Xts.aesDecryptContract RISCV64.abi) :=
  Verified.of_correct decrypt_correct decrypt_ct (by
    sig_implies [Proof.Xts.aesDecryptContract, Proof.Xts.aesSig, modeRISCV64, AesXts.xtsMode,
      ciphOf, RISCV64.abi, RISCV64.argRegs, VG.Proof.AesCbc.length_blocksAt] [sat] using sat)

end VG.Proof.AesXts.RISCV64
