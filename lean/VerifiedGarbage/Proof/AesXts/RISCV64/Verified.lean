module

public import VerifiedGarbage.Impl.AesXts.RISCV64
public import VerifiedGarbage.Proof.AesCbc.RISCV64.Call
public import VerifiedGarbage.Proof.AesXts.Spec
public import VerifiedGarbage.Spec.Xts.Contract
public import VerifiedGarbage.Proof.Xts.Contract
import VerifiedGarbage.Proof.Aes.RISCV64.WideXts
import VerifiedGarbage.Proof.AesXts.RISCV64.Lit
import VerifiedGarbage.Proof.AesCbc.RISCV64.Verified
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.RISCV64.Exec

/-!
# XTS-AES on RISC-V: `Verified`

Correctness and constant time from the wide encryption's and decryption's
(`xtsEncWide_k`, `xtsDecWide_k`, `Proof/Aes/RISCV64/WideXts.lean`, four
blocks at a time), called as chains (`wrap_wp`, `wrap_ct`,
`Proof/AesCbc/RISCV64/Chain.lean`), a state satisfying the precondition, and
the shared contracts of `Spec/Xts/Contract.lean` (with no stack: a call
stores nothing in memory, and the return address is saved in the scratch
buffer).
-/

@[expose] public section

namespace VG.Proof.AesXts.RISCV64

open VG VG.RISCV64 VG.Impl.AesXts.RISCV64
open VG.Proof.AesCbc (ciphOf)
open VG.Proof.AesCbc.RISCV64

theorem encrypt_correct (s : State) (hs : (modeRISCV64 (AesXts.xtsMode true)).pre s) :
    ∃ t s', Exec isa encrypt s t s' ∧ abiPreserved s s' ∧ (modeRISCV64 (AesXts.xtsMode true)).post s s' := by
  obtain ⟨t, s', he, hg, hra, hsp, hp⟩ :=
    wrap_wp Proof.Aes.RISCV64.xtsEncWide_k (name := "vg_aes_xts_enc_wide") (encrypt_wpre hs)
  exact ⟨t, s', he, ⟨hg, hsp, hra⟩, hp⟩

theorem decrypt_correct (s : State) (hs : (modeRISCV64 (AesXts.xtsMode false)).pre s) :
    ∃ t s', Exec isa decrypt s t s' ∧ abiPreserved s s' ∧ (modeRISCV64 (AesXts.xtsMode false)).post s s' := by
  obtain ⟨t, s', he, hg, hra, hsp, hp⟩ :=
    wrap_wp Proof.Aes.RISCV64.xtsDecWide_k (name := "vg_aes_xts_dec_wide") (encrypt_wpre hs)
  exact ⟨t, s', he, ⟨hg, hsp, hra⟩, hp⟩

theorem encrypt_ct : ConstantTime isa (modeRISCV64 (AesXts.xtsMode true)).pre
    (modeRISCV64 (AesXts.xtsMode true)).pub encrypt :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ =>
    wrap_ct Proof.Aes.RISCV64.xtsEncWide_k "vg_aes_xts_enc_wide" _ _ _ _ _ _ (encrypt_wpre h₁)
      (encrypt_wpre h₂) hq e₁ e₂

theorem decrypt_ct : ConstantTime isa (modeRISCV64 (AesXts.xtsMode false)).pre
    (modeRISCV64 (AesXts.xtsMode false)).pub decrypt :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ =>
    wrap_ct Proof.Aes.RISCV64.xtsDecWide_k "vg_aes_xts_dec_wide" _ _ _ _ _ _ (encrypt_wpre h₁)
      (encrypt_wpre h₂) hq e₁ e₂

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
