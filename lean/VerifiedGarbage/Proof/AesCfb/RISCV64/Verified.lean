module

public import VerifiedGarbage.Impl.AesCfb.RISCV64
public import VerifiedGarbage.Proof.AesCbc.RISCV64.Call
public import VerifiedGarbage.Proof.AesCfb.Spec
public import VerifiedGarbage.Spec.Cfb.Contract
import VerifiedGarbage.Proof.AesCfb.RISCV64.Body
import VerifiedGarbage.Proof.AesCbc.RISCV64.Verified
import VerifiedGarbage.Proof.Aes.RISCV64.ChainModes
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RISCV64.Exec

/-!
# AES-CFB128 on RISC-V: `Verified`

Correctness and constant time, of encryption from the CFB128 chain's
(`Proof/Aes/RISCV64/ChainModes.lean`) and its call's (`wrap_wp`, `wrap_ct`,
`Proof/AesCbc/RISCV64/Chain.lean`), of decryption from the loop AES-CBC's
proofs share, a state satisfying the precondition, and the shared contracts of
`Spec/Cfb/Contract.lean` (with no stack: a call stores nothing in memory, and
the return address is saved in the scratch buffer).
-/

@[expose] public section

namespace VG.Proof.AesCfb.RISCV64

open VG VG.RISCV64 VG.Impl.AesCfb.RISCV64
open VG.Proof.AesCbc (cts)
open VG.Proof.AesCbc.RISCV64

theorem encrypt_correct (s : State) (hs : (modeRISCV64 (cfbMode true)).pre s) :
    ∃ t s', Exec isa encrypt s t s' ∧ abiPreserved s s' ∧ (modeRISCV64 (cfbMode true)).post s s' := by
  obtain ⟨t, s', he, hg, hra, hsp, hp⟩ :=
    wrap_wp Proof.Aes.RISCV64.cfbChain_k (name := "vg_aes_cfb_chain") (encrypt_wpre hs)
  exact ⟨t, s', he, ⟨hg, hsp, hra⟩, hp⟩

theorem encrypt_ct : ConstantTime isa (modeRISCV64 (cfbMode true)).pre (modeRISCV64 (cfbMode true)).pub
    encrypt :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ =>
    wrap_ct Proof.Aes.RISCV64.cfbChain_k "vg_aes_cfb_chain" _ _ _ _ _ _ (encrypt_wpre h₁) (encrypt_wpre h₂)
      hq e₁ e₂

theorem decrypt_correct (s : State) (hs : (modeRISCV64 (cfbMode false)).pre s) :
    ∃ t s', Exec isa decrypt s t s' ∧ abiPreserved s s' ∧ (modeRISCV64 (cfbMode false)).post s s' := by
  obtain ⟨t, s', he, hg, hra, hp⟩ := whole_wp decBody_ok hs
  exact ⟨t, s', he, ⟨hg, Exec.sp he, hra⟩, hp⟩

theorem encrypt_verified : Verified RISCV64.target encrypt (Spec.Cfb.aesEncryptContract RISCV64.abi) :=
  Verified.of_correct encrypt_correct encrypt_ct (by
    sig_implies [Spec.Cfb.aesEncryptContract, Spec.Cfb.aesSig, Spec.Cbc.aesSig, modeRISCV64, cfbMode, cfb, cts,
      RISCV64.abi, RISCV64.argRegs] [sat] using sat)

theorem decrypt_verified : Verified RISCV64.target decrypt (Spec.Cfb.aesDecryptContract RISCV64.abi) :=
  Verified.of_correct decrypt_correct (whole_ct decBody_ok decBody_ct) (by
    sig_implies [Spec.Cfb.aesDecryptContract, Spec.Cfb.aesSig, Spec.Cbc.aesSig, modeRISCV64, cfbMode, cfb, cts,
      RISCV64.abi, RISCV64.argRegs] [sat] using sat)

end VG.Proof.AesCfb.RISCV64
