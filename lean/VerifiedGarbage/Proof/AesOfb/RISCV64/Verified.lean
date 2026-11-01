module

public import VerifiedGarbage.Impl.AesOfb.RISCV64
public import VerifiedGarbage.Proof.AesCbc.RISCV64.Call
public import VerifiedGarbage.Proof.AesOfb.Spec
public import VerifiedGarbage.Spec.Ofb.Contract
import VerifiedGarbage.Proof.Aes.RISCV64.ChainModes
import VerifiedGarbage.Proof.AesCbc.RISCV64.Verified
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RISCV64.Exec

/-!
# AES-OFB on RISC-V: `Verified`

Correctness and constant time, from the OFB chain's
(`Proof/Aes/RISCV64/ChainModes.lean`) and its call's (`wrap_wp`, `wrap_ct`,
`Proof/AesCbc/RISCV64/Chain.lean`), a state satisfying the precondition, and
the shared contract of
`Spec/Ofb/Contract.lean` (with no stack: a call stores nothing in memory, and
the return address is saved in the scratch buffer).
-/

@[expose] public section

namespace VG.Proof.AesOfb.RISCV64

open VG VG.RISCV64 VG.Impl.AesOfb.RISCV64
open VG.Proof.AesCbc.RISCV64

theorem crypt_correct (s : State) (hs : (modeRISCV64 ofbMode).pre s) :
    ∃ t s', Exec isa crypt s t s' ∧ abiPreserved s s' ∧ (modeRISCV64 ofbMode).post s s' := by
  obtain ⟨t, s', he, hg, hra, hsp, hp⟩ :=
    wrap_wp Proof.Aes.RISCV64.ofbChain_k (name := "vg_aes_ofb_chain") (encrypt_wpre hs)
  exact ⟨t, s', he, ⟨hg, hsp, hra⟩, hp⟩

theorem crypt_ct : ConstantTime isa (modeRISCV64 ofbMode).pre (modeRISCV64 ofbMode).pub crypt :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ =>
    wrap_ct Proof.Aes.RISCV64.ofbChain_k "vg_aes_ofb_chain" _ _ _ _ _ _ (encrypt_wpre h₁) (encrypt_wpre h₂)
      hq e₁ e₂

theorem crypt_verified : Verified RISCV64.target crypt (Spec.Ofb.aesContract RISCV64.abi) :=
  Verified.of_correct crypt_correct crypt_ct
    { pre := by sig_implies_pre [Spec.Ofb.aesContract, Spec.Ofb.aesSig, Spec.Cbc.aesSig, modeRISCV64,
        RISCV64.abi, RISCV64.argRegs]
      -- `ofbMode.chain` counts the blocks, which are `n`.
      post := by
        intro s s' _ h
        sig_post [Spec.Ofb.aesContract, Spec.Ofb.aesSig, Spec.Cbc.aesSig, modeRISCV64, ofbMode, RISCV64.abi,
          RISCV64.argRegs]
        sig_reduce [Spec.Ofb.aesContract, Spec.Ofb.aesSig, Spec.Cbc.aesSig, modeRISCV64, ofbMode, RISCV64.abi,
          RISCV64.argRegs] at h
        sig_simp [Spec.Ofb.aesContract, Spec.Ofb.aesSig, Spec.Cbc.aesSig, modeRISCV64, ofbMode, RISCV64.abi,
          RISCV64.argRegs] [] at h
        rwa [VG.Proof.AesCbc.length_blocksAt] at h
      pub := by sig_implies_pub [Spec.Ofb.aesContract, Spec.Ofb.aesSig, Spec.Cbc.aesSig, modeRISCV64,
        RISCV64.abi, RISCV64.argRegs]
      sat := by sig_implies_sat [Spec.Ofb.aesContract, Spec.Ofb.aesSig, Spec.Cbc.aesSig, modeRISCV64,
        RISCV64.abi, RISCV64.argRegs] [sat] using sat }

end VG.Proof.AesOfb.RISCV64
