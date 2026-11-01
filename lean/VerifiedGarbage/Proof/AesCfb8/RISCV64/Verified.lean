module

public import VerifiedGarbage.Impl.AesCfb8.RISCV64
public import VerifiedGarbage.Proof.AesCfb8.RISCV64.Chain
public import VerifiedGarbage.Spec.Cfb8.Contract
import VerifiedGarbage.Proof.AesCbc.RISCV64.Verified
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RISCV64.Exec

/-!
# AES-CFB8 on RISC-V: `Verified`

Correctness and constant time, from the CFB8 chain's (`Chain.lean`) and its
call's (`wrap_wp`, `wrap_ct`, `Proof/AesCbc/RISCV64/Chain.lean`), a state
satisfying the precondition, and the shared contracts of
`Spec/Cfb8/Contract.lean` (with no stack: a call stores nothing in memory,
and the return address is saved in the scratch buffer).
-/

@[expose] public section

namespace VG.Proof.AesCfb8.RISCV64

open VG VG.RISCV64 VG.Impl.AesCfb8.RISCV64
open VG.Proof.AesCbc.RISCV64 (sat wrap_wp wrap_ct)

/-- The precondition, a chain's that writes the bytes (with the scratch buffer of 2176 bytes). -/
theorem wpre {enc : Bool} {s : State} (hs : (cfb8RISCV64 enc).pre s) :
    Proof.AesCbc.RISCV64.WPre true id s :=
  let ⟨a, b, c, _, e, f, g, h, i, j, k, l⟩ := hs
  ⟨a, b, c, e, f.symm, h, g, i, j, k, l⟩

theorem encrypt_correct (s : State) (hs : (cfb8RISCV64 true).pre s) :
    ∃ t s', Exec isa encrypt s t s' ∧ abiPreserved s s' ∧ (cfb8RISCV64 true).post s s' := by
  obtain ⟨t, s', he, hg, hra, hsp, hp⟩ :=
    wrap_wp (cfb8Chain_k true) (name := "vg_aes_cfb8_enc_chain") (wpre hs)
  exact ⟨t, s', he, ⟨hg, hsp, hra⟩, hp⟩

theorem decrypt_correct (s : State) (hs : (cfb8RISCV64 false).pre s) :
    ∃ t s', Exec isa decrypt s t s' ∧ abiPreserved s s' ∧ (cfb8RISCV64 false).post s s' := by
  obtain ⟨t, s', he, hg, hra, hsp, hp⟩ :=
    wrap_wp (cfb8Chain_k false) (name := "vg_aes_cfb8_dec_chain") (wpre hs)
  exact ⟨t, s', he, ⟨hg, hsp, hra⟩, hp⟩

theorem encrypt_ct : ConstantTime isa (cfb8RISCV64 true).pre (cfb8RISCV64 true).pub encrypt :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ =>
    wrap_ct (cfb8Chain_k true) "vg_aes_cfb8_enc_chain" _ _ _ _ _ _ (wpre h₁) (wpre h₂) hq e₁ e₂

theorem decrypt_ct : ConstantTime isa (cfb8RISCV64 false).pre (cfb8RISCV64 false).pub decrypt :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ =>
    wrap_ct (cfb8Chain_k false) "vg_aes_cfb8_dec_chain" _ _ _ _ _ _ (wpre h₁) (wpre h₂) hq e₁ e₂

theorem encrypt_verified : Verified RISCV64.target encrypt (Spec.Cfb8.aesEncryptContract RISCV64.abi) :=
  Verified.of_correct encrypt_correct encrypt_ct (by
    sig_implies [Spec.Cfb8.aesEncryptContract, Spec.Cfb8.aesSig, cfb8RISCV64, cfb8, cts, inK, RISCV64.abi,
      RISCV64.argRegs] [sat] using sat)

theorem decrypt_verified : Verified RISCV64.target decrypt (Spec.Cfb8.aesDecryptContract RISCV64.abi) :=
  Verified.of_correct decrypt_correct decrypt_ct (by
    sig_implies [Spec.Cfb8.aesDecryptContract, Spec.Cfb8.aesSig, cfb8RISCV64, cfb8, cts, inK, RISCV64.abi,
      RISCV64.argRegs] [sat] using sat)

end VG.Proof.AesCfb8.RISCV64
