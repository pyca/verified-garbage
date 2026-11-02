module

public import VerifiedGarbage.Impl.AesCbc.RISCV64
public import VerifiedGarbage.Proof.AesCbc.RISCV64.Call
public import VerifiedGarbage.Spec.Cbc.Contract
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.AesCbc.RISCV64.Chain
import VerifiedGarbage.Proof.Aes.RISCV64.WideCbc
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.AesCbc.RISCV64.Call
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Cbc.Contract
meta import VerifiedGarbage.TCB.RISCV64.Target

/-!
# AES-CBC on RISC-V: `Verified`

Correctness and constant time, of encryption from the chain's
(`wrap_wp`, `wrap_ct`, `Chain.lean`: CBC encryption, the blocks enciphered
and their last the chaining value) and of decryption from the wide
decryption's (`cbcDecWide_k`, `Proof/Aes/RISCV64/WideCbc.lean`, four blocks
at a time) the same way, a state satisfying the precondition,
and the shared contracts of
`Spec/Cbc/Contract.lean` (with no stack: a call stores nothing in memory, and
the return address is saved in the scratch buffer).
-/

@[expose] public section

namespace VG.Proof.AesCbc.RISCV64

open VG VG.RISCV64 VG.Impl.AesCbc.RISCV64

/-- `vg_aes_cbc_encrypt` (`enc`) or `vg_aes_cbc_decrypt`. -/
abbrev cbcRISCV64 (enc : Bool) : Contract isa := modeRISCV64 (cbcMode enc)

/-- A mode's precondition, a chain's that writes the blocks (with the scratch buffer of 2176
bytes), for encryption and decryption. -/
theorem encrypt_wpre {M : Mode} {s : State} (hs : (modeRISCV64 M).pre s) : WPre true (16 * ·) s :=
  let ⟨a, b, c, _, e, f, g, h, i, j, k, l⟩ := hs
  ⟨a, b, c, e, f.symm, h, g, i, j, k, l⟩

theorem encrypt_correct (s : State) (hs : (cbcRISCV64 true).pre s) :
    ∃ t s', Exec isa encrypt s t s' ∧ abiPreserved s s' ∧ (cbcRISCV64 true).post s s' := by
  obtain ⟨t, s', he, hg, hra, hsp, hc, ho⟩ := wrap_wp (chain_k true) (name := "vg_aes_cbc_chain") (encrypt_wpre hs)
  exact ⟨t, s', he, ⟨hg, hsp, hra⟩, ho rfl, hc.trans (next_encrypt _ _ _).symm⟩

theorem encrypt_ct : ConstantTime isa (cbcRISCV64 true).pre (cbcRISCV64 true).pub encrypt :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ =>
    wrap_ct (chain_k true) "vg_aes_cbc_chain" _ _ _ _ _ _ (encrypt_wpre h₁) (encrypt_wpre h₂) hq e₁ e₂

theorem decrypt_correct (s : State) (hs : (cbcRISCV64 false).pre s) :
    ∃ t s', Exec isa decrypt s t s' ∧ abiPreserved s s' ∧ (cbcRISCV64 false).post s s' := by
  obtain ⟨t, s', he, hg, hra, hsp, hp⟩ :=
    wrap_wp Proof.Aes.RISCV64.cbcDecWide_k (name := "vg_aes_cbc_dec_wide") (encrypt_wpre hs)
  exact ⟨t, s', he, ⟨hg, hsp, hra⟩, hp⟩

theorem decrypt_ct : ConstantTime isa (cbcRISCV64 false).pre (cbcRISCV64 false).pub decrypt :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ =>
    wrap_ct Proof.Aes.RISCV64.cbcDecWide_k "vg_aes_cbc_dec_wide" _ _ _ _ _ _ (encrypt_wpre h₁)
      (encrypt_wpre h₂) hq e₁ e₂

/-- A state satisfying the precondition (with no blocks). -/
def sat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 10 | .a2 => 0x2000 | .a3 => 0x3000 | .a5 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 240⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x3000, 0⟩, ⟨0x4000, 2176⟩]

theorem encrypt_verified : Verified RISCV64.target encrypt (Spec.Cbc.aesEncryptContract RISCV64.abi) :=
  Verified.of_correct encrypt_correct encrypt_ct (by
    sig_implies [Spec.Cbc.aesEncryptContract, Spec.Cbc.aesSig, cbcRISCV64, modeRISCV64, cbcMode,
      ciphOf, cbc, cts, RISCV64.abi, RISCV64.argRegs] [sat] using sat)

theorem decrypt_verified : Verified RISCV64.target decrypt (Spec.Cbc.aesDecryptContract RISCV64.abi) :=
  Verified.of_correct decrypt_correct decrypt_ct (by
    sig_implies [Spec.Cbc.aesDecryptContract, Spec.Cbc.aesSig, cbcRISCV64, modeRISCV64, cbcMode,
      ciphOf, cbc, cts, RISCV64.abi, RISCV64.argRegs] [sat] using sat)

end VG.Proof.AesCbc.RISCV64
