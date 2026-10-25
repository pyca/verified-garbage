module

public import VerifiedGarbage.Impl.AesCbc.RISCV64
public import VerifiedGarbage.Proof.AesCbc.RISCV64.Call
public import VerifiedGarbage.Spec.Cbc.Contract
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.AesCbc.RISCV64.Body
import VerifiedGarbage.Proof.AesCbc.RISCV64.CT
import VerifiedGarbage.Proof.AesCbc.RISCV64.Lit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.AesCbc.RISCV64.Call
meta import VerifiedGarbage.Proof.AesCbc.RISCV64.Lit
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Cbc.Contract
meta import VerifiedGarbage.TCB.RISCV64.Target

/-!
# AES-CBC on RISC-V: `Verified`

Correctness (`whole_wp`) and constant time (`whole_ct`, `CT.lean`), a state
satisfying the precondition, and the shared contracts of
`Spec/Cbc/Contract.lean` (with no stack: a call stores nothing in memory, and
the return address is saved in the scratch buffer).
-/

@[expose] public section

namespace VG.Proof.AesCbc.RISCV64

open VG VG.RISCV64 VG.Impl.AesCbc.RISCV64

/-- `vg_aes_cbc_encrypt` (`enc`) or `vg_aes_cbc_decrypt`. -/
abbrev cbcRISCV64 (enc : Bool) : Contract isa := modeRISCV64 (cbcMode enc)

theorem encrypt_correct (s : State) (hs : (cbcRISCV64 true).pre s) :
    ∃ t s', Exec isa encrypt s t s' ∧ abiPreserved s s' ∧ (cbcRISCV64 true).post s s' := by
  obtain ⟨t, s', he, hg, hra, hp⟩ := whole_wp encBody_ok hs
  exact ⟨t, s', he, ⟨hg, Exec.sp he, hra⟩, hp⟩

theorem decrypt_correct (s : State) (hs : (cbcRISCV64 false).pre s) :
    ∃ t s', Exec isa decrypt s t s' ∧ abiPreserved s s' ∧ (cbcRISCV64 false).post s s' := by
  obtain ⟨t, s', he, hg, hra, hp⟩ := whole_wp decBody_ok hs
  exact ⟨t, s', he, ⟨hg, Exec.sp he, hra⟩, hp⟩

/-- A state satisfying the precondition (with no blocks). -/
def sat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 10 | .a2 => 0x2000 | .a3 => 0x3000 | .a5 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 240⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x3000, 0⟩, ⟨0x4000, 2176⟩]

theorem encrypt_verified : Verified RISCV64.target encrypt (Spec.Cbc.aesEncryptContract RISCV64.abi) :=
  Verified.of_correct encrypt_correct (whole_ct encBody_ok encBody_ct) (by
    sig_implies [Spec.Cbc.aesEncryptContract, Spec.Cbc.aesSig, cbcRISCV64, modeRISCV64, cbcMode,
      ciphOf, cbc, cts, RISCV64.abi, RISCV64.argRegs] [sat] using sat)

theorem decrypt_verified : Verified RISCV64.target decrypt (Spec.Cbc.aesDecryptContract RISCV64.abi) :=
  Verified.of_correct decrypt_correct (whole_ct decBody_ok decBody_ct) (by
    sig_implies [Spec.Cbc.aesDecryptContract, Spec.Cbc.aesSig, cbcRISCV64, modeRISCV64, cbcMode,
      ciphOf, cbc, cts, RISCV64.abi, RISCV64.argRegs] [sat] using sat)

end VG.Proof.AesCbc.RISCV64
