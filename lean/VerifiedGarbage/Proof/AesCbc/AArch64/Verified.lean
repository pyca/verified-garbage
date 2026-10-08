import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.AesCbc.AArch64.CT

/-!
# AES-CBC on AArch64: `Verified`

Correctness and constant time (for any implementation `v` of the block
functions), a state satisfying the precondition, and the shared contracts of
`Spec/Cbc/Contract.lean` (with no stack: the calls keep the return address in
`x30`, which each function saves in the scratch buffer).
-/

namespace VG.Proof.AesCbc.AArch64

open VG VG.AArch64 VG.Impl.AesCbc.AArch64
open VG.Proof.Aes.AArch64 (BlocksImpl)

theorem encrypt_keepsV (v : BlocksImpl) : (encrypt v.enc).allInstrs keepsV = true := by
  simp only [encrypt, whole, encBody, Code.allInstrs, v.encKeepsV]; decide +kernel

theorem decrypt_keepsV (v : BlocksImpl) : (decrypt v.dec).allInstrs keepsV = true := by
  simp only [decrypt, whole, decBody, Code.allInstrs, v.decKeepsV]; decide +kernel

theorem encrypt_correct (v : BlocksImpl) (s : State) (hs : (cbcAArch64 true).pre s) :
    ∃ t s', Exec isa (encrypt v.enc) s t s' ∧ abiPreserved s s' ∧ (cbcAArch64 true).post s s' :=
  WP.withPreservedV (whole_wp (encBody_ok v) hs) (encrypt_keepsV v)

theorem decrypt_correct (v : BlocksImpl) (s : State) (hs : (cbcAArch64 false).pre s) :
    ∃ t s', Exec isa (decrypt v.dec) s t s' ∧ abiPreserved s s' ∧ (cbcAArch64 false).post s s' :=
  WP.withPreservedV (whole_wp (decBody_ok v) hs) (decrypt_keepsV v)

/-- A state satisfying the precondition (with no blocks). -/
def sat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 10 | .x2 => 0x2000 | .x3 => 0x3000 | .x5 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 240⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x3000, 0⟩, ⟨0x4000, 2176⟩]

theorem encrypt_verified (v : BlocksImpl) :
    Verified AArch64.target (encrypt v.enc) (Spec.Cbc.aesEncryptContract AArch64.abi) :=
  Verified.of_correct (encrypt_correct v) (whole_ct (encBody_ok v) (encBody_ct v)) (by
    sig_implies [Spec.Cbc.aesEncryptContract, Spec.Cbc.aesSig, cbcAArch64, ciphOf, cbc, cts, AArch64.abi,
      AArch64.argRegs] [sat] using sat)

theorem decrypt_verified (v : BlocksImpl) :
    Verified AArch64.target (decrypt v.dec) (Spec.Cbc.aesDecryptContract AArch64.abi) :=
  Verified.of_correct (decrypt_correct v) (whole_ct (decBody_ok v) (decBody_ct v)) (by
    sig_implies [Spec.Cbc.aesDecryptContract, Spec.Cbc.aesSig, cbcAArch64, ciphOf, cbc, cts, AArch64.abi,
      AArch64.argRegs] [sat] using sat)

end VG.Proof.AesCbc.AArch64
