import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.AesCbc.X86_64.CT

/-!
# AES-CBC on x86-64: `Verified`

Correctness and constant time (for any implementation `v` of the block
functions), a state satisfying the precondition, and the shared contracts of
`Spec/Cbc/Contract.lean` (with 8 bytes of stack, for the return address of
the call of the block function).
-/

namespace VG.Proof.AesCbc.X86_64

open VG VG.X86_64 VG.Impl.AesCbc.X86_64
open VG.Proof.Aes.X86_64 (BlocksImpl)

theorem encrypt_mx (v : BlocksImpl) : (encrypt v.enc).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [encrypt, whole, encBody, Code.allInstrs, v.encMxcsr]; decide +kernel

theorem decrypt_mx (v : BlocksImpl) : (decrypt v.dec).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [decrypt, whole, decBody, Code.allInstrs, v.decMxcsr]; decide +kernel

theorem encrypt_spSafe (v : BlocksImpl) : (encrypt v.enc).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [encrypt, whole, encBody, Code.all, v.encSpSafe]; decide +kernel

theorem decrypt_spSafe (v : BlocksImpl) : (decrypt v.dec).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [decrypt, whole, decBody, Code.all, v.decSpSafe]; decide +kernel

theorem encrypt_correct (v : BlocksImpl) (s : State) (hs : (cbcX86_64 true).pre s) :
    ∃ t s', Exec isa (encrypt v.enc) s t s' ∧ abiPreserved s s' ∧ (cbcX86_64 true).post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := whole_wp (encBody_ok v) hs
  exact ⟨t, s', he, abiPreserved_of_exec (encrypt_mx v) he hg, hp⟩

theorem decrypt_correct (v : BlocksImpl) (s : State) (hs : (cbcX86_64 false).pre s) :
    ∃ t s', Exec isa (decrypt v.dec) s t s' ∧ abiPreserved s s' ∧ (cbcX86_64 false).post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := whole_wp (decBody_ok v) hs
  exact ⟨t, s', he, abiPreserved_of_exec (decrypt_mx v) he hg, hp⟩

/-- A state satisfying the precondition (with no blocks). -/
def sat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 10 | .rdx => 0x2000 | .rcx => 0x3000 | .r9 => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 240⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x3000, 0⟩, ⟨0x4000, 2176⟩]

theorem encrypt_verified (v : BlocksImpl) :
    Verified X86_64.target (encrypt v.enc) (Spec.Cbc.aesEncryptContract X86_64.abi 8) :=
  Verified.of_correct (encrypt_correct v) (whole_ct (encBody_ok v) (encBody_ct v)) (by
    sig_implies [Spec.Cbc.aesEncryptContract, Spec.Cbc.aesSig, cbcX86_64, ciphOf, cbc, cts, X86_64.abi,
      X86_64.argRegs] [sat] using sat)

theorem decrypt_verified (v : BlocksImpl) :
    Verified X86_64.target (decrypt v.dec) (Spec.Cbc.aesDecryptContract X86_64.abi 8) :=
  Verified.of_correct (decrypt_correct v) (whole_ct (decBody_ok v) (decBody_ct v)) (by
    sig_implies [Spec.Cbc.aesDecryptContract, Spec.Cbc.aesSig, cbcX86_64, ciphOf, cbc, cts, X86_64.abi,
      X86_64.argRegs] [sat] using sat)

end VG.Proof.AesCbc.X86_64
