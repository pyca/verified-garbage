import VerifiedGarbage.Proof.AesCbc.X86_64.Verified
import VerifiedGarbage.Proof.AesCfb8.X86_64.CT

/-!
# AES-CFB8 on x86-64: `Verified`

Correctness and constant time (for any implementation `v` of the block
functions), AES-CBC's state satisfying the precondition, and the shared
contracts of `Spec/Cfb8/Contract.lean` (with 8 bytes of stack, for the
return address of the call of the block function).
-/

namespace VG.Proof.AesCfb8.X86_64

open VG VG.X86_64 VG.Impl.AesCfb8.X86_64
open VG.Impl.AesCbc.X86_64 (whole)
open VG.Proof.AesCbc.X86_64 (sat)
open VG.Proof.Aes.X86_64 (BlocksImpl)

theorem encrypt_mx (v : BlocksImpl) : (encrypt v.enc).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [encrypt, whole, body, Code.allInstrs, v.encMxcsr]; decide +kernel

theorem decrypt_mx (v : BlocksImpl) : (decrypt v.enc).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [decrypt, whole, body, Code.allInstrs, v.encMxcsr]; decide +kernel

theorem encrypt_spSafe (v : BlocksImpl) : (encrypt v.enc).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [encrypt, whole, body, Code.all, v.encSpSafe]; decide +kernel

theorem decrypt_spSafe (v : BlocksImpl) : (decrypt v.enc).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [decrypt, whole, body, Code.all, v.encSpSafe]; decide +kernel

theorem encrypt_correct (v : BlocksImpl) (s : State) (hs : (cfb8X86_64 true).pre s) :
    ∃ t s', Exec isa (encrypt v.enc) s t s' ∧ abiPreserved s s' ∧ (cfb8X86_64 true).post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := whole_wp (encBody_ok v) hs
  exact ⟨t, s', he, abiPreserved_of_exec (encrypt_mx v) he hg, hp⟩

theorem decrypt_correct (v : BlocksImpl) (s : State) (hs : (cfb8X86_64 false).pre s) :
    ∃ t s', Exec isa (decrypt v.enc) s t s' ∧ abiPreserved s s' ∧ (cfb8X86_64 false).post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := whole_wp (decBody_ok v) hs
  exact ⟨t, s', he, abiPreserved_of_exec (decrypt_mx v) he hg, hp⟩

theorem encrypt_verified (v : BlocksImpl) :
    Verified X86_64.target (encrypt v.enc) (Spec.Cfb8.aesEncryptContract X86_64.abi 8) :=
  Verified.of_correct (encrypt_correct v) (whole_ct (encBody_ok v) (encBody_ct v)) (by
    sig_implies [Spec.Cfb8.aesEncryptContract, Spec.Cfb8.aesSig, cfb8X86_64, cfb8, cts, inK, X86_64.abi,
      X86_64.argRegs] [sat] using sat)

theorem decrypt_verified (v : BlocksImpl) :
    Verified X86_64.target (decrypt v.enc) (Spec.Cfb8.aesDecryptContract X86_64.abi 8) :=
  Verified.of_correct (decrypt_correct v) (whole_ct (decBody_ok v) (decBody_ct v)) (by
    sig_implies [Spec.Cfb8.aesDecryptContract, Spec.Cfb8.aesSig, cfb8X86_64, cfb8, cts, inK, X86_64.abi,
      X86_64.argRegs] [sat] using sat)

end VG.Proof.AesCfb8.X86_64
