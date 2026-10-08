import VerifiedGarbage.Proof.AesCbc.X86_64.Verified
import VerifiedGarbage.Proof.AesCfb.X86_64.Body

/-!
# AES-CFB128 on x86-64: `Verified`

Correctness and constant time (for any implementation `v` of the block
functions), from the loop AES-CBC's proofs share, a state satisfying the
precondition, and the shared contracts of `Spec/Cfb/Contract.lean` (with 8
bytes of stack, for the return address of the call of the block function).
-/

namespace VG.Proof.AesCfb.X86_64

open VG VG.X86_64 VG.Impl.AesCfb.X86_64
open VG.Impl.AesCbc.X86_64 (whole)
open VG.Impl.AesOfb.X86_64 (ivArgs)
open VG.Proof.AesCbc (cts)
open VG.Proof.AesCbc.X86_64
open VG.Proof.Aes.X86_64 (BlocksImpl)

theorem encrypt_mx (v : BlocksImpl) : (encrypt v.enc).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [encrypt, whole, body, Code.allInstrs, v.encMxcsr]; decide +kernel

theorem decrypt_mx (v : BlocksImpl) : (decrypt v.enc).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [decrypt, whole, body, Code.allInstrs, v.encMxcsr]; decide +kernel

theorem encrypt_spSafe (v : BlocksImpl) : (encrypt v.enc).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [encrypt, whole, body, Code.all, v.encSpSafe]; decide +kernel

theorem decrypt_spSafe (v : BlocksImpl) : (decrypt v.enc).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [decrypt, whole, body, Code.all, v.encSpSafe]; decide +kernel

theorem encrypt_correct (v : BlocksImpl) (s : State) (hs : (modeX86_64 (cfbMode true)).pre s) :
    ∃ t s', Exec isa (encrypt v.enc) s t s' ∧ abiPreserved s s' ∧ (modeX86_64 (cfbMode true)).post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := whole_wp (encBody_ok v) hs
  exact ⟨t, s', he, abiPreserved_of_exec (encrypt_mx v) he hg, hp⟩

theorem decrypt_correct (v : BlocksImpl) (s : State) (hs : (modeX86_64 (cfbMode false)).pre s) :
    ∃ t s', Exec isa (decrypt v.enc) s t s' ∧ abiPreserved s s' ∧ (modeX86_64 (cfbMode false)).post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := whole_wp (decBody_ok v) hs
  exact ⟨t, s', he, abiPreserved_of_exec (decrypt_mx v) he hg, hp⟩

theorem encrypt_verified (v : BlocksImpl) :
    Verified X86_64.target (encrypt v.enc) (Spec.Cfb.aesEncryptContract X86_64.abi 8) :=
  Verified.of_correct (encrypt_correct v) (whole_ct (encBody_ok v) (encBody_ct v)) (by
    sig_implies [Spec.Cfb.aesEncryptContract, Spec.Cfb.aesSig, Spec.Cbc.aesSig, modeX86_64, cfbMode, cfb, cts,
      X86_64.abi, X86_64.argRegs] [sat] using sat)

theorem decrypt_verified (v : BlocksImpl) :
    Verified X86_64.target (decrypt v.enc) (Spec.Cfb.aesDecryptContract X86_64.abi 8) :=
  Verified.of_correct (decrypt_correct v) (whole_ct (decBody_ok v) (decBody_ct v)) (by
    sig_implies [Spec.Cfb.aesDecryptContract, Spec.Cfb.aesSig, Spec.Cbc.aesSig, modeX86_64, cfbMode, cfb, cts,
      X86_64.abi, X86_64.argRegs] [sat] using sat)

end VG.Proof.AesCfb.X86_64
