module

public import VerifiedGarbage.Impl.AesCfb8.PPC64LE
public import VerifiedGarbage.Proof.AesCfb8.PPC64LE.Loop
public import VerifiedGarbage.Spec.Cfb8.Contract
import VerifiedGarbage.Proof.AesCfb8.PPC64LE.CT
import VerifiedGarbage.Proof.AesCfb8.PPC64LE.Body
import VerifiedGarbage.Proof.AesCbc.PPC64LE.Verified
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec

/-!
# AES-CFB8 on PPC64LE: `Verified`

Correctness and constant time, a state satisfying the precondition (AES-CBC's,
with no bytes), and the shared contracts of `Spec/Cfb8/Contract.lean` (with
no stack: a call stores nothing in memory).
-/

@[expose] public section

namespace VG.Proof.AesCfb8.PPC64LE

open VG VG.PPC64LE VG.Impl.AesCfb8.PPC64LE
open VG.Proof.AesCbc.PPC64LE (sat)

theorem encrypt_correct (s : State) (hs : (cfb8PPC64LE true).pre s) :
    ∃ t s', Exec isa encrypt s t s' ∧ abiPreserved s s' ∧ (cfb8PPC64LE true).post s s' := by
  obtain ⟨t, s', he, hg, hlr, hp⟩ := whole_wp encBody_ok hs
  exact ⟨t, s', he, ⟨hg, Exec.sp he, hlr⟩, hp⟩

theorem decrypt_correct (s : State) (hs : (cfb8PPC64LE false).pre s) :
    ∃ t s', Exec isa decrypt s t s' ∧ abiPreserved s s' ∧ (cfb8PPC64LE false).post s s' := by
  obtain ⟨t, s', he, hg, hlr, hp⟩ := whole_wp decBody_ok hs
  exact ⟨t, s', he, ⟨hg, Exec.sp he, hlr⟩, hp⟩

theorem encrypt_verified : Verified PPC64LE.target encrypt (Spec.Cfb8.aesEncryptContract PPC64LE.abi) :=
  Verified.of_correct encrypt_correct (whole_ct encBody_ok encPost_taint) (by
    sig_implies [Spec.Cfb8.aesEncryptContract, Spec.Cfb8.aesSig, cfb8PPC64LE, cfb8, cts, inK, PPC64LE.abi,
      PPC64LE.argRegs] [sat] using sat)

theorem decrypt_verified : Verified PPC64LE.target decrypt (Spec.Cfb8.aesDecryptContract PPC64LE.abi) :=
  Verified.of_correct decrypt_correct (whole_ct decBody_ok decPost_taint) (by
    sig_implies [Spec.Cfb8.aesDecryptContract, Spec.Cfb8.aesSig, cfb8PPC64LE, cfb8, cts, inK, PPC64LE.abi,
      PPC64LE.argRegs] [sat] using sat)

end VG.Proof.AesCfb8.PPC64LE
