module

public import VerifiedGarbage.Impl.AesCfb.PPC64LE
public import VerifiedGarbage.Proof.AesCbc.PPC64LE.Call
public import VerifiedGarbage.Proof.AesCfb.Spec
public import VerifiedGarbage.Spec.Cfb.Contract
import VerifiedGarbage.Proof.AesCfb.PPC64LE.Body
import VerifiedGarbage.Proof.AesCbc.PPC64LE.Verified
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec

/-!
# AES-CFB128 on PPC64LE: `Verified`

Correctness and constant time, from the loop AES-CBC's proofs share, a state
satisfying the precondition, and the shared contracts of
`Spec/Cfb/Contract.lean` (with no stack: a call stores nothing in memory).
-/

@[expose] public section

namespace VG.Proof.AesCfb.PPC64LE

open VG VG.PPC64LE VG.Impl.AesCfb.PPC64LE
open VG.Proof.AesCbc (cts)
open VG.Proof.AesCbc.PPC64LE

theorem encrypt_correct (s : State) (hs : (modePPC64LE (cfbMode true)).pre s) :
    ∃ t s', Exec isa encrypt s t s' ∧ abiPreserved s s' ∧ (modePPC64LE (cfbMode true)).post s s' := by
  obtain ⟨t, s', he, hg, hlr, hp⟩ := whole_wp encBody_ok hs
  exact ⟨t, s', he, ⟨hg, Exec.sp he, hlr⟩, hp⟩

theorem decrypt_correct (s : State) (hs : (modePPC64LE (cfbMode false)).pre s) :
    ∃ t s', Exec isa decrypt s t s' ∧ abiPreserved s s' ∧ (modePPC64LE (cfbMode false)).post s s' := by
  obtain ⟨t, s', he, hg, hlr, hp⟩ := whole_wp decBody_ok hs
  exact ⟨t, s', he, ⟨hg, Exec.sp he, hlr⟩, hp⟩

theorem encrypt_verified : Verified PPC64LE.target encrypt (Spec.Cfb.aesEncryptContract PPC64LE.abi) :=
  Verified.of_correct encrypt_correct (whole_ct encBody_ok encBody_ct) (by
    sig_implies [Spec.Cfb.aesEncryptContract, Spec.Cfb.aesSig, Spec.Cbc.aesSig, modePPC64LE, cfbMode, cfb, cts,
      PPC64LE.abi, PPC64LE.argRegs] [sat] using sat)

theorem decrypt_verified : Verified PPC64LE.target decrypt (Spec.Cfb.aesDecryptContract PPC64LE.abi) :=
  Verified.of_correct decrypt_correct (whole_ct decBody_ok decBody_ct) (by
    sig_implies [Spec.Cfb.aesDecryptContract, Spec.Cfb.aesSig, Spec.Cbc.aesSig, modePPC64LE, cfbMode, cfb, cts,
      PPC64LE.abi, PPC64LE.argRegs] [sat] using sat)

end VG.Proof.AesCfb.PPC64LE
