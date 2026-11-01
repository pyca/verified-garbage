module

public import VerifiedGarbage.Impl.AesXts.PPC64LE
public import VerifiedGarbage.Proof.AesCbc.PPC64LE.Call
public import VerifiedGarbage.Proof.AesXts.Spec
public import VerifiedGarbage.Spec.Xts.Contract
public import VerifiedGarbage.Proof.Xts.Contract
import VerifiedGarbage.Proof.AesXts.PPC64LE.Body
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec

/-!
# XTS-AES on PPC64LE: the contracts

`Verified` for `vg_aes_xts_encrypt` and `vg_aes_xts_decrypt`: AES-CBC's
`whole_wp` and `whole_ct` (`Proof/AesCbc/PPC64LE/`) with the bodies of
`Body.lean`, and the contracts of `Spec/Xts/Contract.lean` from
`modePPC64LE (xtsMode enc)`.
-/

@[expose] public section

namespace VG.Proof.AesXts.PPC64LE

open VG VG.PPC64LE VG.Impl.AesXts.PPC64LE
open VG.Proof.AesCbc (ciphOf)
open VG.Proof.AesCbc.PPC64LE

theorem encrypt_correct (s : State) (hs : (modePPC64LE (AesXts.xtsMode true)).pre s) :
    ∃ t s', Exec isa encrypt s t s' ∧ abiPreserved s s' ∧ (modePPC64LE (AesXts.xtsMode true)).post s s' := by
  obtain ⟨t, s', he, hg, hlr, hp⟩ := whole_wp encBody_ok hs
  exact ⟨t, s', he, ⟨hg, Exec.sp he, hlr⟩, hp⟩

theorem decrypt_correct (s : State) (hs : (modePPC64LE (AesXts.xtsMode false)).pre s) :
    ∃ t s', Exec isa decrypt s t s' ∧ abiPreserved s s' ∧ (modePPC64LE (AesXts.xtsMode false)).post s s' := by
  obtain ⟨t, s', he, hg, hlr, hp⟩ := whole_wp decBody_ok hs
  exact ⟨t, s', he, ⟨hg, Exec.sp he, hlr⟩, hp⟩

theorem encrypt_ct : ConstantTime isa (modePPC64LE (AesXts.xtsMode true)).pre
    (modePPC64LE (AesXts.xtsMode true)).pub encrypt :=
  whole_ct encBody_ok encBody_ct

theorem decrypt_ct : ConstantTime isa (modePPC64LE (AesXts.xtsMode false)).pre
    (modePPC64LE (AesXts.xtsMode false)).pub decrypt :=
  whole_ct decBody_ok decBody_ct

theorem encrypt_noFrames : encrypt.noFrames = true := by decide +kernel

theorem decrypt_noFrames : decrypt.noFrames = true := by decide +kernel

/-- A state satisfying the precondition (with no blocks). -/
def sat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 10 | .r5 => 0x2000 | .r6 => 0x3000 | .r8 => 0x4000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 240⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x3000, 0⟩, ⟨0x4000, 2176⟩]

theorem encrypt_verified : Verified PPC64LE.target encrypt (Proof.Xts.aesEncryptContract PPC64LE.abi) :=
  Verified.of_correct encrypt_correct encrypt_ct (by
    sig_implies [Proof.Xts.aesEncryptContract, Proof.Xts.aesSig, modePPC64LE, AesXts.xtsMode,
      ciphOf, PPC64LE.abi, PPC64LE.argRegs, VG.Proof.AesCbc.length_blocksAt] [sat] using sat)

theorem decrypt_verified : Verified PPC64LE.target decrypt (Proof.Xts.aesDecryptContract PPC64LE.abi) :=
  Verified.of_correct decrypt_correct decrypt_ct (by
    sig_implies [Proof.Xts.aesDecryptContract, Proof.Xts.aesSig, modePPC64LE, AesXts.xtsMode,
      ciphOf, PPC64LE.abi, PPC64LE.argRegs, VG.Proof.AesCbc.length_blocksAt] [sat] using sat)

end VG.Proof.AesXts.PPC64LE
