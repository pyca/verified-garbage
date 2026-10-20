module

import VerifiedGarbage.Proof.AesXts.AArch64.Unit.CT
import VerifiedGarbage.Proof.AesXts.AArch64.Verified
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Aes.AArch64.BlocksVariant
public import VerifiedGarbage.Proof.AesCbc.AArch64.Call
public import VerifiedGarbage.Proof.AesXts.AArch64.Unit.Contract
public import VerifiedGarbage.Proof.AesXts.Spec
import VerifiedGarbage.Proof.AesXts.AArch64.Unit.Dec
import VerifiedGarbage.Proof.AesXts.AArch64.CT

/-!
# XTS-AES of data units on AArch64: `Verified`

Correctness (`encrypt_wp`, `decrypt_wp`) and constant time (`encrypt_ct`,
`decrypt_ct`) for the whole-block functions calling any implementation `v`
of the block functions (`xtsE v`, `xtsD v`), a state satisfying the
precondition (`unitSat`), and the shared contracts of
`Spec/Xts/Contract.lean`, with no stack: the calls keep the return address
in `x30`, which the functions save in the scratch buffer.
-/

@[expose] public section

namespace VG.Proof.AesXts.AArch64.Unit

open VG VG.AArch64 VG.Impl.AesXts.AArch64Unit
open VG.Proof.AesCbc (aesWith_state aesInvWith_state)
open VG.Proof.Aes.AArch64 (BlocksImpl)

/-- `vg_aes_xts_encrypt` calling the block functions of `v`, with `v`'s suffix. -/
abbrev xtsE (v : BlocksImpl) : Impl.Aes.AArch64.Blocks :=
  ⟨Spec.Xts.aesEncryptApi.name ++ v.suffix, Impl.AesXts.AArch64.encrypt v.enc⟩

/-- `vg_aes_xts_decrypt` calling the block functions of `v`, with `v`'s suffix. -/
abbrev xtsD (v : BlocksImpl) : Impl.Aes.AArch64.Blocks :=
  ⟨Spec.Xts.aesDecryptApi.name ++ v.suffix, Impl.AesXts.AArch64.decrypt v.dec⟩

theorem crypt_noFrames {b : Impl.Aes.AArch64.Blocks} (h : b.code.noFrames = true) :
    (Impl.AesXts.AArch64.crypt b).noFrames = true := by
  simp [Impl.AesXts.AArch64.crypt, Impl.AesXts.AArch64.batch, Impl.AesXts.AArch64.pass, Code.noFrames, h]

theorem encrypt_keepsV (v : BlocksImpl) : (encrypt (xtsE v)).allInstrs keepsV = true := by
  simp only [encrypt, tweak, encSteal, swap, Code.allInstrs, Proof.AesXts.AArch64.encrypt_keepsV v]; decide +kernel

theorem decrypt_keepsV (v : BlocksImpl) : (decrypt (xtsE v) (xtsD v)).allInstrs keepsV = true := by
  simp only [decrypt, tweak, decSteal, swap, Code.allInstrs, Proof.AesXts.AArch64.encrypt_keepsV v,
    Proof.AesXts.AArch64.decrypt_keepsV v]; decide +kernel

theorem encrypt_correct (v : BlocksImpl) (s : State) (hs : (unitAArch64 true).pre s) :
    ∃ t s', Exec isa (encrypt (xtsE v)) s t s' ∧ abiPreserved s s' ∧ (unitAArch64 true).post s s' :=
  WP.withPreservedV (encrypt_wp (UPre.of hs) (Proof.AesXts.AArch64.encrypt_correct v)
    (crypt_noFrames v.encNoFrames)) (encrypt_keepsV v)

theorem decrypt_correct (v : BlocksImpl) (s : State) (hs : (unitAArch64 false).pre s) :
    ∃ t s', Exec isa (decrypt (xtsE v) (xtsD v)) s t s' ∧ abiPreserved s s' ∧ (unitAArch64 false).post s s' :=
  WP.withPreservedV (decrypt_wp (UPre.of hs) (Proof.AesXts.AArch64.encrypt_correct v)
    (crypt_noFrames v.encNoFrames) (Proof.AesXts.AArch64.decrypt_correct v) (crypt_noFrames v.decNoFrames))
    (decrypt_keepsV v)

theorem xtsE_ct (v : BlocksImpl) :
    ConstantTime isa (AesCbc.AArch64.modeAArch64 (AesXts.xtsMode true)).pre
      (AesCbc.AArch64.modeAArch64 (AesXts.xtsMode true)).pub (xtsE v).code :=
  Proof.AesXts.AArch64.crypt_ct true v.encOk v.encCt v.encNoFrames fun R w m p => (aesWith_state R w m p).symm

theorem xtsD_ct (v : BlocksImpl) :
    ConstantTime isa (AesCbc.AArch64.modeAArch64 (AesXts.xtsMode false)).pre
      (AesCbc.AArch64.modeAArch64 (AesXts.xtsMode false)).pub (xtsD v).code :=
  Proof.AesXts.AArch64.crypt_ct false v.decOk v.decCt v.decNoFrames fun R w m p => (aesInvWith_state R w m p).symm

/-- A state satisfying the precondition: AES-128, a data unit of one block
at `0x4000`, and the scratch buffer at `0x5000`. -/
def unitSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 10 | .x3 => 0x3000 | .x4 => 0x4000 | .x5 => 16 | .x6 => 0x5000
    | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 240⟩, ⟨0x2000, 240⟩, ⟨0x3000, 16⟩]
  wr := [⟨0x4000, 16⟩, ⟨0x5000, 2432⟩]

theorem encrypt_verified (v : BlocksImpl) :
    Verified AArch64.target (encrypt (xtsE v)) (Spec.Xts.aesEncryptUnitContract AArch64.abi) :=
  Verified.of_correct (encrypt_correct v)
    (encrypt_ct (Proof.AesXts.AArch64.encrypt_correct v) (crypt_noFrames v.encNoFrames) (xtsE_ct v)) (by
    sig_implies [Spec.Xts.aesEncryptUnitContract, Spec.Xts.aesUnitSig, Spec.Xts.aesUnitPre,
      Spec.Xts.aesEncryptUnitPost, unitAArch64, unitPre, unitPub, xtsOf, W, K, R, I, D, Len, S, schR, tschR, iR,
      dataR, scrR, AArch64.abi, AArch64.argRegs] [unitSat] using unitSat)

theorem decrypt_verified (v : BlocksImpl) :
    Verified AArch64.target (decrypt (xtsE v) (xtsD v)) (Spec.Xts.aesDecryptUnitContract AArch64.abi) :=
  Verified.of_correct (decrypt_correct v)
    (decrypt_ct (Proof.AesXts.AArch64.encrypt_correct v) (crypt_noFrames v.encNoFrames) (xtsE_ct v)
      (Proof.AesXts.AArch64.decrypt_correct v) (crypt_noFrames v.decNoFrames) (xtsD_ct v)) (by
    sig_implies [Spec.Xts.aesDecryptUnitContract, Spec.Xts.aesUnitSig, Spec.Xts.aesUnitPre,
      Spec.Xts.aesDecryptUnitPost, unitAArch64, unitPre, unitPub, xtsOf, W, K, R, I, D, Len, S, schR, tschR, iR,
      dataR, scrR, AArch64.abi, AArch64.argRegs] [unitSat] using unitSat)

end VG.Proof.AesXts.AArch64.Unit
