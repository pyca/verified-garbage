module
public import VerifiedGarbage.Impl.AesXts.AArch64
public import VerifiedGarbage.Proof.Aes.AArch64.BlocksVariant
public import VerifiedGarbage.Proof.AesCbc.AArch64.Call
public import VerifiedGarbage.Proof.AesXts.Spec
public import VerifiedGarbage.Spec.Xts.Contract

import VerifiedGarbage.Proof.AesCbc.AArch64.Verified
import VerifiedGarbage.Proof.AesXts.AArch64.CT
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Aes.AArch64.CodeLit

/-!
# XTS-AES on AArch64: `Verified`

Correctness and constant time (for any implementation `v` of the block
functions), from `crypt_wp` and `crypt_ct`, a state satisfying the
precondition, and the shared contracts of `Spec/Xts/Contract.lean` (with no
stack: the call keeps the return address in `x30`, which the functions save
in the scratch buffer).
-/

@[expose] public section

namespace VG.Proof.AesXts.AArch64

open VG VG.AArch64 VG.Impl.AesXts.AArch64
open VG.Proof.AesCbc (ciphOf aesWith_state aesInvWith_state)
open VG.Proof.AesCbc.AArch64
open VG.Proof.Aes.AArch64 (BlocksImpl)

theorem encrypt_keepsV (v : BlocksImpl) : (encrypt v.enc).allInstrs keepsV = true := by
  simp only [encrypt, crypt, batch, pass, Code.allInstrs, v.encKeepsV]; decide +kernel

theorem encrypt_correct (v : BlocksImpl) (s : State) (hs : (modeAArch64 (AesXts.xtsMode true)).pre s) :
    ∃ t s', Exec isa (encrypt v.enc) s t s' ∧ abiPreserved s s' ∧ (modeAArch64 (AesXts.xtsMode true)).post s s' :=
  WP.withPreservedV (crypt_wp true v.encOk v.encNoFrames (fun R w m p => (aesWith_state R w m p).symm) hs)
    (encrypt_keepsV v)

theorem decrypt_keepsV (v : BlocksImpl) : (decrypt v.dec).allInstrs keepsV = true := by
  simp only [decrypt, crypt, batch, pass, Code.allInstrs, v.decKeepsV]; decide +kernel

theorem decrypt_correct (v : BlocksImpl) (s : State) (hs : (modeAArch64 (AesXts.xtsMode false)).pre s) :
    ∃ t s', Exec isa (decrypt v.dec) s t s' ∧ abiPreserved s s' ∧ (modeAArch64 (AesXts.xtsMode false)).post s s' :=
  WP.withPreservedV (crypt_wp false v.decOk v.decNoFrames (fun R w m p => (aesInvWith_state R w m p).symm) hs)
    (decrypt_keepsV v)

end VG.Proof.AesXts.AArch64
