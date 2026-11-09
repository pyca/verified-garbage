module
public import VerifiedGarbage.Impl.AesXts.X86
public import VerifiedGarbage.Proof.Aes.X86.BlocksVariant
public import VerifiedGarbage.Spec.Xts.Contract

import VerifiedGarbage.Proof.AesCbc.X86.Verified
import VerifiedGarbage.Proof.AesXts.X86.CT
import VerifiedGarbage.Proof.Aes.X86.AesNi.Lit
import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# XTS-AES on x86: `Verified`

Correctness and constant time (for any implementation `v` of the block
functions), from `crypt_wp` and `crypt_ct`, a state satisfying the
precondition, and the shared contracts of `Spec/Xts/Contract.lean`, with 24
bytes of stack: the call of the block function pushes its five arguments and
the return address.
-/

@[expose] public section

namespace VG.Proof.AesXts.X86

open VG VG.X86 VG.Impl.AesXts.X86
open VG.Proof.AesCbc (ciphOf aesWith_state aesInvWith_state)
open VG.Proof.AesCbc.X86
open VG.Proof.Aes.X86 (BlocksImpl)

theorem encrypt_spSafe (v : BlocksImpl) : (encrypt v.enc).all (fun i => !isa.writesSp i) = true := by
  simp only [encrypt, crypt, batch, pass, Impl.AesOcb.X86.blocksFrame, Code.all, v.encSpSafe]
  decide +kernel

theorem decrypt_spSafe (v : BlocksImpl) : (decrypt v.dec).all (fun i => !isa.writesSp i) = true := by
  simp only [decrypt, crypt, batch, pass, Impl.AesOcb.X86.blocksFrame, Code.all, v.decSpSafe]
  decide +kernel

end VG.Proof.AesXts.X86
