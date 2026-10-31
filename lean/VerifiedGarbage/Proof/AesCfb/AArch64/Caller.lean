module

import VerifiedGarbage.Proof.AesCfb.AArch64.Decrypt.Verified
import VerifiedGarbage.Proof.AesCfb.AArch64.Verified
public import VerifiedGarbage.Impl.AesCfb.AArch64
public import VerifiedGarbage.Impl.AesCfb.AArch64.Decrypt
public import VerifiedGarbage.Proof.Aes.AArch64.BlocksVariant
public import VerifiedGarbage.Proof.AesCbc.AArch64.Block
public import VerifiedGarbage.Spec.Cfb.Contract

/-! Specialize the AES-instruction caller while preserving generic composition. -/

@[expose] public section
namespace VG.Proof.AesCfb.AArch64.Caller
open VG VG.AArch64 VG.Proof.Aes.AArch64

/-- Other block variants continue through their generic verified caller. -/
def decrypt (v : BlocksImpl) : Prog isa :=
  if v.enc.name="vg_aes_encrypt_blocks_aes" then Impl.AesCfb.AArch64.Decrypt.code
  else Impl.AesCfb.AArch64.decrypt v.enc

def written (v : BlocksImpl) : List (String × Nat) :=
  if v.enc.name="vg_aes_encrypt_blocks_aes" then [("scratch",0)] else []

theorem verified (v : BlocksImpl) :
    Verified AArch64.target (decrypt v) (Spec.Cfb.aesDecryptContract AArch64.abi) := by
  unfold decrypt
  split
  · exact Decrypt.verified
  · exact decrypt_verified v

theorem written_ok (v : BlocksImpl) (s : State) (tr : List Leak) (t : State)
    (hp : (Spec.Cfb.aesDecryptContract AArch64.abi).pre s) (he : Exec isa (decrypt v) s tr t) :
    Sig.writtenWithin (AArch64.abi.withConsts []) Spec.Cfb.aesSig (written v) s t := by
  by_cases h : v.enc.name="vg_aes_encrypt_blocks_aes"
  · rw [decrypt,ite_eq_left h] at he
    rw [written,ite_eq_left h]
    exact Decrypt.written s tr t hp he
  · rw [written,ite_eq_right h]
    trivial
end VG.Proof.AesCfb.AArch64.Caller
