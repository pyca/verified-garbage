module

public import VerifiedGarbage.Proof.AesCbc.AArch64.Encrypt.Verified
public import VerifiedGarbage.Proof.AesCbc.AArch64.Verified

/-! Specialize the AES-instruction caller while preserving generic composition. -/

@[expose] public section
namespace VG.Proof.AesCbc.AArch64.Caller
open VG VG.AArch64 VG.Proof.Aes.AArch64

/-- Other block variants continue through their generic verified caller. -/
def encrypt (v : BlocksImpl) : Prog isa :=
  if v.enc.name="vg_aes_encrypt_blocks_aes" then Impl.AesCbc.AArch64.Encrypt.code
  else Impl.AesCbc.AArch64.encrypt v.enc

def written (v : BlocksImpl) : List (String × Nat) :=
  if v.enc.name="vg_aes_encrypt_blocks_aes" then [("scratch",0)] else []

theorem verified (v : BlocksImpl) :
    Verified AArch64.target (encrypt v) (Spec.Cbc.aesEncryptContract AArch64.abi) := by
  unfold encrypt
  split
  · exact Encrypt.verified
  · exact encrypt_verified v

theorem written_ok (v : BlocksImpl) (s : State) (tr : List Leak) (t : State)
    (hp : (Spec.Cbc.aesEncryptContract AArch64.abi).pre s) (he : Exec isa (encrypt v) s tr t) :
    Sig.writtenWithin (AArch64.abi.withConsts []) Spec.Cbc.aesSig (written v) s t := by
  by_cases h : v.enc.name="vg_aes_encrypt_blocks_aes"
  · rw [encrypt,ite_eq_left h] at he
    rw [written,ite_eq_left h]
    exact Encrypt.written s tr t hp he
  · rw [written,ite_eq_right h]
    trivial
end VG.Proof.AesCbc.AArch64.Caller
