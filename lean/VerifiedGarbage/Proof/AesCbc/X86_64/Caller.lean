module

public import VerifiedGarbage.Proof.AesCbc.Rounds
public import VerifiedGarbage.Proof.AesCbc.X86_64.Encrypt
public import VerifiedGarbage.Proof.AesCbc.X86_64.Decrypt
public import VerifiedGarbage.Proof.AesCbc.X86_64.VaesDecrypt
public import VerifiedGarbage.Proof.AesCbc.X86_64.Verified

-- separate module: generic registrations bind these choices without containing proof code.

/-! # Specializing CBC's hardware loops while retaining generic callers -/

@[expose] public section
namespace VG.Proof.AesCbc.X86_64.Caller
open VG VG.X86_64 VG.Proof.Aes.X86_64

def hardware (v : BlocksImpl) : Bool :=
  v.enc.name == "vg_aes_encrypt_blocks_aesni" || v.enc.name == "vg_aes_encrypt_blocks_vaes"

def encrypt (v : BlocksImpl) : Prog isa :=
  if hardware v then Impl.AesCbc.X86_64.Encrypt.encrypt else Impl.AesCbc.X86_64.encrypt v.enc

def encFeatures (v : BlocksImpl) : List String := if hardware v then ["aes"] else v.features

theorem verified (v : BlocksImpl) :
    Verified X86_64.target (encrypt v) (Proof.AesCbc.encryptRoundsContract X86_64.abi 8) := by
  unfold encrypt
  split
  · exact Encrypt.verified
  · exact encrypt_verified v

theorem spSafe (v : BlocksImpl) : (encrypt v).all (fun i => !isa.writesSp i) = true := by
  unfold encrypt
  split
  · decide +kernel
  · exact encrypt_spSafe v

def written (v : BlocksImpl) : List (String × Nat) := if hardware v then [("scratch", 0)] else []

theorem written_ok (v : BlocksImpl) (s : State) (tr : List Leak) (t : State)
    (hp : (Proof.AesCbc.encryptRoundsContract X86_64.abi 8).pre s) (he : Exec isa (encrypt v) s tr t) :
    Sig.writtenWithin (X86_64.abi.withConsts []) Spec.Cbc.aesSig (written v) s t := by
  unfold encrypt at he
  unfold written
  split at he
  · rename_i h
    rw [ite_eq_left h]
    exact Encrypt.written s tr t hp he
  · rename_i h
    rw [ite_eq_right h]
    trivial

def vaes (v : BlocksImpl) : Bool := v.dec.name == "vg_aes_decrypt_blocks_vaes"

def decrypt (v : BlocksImpl) : Prog isa :=
  if vaes v then Impl.AesCbc.X86_64.VaesDecrypt.decrypt
  else if hardware v then Impl.AesCbc.X86_64.Decrypt.decrypt else Impl.AesCbc.X86_64.decrypt v.dec

def decFeatures (v : BlocksImpl) : List String :=
  if vaes v then ["aes","avx","avx2","vaes"] else if hardware v then ["aes"] else v.features

theorem decryptVerified (v : BlocksImpl) :
    Verified X86_64.target (decrypt v) (Proof.AesCbc.decryptRoundsContract X86_64.abi 8) := by
  unfold decrypt
  split
  · exact VaesDecrypt.verified
  · split
    · exact Decrypt.verified
    · exact decrypt_verified v

theorem decryptSpSafe (v : BlocksImpl) : (decrypt v).all (fun i => !isa.writesSp i) = true := by
  unfold decrypt
  split
  · decide +kernel
  · split
    · decide +kernel
    · exact decrypt_spSafe v

def decWritten (v : BlocksImpl) : List (String × Nat) :=
  if vaes v then [("scratch",224)] else if hardware v then [("scratch",224)] else []

theorem decWritten_ok (v : BlocksImpl) (s : State) (tr : List Leak) (t : State)
    (hp : (Proof.AesCbc.decryptRoundsContract X86_64.abi 8).pre s) (he : Exec isa (decrypt v) s tr t) :
    Sig.writtenWithin (X86_64.abi.withConsts []) Spec.Cbc.aesSig (decWritten v) s t := by
  unfold decrypt at he
  unfold decWritten
  split at he
  · rename_i h
    rw [ite_eq_left h]
    exact VaesDecrypt.written s tr t hp he
  · rename_i h
    rw [ite_eq_right h]
    split at he
    · rename_i hh
      rw [ite_eq_left hh]
      exact Decrypt.written s tr t hp he
    · rename_i hh
      rw [ite_eq_right hh]
      trivial

end VG.Proof.AesCbc.X86_64.Caller
