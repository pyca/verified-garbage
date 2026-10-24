module

public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Verified
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Hashes

/-!
# RSAES-OAEP encryption on PPC64LE: the instances

Untrusted: everything here is checked by Lean. A hash function's streaming
functions with what the proofs need of them (`Link`: `HashOK`, `HashCT`, and
the hash function of `Spec.Mgf1` they compute, among those the label may be
hashed with); `link_verified`: encryption for two of them, which the
registration files bind.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE

open VG VG.PPC64LE
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE

/-- A hash function's streaming functions, with what the proofs need. -/
structure Link (H : Hash) where
  ok : HashOK H
  ct : HashCT ok
  G : Spec.Mgf1.Hash
  hash : ∀ x, G.hash x = ok.SH.H.hash x
  len : G.len = H.D
  mem : G ∈ labelHashes

theorem Link.valid {H : Hash} (l : Link H) : Proof.Mgf1.Valid l.G :=
  ⟨by rw [l.len]; exact l.ok.hD0, fun x => by rw [l.hash, l.ok.hashLen, l.len]⟩

def sha1L : Link Sha1.hash := ⟨Sha1.ok, sha1CT, Spec.Mgf1.sha1, fun _ => rfl, rfl, by simp [labelHashes]⟩
def sha224L : Link Sha224.hash := ⟨Sha224.ok, sha224CT, Spec.Mgf1.sha224, fun _ => rfl, rfl, by simp [labelHashes]⟩
def sha256L : Link Sha256.hash := ⟨Sha256.ok, sha256CT, Spec.Mgf1.sha256, fun _ => rfl, rfl, by simp [labelHashes]⟩
def sha384L : Link Sha384.hash := ⟨Sha384.ok, sha384CT, Spec.Mgf1.sha384, fun _ => rfl, rfl, by simp [labelHashes]⟩
def sha512L : Link Sha512.hash := ⟨Sha512.ok, sha512CT, Spec.Mgf1.sha512, fun _ => rfl, rfl, by simp [labelHashes]⟩
def sha512_224L : Link Sha512_224.hash :=
  ⟨Sha512_224.ok, sha512_224CT, Spec.Mgf1.sha512_224, fun _ => rfl, rfl, by simp [labelHashes]⟩
def sha512_256L : Link Sha512_256.hash :=
  ⟨Sha512_256.ok, sha512_256CT, Spec.Mgf1.sha512_256, fun _ => rfl, rfl, by simp [labelHashes]⟩

/-- `vg_rsa_oaep_<H>_mgf1_<G>_encrypt_precomputed` for the linked hash
functions. -/
theorem link_verified {H G : Hash} (lh : Link H) (lg : Link G) :
    Verified PPC64LE.target (Impl.RsaOaep.PPC64LE.encrypt H G)
      (Spec.RsaOaep.encryptPrecomputedContract lh.G lg.G abi 304) :=
  enc_verified lh.ok lh.ct lg.ok lg.ct lh.hash lh.len lg.hash lg.len lg.valid (enc_sat lg.G lh.mem)

end VG.Proof.RsaOaep.PPC64LE
