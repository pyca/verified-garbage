module

public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Verified
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Hashes
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Md5

/-!
# RSASSA-PSS verification on PPC64LE: the instances

Untrusted: everything here is checked by Lean. MD5's streaming functions
are constant time for the contracts the proofs call them by (`md5CT`), from
their artifacts' proofs, as SHA-1's and the SHA-2 family's are
(`Proof/RsaOaep/PPC64LE/Hashes.lean`). A hash function's streaming
functions with what the proofs need of them (`Link`: `HashOK`, `HashCT`, and
the hash function of `Spec.Mgf1` they compute, among those verification
uses); `link_verified`: verification for one of them, which the
registration files bind.
-/

@[expose] public section

namespace VG.Proof.RsaPss.PPC64LE

open VG VG.PPC64LE
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE
open VG.Proof.RsaOaep.PPC64LE (HashCT ct_mono sha1CT sha224CT sha256CT sha384CT sha512CT sha512_224CT sha512_256CT)

theorem md5CT : HashCT Md5.ok where
  init := ct_mono Proof.Md5.PPC64LE.Stream.init_verified.2.1 (fun _ hs => ⟨hs.1, hs.2.1⟩) fun _ _ h => h
  upd := ct_mono Proof.Md5.PPC64LE.Stream.Update.update_verified.2.1 (fun _ hs => hs) fun _ _ h => h
  fin := ct_mono Proof.Md5.PPC64LE.Stream.Finalize.finalize_verified.2.1 (fun _ hs => hs) fun _ _ h => h

/-- A hash function's streaming functions, with what the proofs need. -/
structure Link (H : Hash) where
  ok : HashOK H
  ct : HashCT ok
  G : Spec.Mgf1.Hash
  hash : ∀ x, G.hash x = ok.SH.H.hash x
  len : G.len = H.D
  mem : G ∈ pssHashes

theorem Link.valid {H : Hash} (l : Link H) : Proof.Mgf1.Valid l.G :=
  ⟨by rw [l.len]; exact l.ok.hD0, fun x => by rw [l.hash, l.ok.hashLen, l.len]⟩

def md5L : Link Md5.hash := ⟨Md5.ok, md5CT, Spec.Mgf1.md5, fun _ => rfl, rfl, by simp [pssHashes]⟩
def sha1L : Link Sha1.hash := ⟨Sha1.ok, sha1CT, Spec.Mgf1.sha1, fun _ => rfl, rfl, by simp [pssHashes]⟩
def sha224L : Link Sha224.hash := ⟨Sha224.ok, sha224CT, Spec.Mgf1.sha224, fun _ => rfl, rfl, by simp [pssHashes]⟩
def sha256L : Link Sha256.hash := ⟨Sha256.ok, sha256CT, Spec.Mgf1.sha256, fun _ => rfl, rfl, by simp [pssHashes]⟩
def sha384L : Link Sha384.hash := ⟨Sha384.ok, sha384CT, Spec.Mgf1.sha384, fun _ => rfl, rfl, by simp [pssHashes]⟩
def sha512L : Link Sha512.hash := ⟨Sha512.ok, sha512CT, Spec.Mgf1.sha512, fun _ => rfl, rfl, by simp [pssHashes]⟩
def sha512_224L : Link Sha512_224.hash :=
  ⟨Sha512_224.ok, sha512_224CT, Spec.Mgf1.sha512_224, fun _ => rfl, rfl, by simp [pssHashes]⟩
def sha512_256L : Link Sha512_256.hash :=
  ⟨Sha512_256.ok, sha512_256CT, Spec.Mgf1.sha512_256, fun _ => rfl, rfl, by simp [pssHashes]⟩

/-- `vg_rsa_pss_<H>_mgf1_<H>_verify_precomputed` for a linked hash function. -/
theorem link_verified {H : Hash} (l : Link H) :
    Verified PPC64LE.target (Impl.RsaPss.PPC64LE.verifyPrecomputed H)
      (Spec.RsaPss.verifyPrecomputedContract l.G l.G abi 304) :=
  verify_verified l.ok l.ct l.hash l.len l.valid (verify_sat l.mem)

end VG.Proof.RsaPss.PPC64LE
