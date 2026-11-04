module

public import VerifiedGarbage.Proof.RsaPss.X86.SgSat
public import VerifiedGarbage.Proof.RsaPss.X86.VfSat
public import VerifiedGarbage.Proof.RsaPss.X86.Hashes.Md5
public import VerifiedGarbage.Proof.RsaPss.X86.Hashes.Sha1
public import VerifiedGarbage.Proof.RsaPss.X86.Hashes.Sha224
public import VerifiedGarbage.Proof.RsaPss.X86.Hashes.Sha256
public import VerifiedGarbage.Proof.RsaPss.X86.Hashes.Sha512
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyInstances

/-!
# RSASSA-PSS on x86: the instances emitted

The variants of the hash functions whose tables of `MdHash` the functions
take (`mvars`: MD5's, SHA-1's and SHA-224's and SHA-256's with each of their
backends, and the SHA-512 family's), and the instances' proofs against the
contracts the registrations state, with the hash function any of the tables
of `MdHash` and MGF1's any of `Hash`: signing (`sign_ok`) and verification
(`verify_ok`), when the registration's check (`Sg.OK`) holds.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86

open VG VG.X86
open VG.Proof.MdHashTable.X86 (MVar)
open VG.Proof.HashTable.X86 (TVar)

def md5W : MVar := ⟨md5, "", [], rfl⟩
def sha1W (b : Proof.Sha1.X86.Variants.Backend) : MVar := ⟨sha1 b, b.stream.suffix, b.features, rfl⟩
def sha224W (b : Proof.Sha256.X86.Variants.Backend) : MVar := ⟨sha224 b, b.stream.suffix, b.features, rfl⟩
def sha256W (b : Proof.Sha256.X86.Variants.Backend) : MVar := ⟨sha256 b, b.stream.suffix, b.features, rfl⟩
def sha384W : MVar := ⟨sha384, "", [], rfl⟩
def sha512W : MVar := ⟨sha512, "", [], rfl⟩
def sha512_224W : MVar := ⟨sha512_224, "", [], rfl⟩
def sha512_256W : MVar := ⟨sha512_256, "", [], rfl⟩

/-- Every variant: MD5's, SHA-1's with the backends `vs1`, SHA-224's and
SHA-256's with `vs256`, and the SHA-512 family's. -/
def mvars (vs1 : List Proof.Sha1.X86.Variants.Backend) (vs256 : List Proof.Sha256.X86.Variants.Backend) :
    List MVar :=
  md5W :: (vs1.map sha1W ++ vs256.map sha224W ++ vs256.map sha256W ++ [sha384W, sha512W, sha512_224W, sha512_256W])

variable {vs : List MVar} {gs : List TVar}

theorem ok_sat (hok : Sg.OK vs gs) : ∃ w ∈ vs, ∃ wg ∈ gs, Proof.MdHashTable.X86.Shape w := by
  obtain ⟨w, hw, -⟩ := hok.2.2.2.1 0 (by decide)
  obtain ⟨wg, hwg⟩ := List.exists_mem_of_ne_nil _ hok.2.2.2.2.1
  exact ⟨w, hw, wg, hwg, hok.2.1 w hw⟩

/-- `vg_rsa_pss_sign`, with the tables of `vs` and `gs` and the private-key
operation of `c`. -/
theorem sign_ok (vs : List MVar) (gs : List TVar) (hok : Sg.OK vs gs) (c : Proof.Rsa.X86.PrivChecked.CrtImpl) :
    Verified target (Sg.signCode vs gs c) (Sg.sspec vs gs) :=
  Sg.sign_verified hok (let ⟨_, hw, _, hwg, hs⟩ := ok_sat hok; Sg.sign_sat hw hwg hs hok.2.2.2.2.2) c

/-- `vg_rsa_pss_verify_precomputed`, with the tables of `vs` and `gs` and the
public-key operation of `c`. -/
theorem verify_ok (vs : List MVar) (gs : List TVar) (hok : Sg.OK vs gs) (c : RsaPkcs1Sig.X86.Ver.PublicImpl) :
    Verified target (Vf.verifyCode vs gs c) (Vf.vspec vs gs) :=
  Vf.verify_verified hok (let ⟨_, hw, _, hwg, hs⟩ := ok_sat hok; Vf.verify_sat hw hwg hs hok.2.2.2.2.2) c

end VG.Proof.RsaPss.X86
