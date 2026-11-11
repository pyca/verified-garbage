module

public import VerifiedGarbage.Proof.RsaPss.X86.SgSat
public import VerifiedGarbage.Proof.RsaPss.X86.SgPSat
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
of `MdHash` and MGF1's any of `MdHash`: signing (`sign_ok`, and `signP_ok`
given `pre`) and verification (`verify_ok`), when the registration's check
(`Sg.OK`) holds.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86

open VG VG.X86
open VG.Proof.MdHashTable.X86 (MVar)
open VG.Proof.HashTable.X86 (TVar)

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

/-- `vg_rsa_pss_sign_precomputed`, with the tables of `vs` and `gs` and the
private-key operation of `c` and `w`, given `pre`. -/
theorem signP_ok (vs : List MVar) (gs : List TVar) (hok : Sg.OK vs gs) (c : Proof.Rsa.X86.PrivChecked.CrtImpl)
    (w : Proof.Rsa.X86.PrivChecked.CrtPImpl) :
    Verified target (Sg.signCodeP vs gs c w) (Sg.sspecP vs gs) :=
  Sg.signP_verified hok (let ⟨_, hw, _, hwg, hs⟩ := ok_sat hok; Sg.sign_satP hw hwg hs hok.2.2.2.2.2) c w

/-- `vg_rsa_pss_verify_precomputed`, with the tables of `vs` and `gs` and the
public-key operation of `c`. -/
theorem verify_ok (vs : List MVar) (gs : List TVar) (hok : Sg.OK vs gs) (c : RsaPkcs1Sig.X86.Ver.PublicImpl) :
    Verified target (Vf.verifyCode vs gs c) (Vf.vspec vs gs) :=
  Vf.verify_verified hok (let ⟨_, hw, _, hwg, hs⟩ := ok_sat hok; Vf.verify_sat hw hwg hs hok.2.2.2.2.2) c

end VG.Proof.RsaPss.X86
