module

public import VerifiedGarbage.Proof.RsaOaep.X86.Dec.Verified
public import VerifiedGarbage.Proof.RsaOaep.X86.Dec.Sat
public import VerifiedGarbage.Proof.RsaOaep.X86.Enc.Verified
public import VerifiedGarbage.Proof.RsaOaep.X86.Enc.Sat
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyInstances

/-!
# RSAES-OAEP on x86: the instances emitted

What the registrations check of the variants whose tables a function takes
(`OK`), and the instances' proofs against the contracts the registrations
state: decryption for any label hash function (`dec_ok`), encryption for
each the satisfiability witnesses cover (`enc_ok`, `enc_ok_<hash>`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86

open VG VG.X86
open VG.Proof.HashTable.X86 (TVar tables names Coh)

/-- What the registrations check of the variants whose tables a function
takes: their functions of the same name have the same code, there are not
too many to give distinct addresses in the witnesses, and there is one. -/
def OK (vs : List TVar) : Prop := Coh vs ∧ (names vs).length < 2 ^ 24 ∧ vs ≠ []

instance (vs : List TVar) : Decidable (OK vs) := by unfold OK; infer_instance

theorem OK.mem {vs : List TVar} (h : OK vs) : ∃ w, w ∈ vs := List.exists_mem_of_ne_nil _ h.2.2

/-- `vg_rsa_oaep_<H>_mgf1_decrypt`, for the label's hash function `h`, with
the tables of `vs` and the private-key operation of `c`. -/
theorem dec_ok (h : OHash) (vs : List TVar) (hok : OK vs) (c : Proof.Rsa.X86.PrivChecked.CrtImpl) :
    Verified target (Dec.decCode h vs c) (Dec.dspec h vs) :=
  Dec.dec_verified hok.1 (let ⟨_, hw⟩ := hok.mem; Dec.dec_sat h.G hw hok.2.1) c

/-- `vg_rsa_oaep_<H>_mgf1_encrypt_precomputed`, for the label's hash
function `h`, with the tables of `vs`. -/
theorem enc_ok (h : OHash) (hH : h.G ∈ Enc.hashes) (vs : List TVar) (hok : OK vs) :
    Verified target (Enc.encryptCode h vs RsaPkcs1Sig.X86.Ver.baseline) (Enc.espec h vs) :=
  Enc.encrypt_verified hok.1 (let ⟨_, hw⟩ := hok.mem; Enc.encrypt_sat hH hw hok.2.1) _

theorem enc_ok_sha1 (v : Proof.Sha1.X86.Variants.Backend) (vs : List TVar) (hok : OK vs) :
    Verified target (Enc.encryptCode (sha1 v) vs RsaPkcs1Sig.X86.Ver.baseline) (Enc.espec (sha1 v) vs) :=
  enc_ok (sha1 v) (List.mem_cons_self ..) vs hok

theorem enc_ok_sha224 (v : Proof.Sha256.X86.Variants.Backend) (vs : List TVar) (hok : OK vs) :
    Verified target (Enc.encryptCode (sha224 v) vs RsaPkcs1Sig.X86.Ver.baseline) (Enc.espec (sha224 v) vs) :=
  enc_ok (sha224 v) (List.mem_cons_of_mem _ (List.mem_cons_self ..)) vs hok

theorem enc_ok_sha256 (v : Proof.Sha256.X86.Variants.Backend) (vs : List TVar) (hok : OK vs) :
    Verified target (Enc.encryptCode (sha256 v) vs RsaPkcs1Sig.X86.Ver.baseline) (Enc.espec (sha256 v) vs) :=
  enc_ok (sha256 v) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) vs hok

theorem enc_ok_sha384 (vs : List TVar) (hok : OK vs) :
    Verified target (Enc.encryptCode sha384 vs RsaPkcs1Sig.X86.Ver.baseline) (Enc.espec sha384 vs) :=
  enc_ok sha384 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))) vs hok

theorem enc_ok_sha512 (vs : List TVar) (hok : OK vs) :
    Verified target (Enc.encryptCode sha512 vs RsaPkcs1Sig.X86.Ver.baseline) (Enc.espec sha512 vs) :=
  enc_ok sha512 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))) vs hok

theorem enc_ok_sha512_224 (vs : List TVar) (hok : OK vs) :
    Verified target (Enc.encryptCode sha512_224 vs RsaPkcs1Sig.X86.Ver.baseline) (Enc.espec sha512_224 vs) :=
  enc_ok sha512_224 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))) vs hok

theorem enc_ok_sha512_256 (vs : List TVar) (hok : OK vs) :
    Verified target (Enc.encryptCode sha512_256 vs RsaPkcs1Sig.X86.Ver.baseline) (Enc.espec sha512_256 vs) :=
  enc_ok sha512_256 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))) vs hok

end VG.Proof.RsaOaep.X86
