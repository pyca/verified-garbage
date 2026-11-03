module

public import VerifiedGarbage.Proof.RsaOaep.Arm.DecVerified
public import VerifiedGarbage.Proof.RsaOaep.Arm.DecSat
public import VerifiedGarbage.Proof.RsaOaep.Arm.EncVerified
public import VerifiedGarbage.Proof.RsaOaep.Arm.EncSat

/-!
# RSAES-OAEP on ARMv7: the instances emitted

What the registrations check of the hash functions whose tables a function
takes (`OK`), and the instances' proofs against the contracts the
registrations state: decryption for any label hash function (`dec_ok`),
encryption for each the satisfiability witnesses cover (`enc_ok`,
`enc_ok_<hash>`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.Arm

open VG VG.Arm
open VG.Proof.HashTable.Arm (TVar tables names Coh)

/-- What the registrations check of the hash functions whose tables a
function takes: their functions of the same name have the same code, there
are not too many to give distinct addresses in the witnesses, and there is
one. -/
def OK (vs : List TVar) : Prop := Coh vs ∧ (names vs).length < 2 ^ 24 ∧ vs ≠ []

instance (vs : List TVar) : Decidable (OK vs) := by unfold OK; infer_instance

theorem OK.mem {vs : List TVar} (h : OK vs) : ∃ w, w ∈ vs := List.exists_mem_of_ne_nil _ h.2.2

/-- `vg_rsa_oaep_<H>_mgf1_decrypt`, for the label's hash function `h`, with
the tables of `vs` and the private-key operation over `c`. -/
theorem dec_ok (h : OHash) (vs : List TVar) (hok : OK vs) (c : Proof.Rsa.Arm.CrtImpl) :
    Verified target (Dec.decCode h vs c) (Dec.dspec h vs) :=
  Dec.dec_verified hok.1 (let ⟨_, hw⟩ := hok.mem; Dec.dec_sat h.G hw hok.2.1) c

/-- `vg_rsa_oaep_<H>_mgf1_encrypt_precomputed`, for the label's hash
function `h`, with the tables of `vs`, calling `c`. -/
theorem enc_ok (h : OHash) (hH : h.G ∈ Enc.hashes) (vs : List TVar) (hok : OK vs) (c : RsaPkcs1Sig.Arm.PdImpl) :
    Verified target (Enc.encryptCode h vs c) (Enc.espec h vs) :=
  Enc.encrypt_verified hok.1 (let ⟨_, hw⟩ := hok.mem; Enc.encrypt_sat hH hw hok.2.1) c

theorem enc_ok_sha1 (vs : List TVar) (hok : OK vs) (c : RsaPkcs1Sig.Arm.PdImpl) :
    Verified target (Enc.encryptCode (OHash.ofPss Proof.RsaPss.Arm.sha1) vs c) (Enc.espec (OHash.ofPss Proof.RsaPss.Arm.sha1) vs) :=
  enc_ok (OHash.ofPss Proof.RsaPss.Arm.sha1) (List.mem_cons_self ..) vs hok c

theorem enc_ok_sha224 (vs : List TVar) (hok : OK vs) (c : RsaPkcs1Sig.Arm.PdImpl) :
    Verified target (Enc.encryptCode (OHash.ofPss Proof.RsaPss.Arm.sha224) vs c) (Enc.espec (OHash.ofPss Proof.RsaPss.Arm.sha224) vs) :=
  enc_ok (OHash.ofPss Proof.RsaPss.Arm.sha224) (List.mem_cons_of_mem _ (List.mem_cons_self ..)) vs hok c

theorem enc_ok_sha256 (vs : List TVar) (hok : OK vs) (c : RsaPkcs1Sig.Arm.PdImpl) :
    Verified target (Enc.encryptCode (OHash.ofPss Proof.RsaPss.Arm.sha256) vs c) (Enc.espec (OHash.ofPss Proof.RsaPss.Arm.sha256) vs) :=
  enc_ok (OHash.ofPss Proof.RsaPss.Arm.sha256) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) vs hok c

theorem enc_ok_sha384 (vs : List TVar) (hok : OK vs) (c : RsaPkcs1Sig.Arm.PdImpl) :
    Verified target (Enc.encryptCode (OHash.ofPss Proof.RsaPss.Arm.sha384) vs c) (Enc.espec (OHash.ofPss Proof.RsaPss.Arm.sha384) vs) :=
  enc_ok (OHash.ofPss Proof.RsaPss.Arm.sha384) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))) vs hok c

theorem enc_ok_sha512 (vs : List TVar) (hok : OK vs) (c : RsaPkcs1Sig.Arm.PdImpl) :
    Verified target (Enc.encryptCode (OHash.ofPss Proof.RsaPss.Arm.sha512) vs c) (Enc.espec (OHash.ofPss Proof.RsaPss.Arm.sha512) vs) :=
  enc_ok (OHash.ofPss Proof.RsaPss.Arm.sha512) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))) vs hok c

theorem enc_ok_sha512_224 (vs : List TVar) (hok : OK vs) (c : RsaPkcs1Sig.Arm.PdImpl) :
    Verified target (Enc.encryptCode (OHash.ofPss Proof.RsaPss.Arm.sha512_224) vs c) (Enc.espec (OHash.ofPss Proof.RsaPss.Arm.sha512_224) vs) :=
  enc_ok (OHash.ofPss Proof.RsaPss.Arm.sha512_224) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))) vs hok c

theorem enc_ok_sha512_256 (vs : List TVar) (hok : OK vs) (c : RsaPkcs1Sig.Arm.PdImpl) :
    Verified target (Enc.encryptCode (OHash.ofPss Proof.RsaPss.Arm.sha512_256) vs c) (Enc.espec (OHash.ofPss Proof.RsaPss.Arm.sha512_256) vs) :=
  enc_ok (OHash.ofPss Proof.RsaPss.Arm.sha512_256) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))) vs hok c

end VG.Proof.RsaOaep.Arm
