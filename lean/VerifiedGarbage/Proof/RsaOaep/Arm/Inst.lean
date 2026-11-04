module

public import VerifiedGarbage.Proof.RsaOaep.Arm.DecVerified
public import VerifiedGarbage.Proof.RsaOaep.Arm.DecSat
public import VerifiedGarbage.Proof.RsaOaep.Arm.EncVerified
public import VerifiedGarbage.Proof.RsaOaep.Arm.EncSat

/-!
# RSAES-OAEP on ARMv7: the instances emitted

What the registrations check of the hash functions whose tables a function
takes (`OK`), and the instances' proofs against the contracts the
registrations state, with both hash functions any of the tables: decryption
(`dec_ok`) and encryption (`enc_ok`).
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

/-- `vg_rsa_oaep_decrypt`, with the tables of `vs` and the private-key
operation over `c`. -/
theorem dec_ok (vs : List TVar) (hok : OK vs) (c : Proof.Rsa.Arm.CrtImpl) :
    Verified target (Dec.decCode vs c) (Dec.dspec vs) :=
  Dec.dec_verified hok.1 (let ⟨_, hw⟩ := hok.mem; Dec.dec_sat hw hok.2.1) c

/-- `vg_rsa_oaep_encrypt_precomputed`, with the tables of `vs`, calling `c`. -/
theorem enc_ok (vs : List TVar) (hok : OK vs) (c : RsaPkcs1Sig.Arm.PdImpl) :
    Verified target (Enc.encryptCode vs c) (Enc.espec vs) :=
  Enc.encrypt_verified hok.1 (let ⟨_, hw⟩ := hok.mem; Enc.encrypt_sat hw hok.2.1) c

end VG.Proof.RsaOaep.Arm
