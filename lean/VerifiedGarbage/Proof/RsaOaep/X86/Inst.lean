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
state, with both hash functions any of the tables: decryption (`dec_ok`)
and encryption (`enc_ok`).
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

/-- `vg_rsa_oaep_decrypt`, with the tables of `vs` and the private-key
operation of `c`. -/
theorem dec_ok (vs : List TVar) (hok : OK vs) (c : Proof.Rsa.X86.PrivChecked.CrtImpl) :
    Verified target (Dec.decCode vs c) (Dec.dspec vs) :=
  Dec.dec_verified hok.1 (let ⟨_, hw⟩ := hok.mem; Dec.dec_sat hw hok.2.1) c

/-- `vg_rsa_oaep_encrypt_precomputed`, with the tables of `vs`. -/
theorem enc_ok (vs : List TVar) (hok : OK vs) :
    Verified target (Enc.encryptCode vs RsaPkcs1Sig.X86.Ver.baseline) (Enc.espec vs) :=
  Enc.encrypt_verified hok.1 (let ⟨_, hw⟩ := hok.mem; Enc.encrypt_sat hw hok.2.1) _

end VG.Proof.RsaOaep.X86
