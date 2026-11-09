module

public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Verified
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.Verified

/-!
# RSAES-OAEP on PPC64LE: the instances emitted

Untrusted: everything here is checked by Lean. What the registration checks
of the hash functions whose tables a function takes (`OK`), and the
instances' proofs against the contracts it states: encryption (`enc_ok`)
and decryption (`dec_ok`), with both hash functions any of `vs`' tables.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE

open VG VG.PPC64LE
open VG.Proof.MdHashTable.PPC64LE (MVar tables names Coh fns3)

/-- What the registration checks of the hash functions whose tables a
function takes: their functions of the same name have the same code, there
are not too many to give distinct addresses in the witnesses, and there is
one. -/
def OK (vs : List MVar) : Prop := Coh vs ∧ (names vs).length < 2 ^ 32 ∧ vs ≠ []

instance (vs : List MVar) : Decidable (OK vs) := by unfold OK; infer_instance

theorem OK.mem {vs : List MVar} (h : OK vs) : ∃ w, w ∈ vs := List.exists_mem_of_ne_nil _ h.2.2

/-- `vg_rsa_oaep_encrypt_precomputed`, with the tables of `vs`. -/
theorem enc_ok (vs : List MVar) (hok : OK vs) :
    Verified PPC64LE.target (Impl.RsaOaep.PPC64LE.encrypt (fns3 vs)) (encSpec (tables vs)) :=
  enc_verified hok.1 (let ⟨_, hw⟩ := hok.mem; enc_sat hw hok.2.1)

/-- `vg_rsa_oaep_decrypt`, with the tables of `vs`. -/
theorem dec_ok (vs : List MVar) (hok : OK vs) :
    Verified PPC64LE.target (Impl.RsaOaep.PPC64LE.Dec.decrypt (fns3 vs)) (Dec.decSpec (tables vs)) :=
  Dec.dec_verified hok.1 (let ⟨_, hw⟩ := hok.mem; Dec.dec_sat hw hok.2.1)

end VG.Proof.RsaOaep.PPC64LE
