module

public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Verified
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.Verified

/-!
# RSAES-OAEP on PPC64LE: the instances emitted

Untrusted: everything here is checked by Lean. What the registration checks
of the hash functions whose tables a function takes (`OK`), and the
instances' proofs against the contracts it states: encryption (`enc_ok`)
and decryption (`dec_ok`) for a label hash function `H` (`Link`), with
MGF1's hash function any of `vs`' tables.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE

open VG VG.PPC64LE
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.HashTable.PPC64LE (TVar tables names Coh fnsOf)

/-- What the registration checks of the hash functions whose tables a
function takes: their functions of the same name have the same code, there
are not too many to give distinct addresses in the witnesses, and there is
one. -/
def OK (vs : List TVar) : Prop := Coh vs ∧ (names vs).length < 2 ^ 32 ∧ vs ≠ []

instance (vs : List TVar) : Decidable (OK vs) := by unfold OK; infer_instance

theorem OK.mem {vs : List TVar} (h : OK vs) : ∃ w, w ∈ vs := List.exists_mem_of_ne_nil _ h.2.2

/-- `vg_rsa_oaep_<H>_mgf1_encrypt_precomputed`, with the tables of `vs`. -/
theorem enc_ok {H : Hash} (lh : Link H) (vs : List TVar) (hok : OK vs) :
    Verified PPC64LE.target (Impl.RsaOaep.PPC64LE.encrypt H (fnsOf vs)) (encSpec lh.G (tables vs)) :=
  enc_verified lh.ok lh.ct lh.hash lh.len hok.1 (let ⟨_, hw⟩ := hok.mem; enc_sat lh.mem hw hok.2.1)

/-- `vg_rsa_oaep_<H>_mgf1_decrypt`, with the tables of `vs`. -/
theorem dec_ok {H : Hash} (lh : Link H) (vs : List TVar) (hok : OK vs) :
    Verified PPC64LE.target (Impl.RsaOaep.PPC64LE.Dec.decrypt H (fnsOf vs)) (Dec.decSpec lh.G (tables vs)) :=
  Dec.dec_verified lh.ok lh.ct lh.hash lh.len lh.valid hok.1 (let ⟨_, hw⟩ := hok.mem; Dec.dec_sat lh.G hw hok.2.1)

end VG.Proof.RsaOaep.PPC64LE
