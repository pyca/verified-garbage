module

public import VerifiedGarbage.Proof.RsaOaep.RISCV64.Verified
public import VerifiedGarbage.Proof.RsaOaep.RISCV64.Dc.Verified
public import VerifiedGarbage.Proof.RsaOaep.RISCV64.Dc.DecP

/-!
# RSAES-OAEP on RISC-V: the instances emitted

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaOaep/PPC64LE/Inst.lean`): what the registration checks of the
hash functions whose tables a function takes (`OK`), and the instances'
proofs against the contracts it states: encryption (`enc_ok`) and
decryption (`dec_ok`) and decryption with the key's precomputed values
(`decP_ok`), with the label's hash function and MGF1's each any of
`vs`' tables.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.RISCV64

open VG VG.RISCV64
open VG.Proof.MdHashTable.RISCV64 (MVar tables names Coh fns3)

/-- What the registration checks of the hash functions whose tables a
function takes: their functions of the same name have the same code, there
are not too many to give distinct addresses in the witnesses, and there is
one. -/
def OK (vs : List MVar) : Prop := Coh vs ∧ (names vs).length < 2 ^ 32 ∧ vs ≠ []

instance (vs : List MVar) : Decidable (OK vs) := by unfold OK; infer_instance

theorem OK.mem {vs : List MVar} (h : OK vs) : ∃ w, w ∈ vs := List.exists_mem_of_ne_nil _ h.2.2

/-- `vg_rsa_oaep_encrypt_precomputed`, with the tables of `vs`. -/
theorem enc_ok (vs : List MVar) (hok : OK vs) :
    Verified RISCV64.target (Impl.RsaOaep.RISCV64.encrypt (fns3 vs)) (encSpec (tables vs)) :=
  enc_verified hok.1 (let ⟨_, hw⟩ := hok.mem; enc_sat hw hok.2.1)

/-- `vg_rsa_oaep_decrypt`, with the tables of `vs`. -/
theorem dec_ok (vs : List MVar) (hok : OK vs) :
    Verified RISCV64.target (Impl.RsaOaep.RISCV64.Dec.decrypt (fns3 vs)) (Dec.decSpec (tables vs)) :=
  Dec.dec_verified hok.1 (let ⟨_, hw⟩ := hok.mem; Dec.dec_sat hw hok.2.1)

/-- `vg_rsa_oaep_decrypt_precomputed`, with the tables of `vs`. -/
theorem decP_ok (vs : List MVar) (hok : OK vs) :
    Verified RISCV64.target (Impl.RsaOaep.RISCV64.Dec.decryptP (fns3 vs)) (Dec.decPSpec (tables vs)) :=
  ⟨Dec.codeP_correct hok.1, Dec.codeP_constantTime hok.1, let ⟨_, hw⟩ := hok.mem; Dec.decP_sat hw hok.2.1⟩

end VG.Proof.RsaOaep.RISCV64
