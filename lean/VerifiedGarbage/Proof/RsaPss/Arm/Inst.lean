module

public import VerifiedGarbage.Proof.RsaPss.Arm.SgVerified
public import VerifiedGarbage.Proof.RsaPss.Arm.SgSat
public import VerifiedGarbage.Proof.RsaPss.Arm.VfVerified
public import VerifiedGarbage.Proof.RsaPss.Arm.VfSat

/-!
# RSASSA-PSS on ARMv7: the instances emitted

What the registrations check of the hash functions whose tables a function
takes (`OK`), and the instances' proofs against the contracts the
registrations state, with the hash function any of the tables of `MdHash`
and MGF1's any of the tables of `Hash`: signing (`sign_ok`) and
verification (`verify_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.Arm

open VG VG.Arm
open VG.Proof.HashTable.Arm (TVar)
open VG.Proof.MdHashTable.Arm (MVar)

/-- What the registrations check of the hash functions whose tables a
function takes: their functions of the same name have the same code, there
are not too many to give distinct addresses in the witnesses, and there is
one of each kind. -/
def OK (mvs : List MVar) (vs : List TVar) : Prop :=
  MdHashTable.Arm.Coh mvs ∧ HashTable.Arm.Coh vs ∧ (allNames mvs vs).length < 2 ^ 24 ∧ mvs ≠ [] ∧ vs ≠ []

instance (mvs : List MVar) (vs : List TVar) : Decidable (OK mvs vs) := by unfold OK; infer_instance

/-- `vg_rsa_pss_sign`, with the tables of `mvs` and `vs` and the private-key
operation over `v`. -/
theorem sign_ok {mvs : List MVar} {vs : List TVar} (hok : OK mvs vs) (v : Proof.Rsa.Arm.CrtImpl) :
    Verified target (Sg.signCode mvs vs v) (Sg.sspec mvs vs) :=
  Sg.sign_verified hok.1 hok.2.1 (let ⟨_, hw⟩ := List.exists_mem_of_ne_nil _ hok.2.2.2.1
    let ⟨_, hwg⟩ := List.exists_mem_of_ne_nil _ hok.2.2.2.2; Sg.sign_sat hw hwg hok.2.2.1) v

/-- `vg_rsa_pss_verify_precomputed`, with the tables of `mvs` and `vs`,
calling `c`. -/
theorem verify_ok {mvs : List MVar} {vs : List TVar} (hok : OK mvs vs) (c : RsaPkcs1Sig.Arm.PdImpl) :
    Verified target (Vf.verifyCode mvs vs c) (Vf.vspec mvs vs) :=
  Vf.verify_verified hok.1 hok.2.1 (let ⟨_, hw⟩ := List.exists_mem_of_ne_nil _ hok.2.2.2.1
    let ⟨_, hwg⟩ := List.exists_mem_of_ne_nil _ hok.2.2.2.2; Vf.verify_sat hw hwg hok.2.2.1) c

end VG.Proof.RsaPss.Arm
