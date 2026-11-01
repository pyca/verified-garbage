module

public import VerifiedGarbage.Spec.Dsa.Derive

/-!
# DSA: the contract of its domain checks

Not trusted: the contract of an internal function (`Rust.Internal`), which only
verified code calls, that its proofs and its callers' compose. Only the
callers' contracts, in `Spec/`, are trusted.

* `vg_dsa_check_parameters` (and `vg_dsa_generation_check_parameters`, the
  same contract) accepts exactly the supported widths and domains that
  `generateKeyBytes` accepts (`checkParametersBytes`), for key generation
  to call before it samples x. All its inputs are public.
-/

@[expose] public section

namespace VG.Proof.Dsa

open VG.Spec VG.Spec.Dsa
open VG.Spec.Rsa (bytesAt)

def checkParametersSig : Sig where
  params := [("params", .slice false .u8 "params_len"), ("p_len", .int .usize true),
    ("q_len", .int .usize true), ("scratch", .slice true .u64 "scratch_len")]
  ret := some .u32

def checkParametersContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  checkParametersSig.contract A
    (pre := fun _params paramsLen pLen qLen _scratch scratchLen _ =>
      lengthsValid pLen.toNat qLen.toNat ∧ paramsLen.toNat = 2 * pLen.toNat + qLen.toNat ∧
        scratchWords pLen.toNat ≤ scratchLen.toNat)
    (post := fun params paramsLen pLen qLen _scratch _scratchLen m _m' r =>
      r.toNat = if checkParametersBytes pLen.toNat qLen.toNat (bytesAt m params paramsLen.toNat)
        then 1 else 0)
    (writeArgs := true) (stack := stack)
    (leak := some fun params paramsLen _pLen _qLen _scratch _scratchLen m =>
      (bytesAt m params paramsLen.toNat).map (·.toNat))

end VG.Proof.Dsa
