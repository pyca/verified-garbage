module

public import VerifiedGarbage.Proof.Rsa.Contract

/-!
# `vg_rsa_private_crt_precomputed`: the contract of the internal function

Not trusted (`Proof/Rsa/Contract.lean`): `vg_rsa_private_crt`'s operation,
given also the factors' `R² mod p` and `R² mod q` (`Spec.Rsa.primeR2`), as
`vg_rsa_private_precompute` writes them after the modulus' values, and so
for a key whose factors' product is the modulus, which those values imply
(`Spec.Rsa.privatePrecompute`). Only `vg_rsa_private_checked_precomputed`
calls it, with the precomputed values of its key.
-/

@[expose] public section

namespace VG.Proof.Rsa

open VG.Spec.Rsa

/-- `vg_rsa_private_crt`'s arguments, then `r2: *const u64, r2_len: usize`. -/
def privateCrtPrecomputedSig : Sig where
  params := privateCrtSig.params ++ [("r2", .slice false .u64 "r2_len")]
  ret := some .u32

/-- `privateCrtContract`, given `R² mod p` and `R² mod q` (`primeR2`) in
`r2`, for factors whose product is the modulus. Constant time but for `n`. -/
def privateCrtPrecomputedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  privateCrtPrecomputedSig.contract A
    (pre := fun _out outLen n nLen _input inputLen p pLen q qLen _dp dpLen _dq dqLen _qinv
        qinvLen _scratch scratchLen r2 r2Len m =>
      lenValid nLen.toNat ∧ outLen.toNat = nLen.toNat ∧ inputLen.toNat = nLen.toNat ∧
        1 ≤ pLen.toNat ∧ pLen.toNat < nLen.toNat ∧ 1 ≤ qLen.toNat ∧ qLen.toNat < nLen.toNat ∧
        dpLen.toNat = pLen.toNat ∧ qinvLen.toNat = pLen.toNat ∧ dqLen.toNat = qLen.toNat ∧
        scratchWords nLen.toNat ≤ scratchLen.toNat ∧
        r2Len.toNat = primeWords pLen.toNat + primeWords qLen.toNat ∧
        wordsAt m r2 r2Len.toNat = primeR2 (bytesAt m p pLen.toNat) ++ primeR2 (bytesAt m q qLen.toNat) ∧
        os2ip (bytesAt m p pLen.toNat) * os2ip (bytesAt m q qLen.toNat) = os2ip (bytesAt m n nLen.toNat))
    (post := fun out _outLen n nLen input _inputLen p pLen q qLen dp _dpLen dq _dqLen qinv
        _qinvLen _scratch _scratchLen _r2 _r2Len m m' r =>
      written m' out nLen.toNat r
        (privateCrt (bytesAt m n nLen.toNat) (bytesAt m input nLen.toNat)
          (bytesAt m p pLen.toNat) (bytesAt m q qLen.toNat) (bytesAt m dp pLen.toNat)
          (bytesAt m dq qLen.toNat) (bytesAt m qinv pLen.toNat)))
    (writeArgs := true) (stack := stack)
    (leak := some fun _out _outLen n nLen _input _inputLen _p _pLen _q _qLen _dp _dpLen _dq
        _dqLen _qinv _qinvLen _scratch _scratchLen _r2 _r2Len m =>
      (bytesAt m n nLen.toNat).map (·.toNat))

end VG.Proof.Rsa
