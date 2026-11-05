module

public import VerifiedGarbage.Spec.RsaKeyGen.Contract

/-! # `vg_rsa_keygen_candidate`'s contract

One candidate for a prime (`VG.Spec.RsaKeyGen.candidateOp`). Only the
verified prime searches call it (`VG.Spec.RsaKeyGen.primeSearchContract`),
so it is an internal function, with its contract here rather than in
`Spec/`: the searches' proofs rest on it, and nothing else does.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen

open VG VG.Spec.RsaKeyGen
open VG.Spec.Rsa (bytesAt wordsAt os2ip i2osp scratchWords scratchSafety)

/-- `vg_rsa_keygen_candidate(out: *mut u8, out_len: usize, used: *mut [u64; 1],
e: *const u8, e_len: usize, p: *const u8, p_len: usize, rand: *const u8,
rand_len: usize, scratch: *mut u64, scratch_len: usize) -> u32`. -/
def candidateSig : Sig where
  params := [("out", .slice true .u8 "out_len"), ("used", .array true .u64 1),
    ("e", .slice false .u8 "e_len"), ("p", .slice false .u8 "p_len"),
    ("rand", .slice false .u8 "rand_len"), ("scratch", .slice true .u64 "scratch_len")]
  ret := some .u32

/-- One candidate for a prime (`candidateOp`): 1 and the prime at `out` if it
is accepted; 2 if it is too close to `p`; 3 if it is rejected otherwise;
with the number of octets of `rand` read at `used`; or 0 if `rand` is too
short. Zeros at `out` but for a prime, and at `used` for 0. Constant time
but for `e` and `candidateLeak`. -/
def candidateContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  candidateSig.contract A
    (pre := fun _out outLen _used _e eLen _p pLen _rand _randLen _scratch scratchLen _ =>
      primeLenValid outLen.toNat ∧ 1 ≤ eLen.toNat ∧ eLen.toNat ≤ 8 ∧
        (pLen.toNat = 0 ∨ pLen.toNat = outLen.toNat) ∧
        scratchWords outLen.toNat ≤ scratchLen.toNat)
    (post := fun out outLen used e eLen p pLen rand randLen _scratch _scratchLen m m' r =>
      let res := candidateOp outLen.toNat (bytesAt m e eLen.toNat) (bytesAt m p pLen.toNat)
        (bytesAt m rand randLen.toNat)
      r.toNat = candidateStatus res ∧
        bytesAt m' out outLen.toNat =
          (match res with
            | some (.prime c, _) => i2osp c outLen.toNat
            | _ => List.replicate outLen.toNat 0) ∧
        wordsAt m' used 1 =
          [BitVec.ofNat 64 (match res with
            | some (_, rest) => randLen.toNat - rest.length
            | none => 0)])
    (writeArgs := true) (stack := stack)
    (leak := some fun _out outLen _used e eLen p pLen rand randLen _scratch _scratchLen m =>
      (bytesAt m e eLen.toNat).map (·.toNat) ++
        candidateLeak outLen.toNat (bytesAt m e eLen.toNat) (bytesAt m p pLen.toNat)
          (bytesAt m rand randLen.toNat))

end VG.Proof.RsaKeyGen
