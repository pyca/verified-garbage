module

public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.Spec.Ffdh.SievedGeneration

/-!
# Finite-field Diffie–Hellman: the contracts of its internal functions

Not trusted: the contracts of internal functions (`Rust.Internal`), which only
verified code calls, that their proofs and their callers' compose. Only the
callers' contracts, in `Spec/`, are trusted.

* `vg_ffdh_parameter_candidate`: one element of `generateParameters`' list,
  with its Miller–Rabin witnesses, from random octets
  (`parameterCandidate`), for the parameter search;
* `vg_ffdh_parameter_candidate_sieved`: the same with RSA's trial-division
  sieve (`sievedParameterCandidate`);
* `vg_ffdh_choose`: a word selected by a secret bit.

Their arguments are as in `Spec/Ffdh/Contract.lean`.
-/

@[expose] public section

namespace VG.Proof.Ffdh

open VG.Spec VG.Spec.Ffdh
open VG.Spec.Rsa (bytesAt wordsAt i2osp scratchWords)
open VG.Spec.RsaKeyGen (Rand)

/-- The status `vg_ffdh_parameter_candidate` returns: 0 if `rand` ran out,
1 for an accepted p, 2 for a rejected candidate. -/
def candidateStatus : Option (Option Nat × Rand) → Nat
  | none => 0
  | some (some _, _) => 1
  | some (none, _) => 2

/-- `vg_ffdh_parameter_candidate(out: *mut u8, out_len: usize, used: *mut [u64; 1],
bits: usize, generator: u32, rand: *const u8, rand_len: usize, scratch: *mut u64,
scratch_len: usize) -> u32`. -/
def parameterCandidateSig : Sig where
  params := [("out", .slice true .u8 "out_len"), ("used", .array true .u64 1),
    ("bits", .int .usize true), ("generator", .int .u32 true),
    ("rand", .slice false .u8 "rand_len"), ("scratch", .slice true .u64 "scratch_len")]
  ret := some .u32

/-- One candidate for p (`parameterCandidate`): `candidateStatus`, p at `out`
for 1 (zeros otherwise), and the number of octets of `rand` read at `used`
(0 for status 0). Everything is public: timing may depend on `rand`. -/
def parameterCandidateContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  parameterCandidateSig.contract A
    (pre := fun _out outLen _used bits generator _rand _randLen _scratch scratchLen _ =>
      512 ≤ bits.toNat ∧ bits.toNat ≤ 8192 ∧ outLen.toNat = (bits.toNat + 7) / 8 ∧
        (generator.toNat = 2 ∨ generator.toNat = 5) ∧
        scratchWords outLen.toNat ≤ scratchLen.toNat)
    (post := fun out outLen used bits generator rand randLen _scratch _scratchLen m m' r =>
      let res := parameterCandidate bits.toNat generator.toNat (bytesAt m rand randLen.toNat)
      r.toNat = candidateStatus res ∧
        bytesAt m' out outLen.toNat =
          (match res with
            | some (some p, _) => i2osp p outLen.toNat
            | _ => List.replicate outLen.toNat 0) ∧
        wordsAt m' used 1 =
          [BitVec.ofNat 64 (match res with
            | some (_, rest) => randLen.toNat - rest.length
            | none => 0)])
    (writeArgs := true) (stack := stack)
    (leak := some fun _out _outLen _used _bits _generator rand randLen _scratch _scratchLen m =>
      (bytesAt m rand randLen.toNat).map (·.toNat))

def sievedParameterCandidateContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  parameterCandidateSig.contract A
    (pre := fun _out outLen _used bits generator _rand _randLen _scratch scratchLen _ =>
      512 ≤ bits.toNat ∧ bits.toNat ≤ 8192 ∧ outLen.toNat = (bits.toNat + 7) / 8 ∧
        (generator.toNat = 2 ∨ generator.toNat = 5) ∧
        scratchWords outLen.toNat ≤ scratchLen.toNat)
    (post := fun out outLen used bits generator rand randLen _scratch _scratchLen m m' r =>
      let res := sievedParameterCandidate bits.toNat generator.toNat (bytesAt m rand randLen.toNat)
      r.toNat = candidateStatus res ∧
        bytesAt m' out outLen.toNat =
          (match res with
            | some (some p, _) => i2osp p outLen.toNat
            | _ => List.replicate outLen.toNat 0) ∧
        wordsAt m' used 1 =
          [BitVec.ofNat 64 (match res with
            | some (_, rest) => randLen.toNat - rest.length
            | none => 0)])
    (writeArgs := true) (stack := stack)
    (leak := some fun _out _outLen _used _bits _generator rand randLen _scratch _scratchLen m =>
      (bytesAt m rand randLen.toNat).map (·.toNat))

def chooseSig : Sig where
  params := [("a", .int .u64 false), ("b", .int .u64 false), ("bit", .int .u64 false)]
  ret := some .u64

def chooseContract {I : ISA} (A : Abi I) (stack : Nat := 0) : Contract I :=
  chooseSig.contract A (post := fun a b bit m m' r => r = choose a b bit ∧ m' = m) (stack := stack)

end VG.Proof.Ffdh
