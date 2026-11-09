module

public import VerifiedGarbage.Spec.RsaKeyGen.Generation
public import VerifiedGarbage.Spec.Rsa.Contract

/-!
# RSA key generation: the contract of the prime search

Not trusted: the contract of an internal function (`Rust.Internal`), which only
verified code calls, that its proofs and its callers' compose: the prime
search, which `vg_rsa_generate` (`Spec.RsaKeyGen.keySearchContract`) calls for
each prime. Only the callers' contracts, in `Spec/`, are trusted.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen

open VG.Spec VG.Spec.RsaKeyGen
open VG.Spec.Rsa (bytesAt wordsAt i2osp scratchWords)

/-! ## `vg_rsa_prime_search` -/

/-- `vg_rsa_prime_search(out: *mut u8, out_len: usize, used: *mut [u64; 1],
e: *const u8, e_len: usize, p: *const u8, p_len: usize, rand: *const u8,
rand_len: usize, scratch: *mut u64, scratch_len: usize,
state: *mut [u64; 4]) -> u32`. -/
def primeSearchSig : Sig where
  params := [("out", .slice true .u8 "out_len"), ("used", .array true .u64 1),
    ("e", .slice false .u8 "e_len"), ("p", .slice false .u8 "p_len"),
    ("rand", .slice false .u8 "rand_len"), ("scratch", .slice true .u64 "scratch_len"),
    ("state", .array true .u64 4)]
  ret := some .u32

/-- `primeSearch` on `rand`, from the candidates left in `state`: its status
(`Entropy.Outcome.status`), the prime at `out` (zeros otherwise), the octets it
consumed at `used`, and the state for the next call, whose last word is the
next tape's length: any that `Entropy.Result.Requests` allows (0 if there is
none). Its timing may depend on `e`, the state's words, the result's status,
consumption and octets left, and the trace of its candidates. -/
def primeSearchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  primeSearchSig.contract A
    (pre := fun _out outLen _used e eLen _p pLen _rand randLen _scratch scratchLen state m =>
      primeLenValid outLen.toNat ∧ 1 ≤ eLen.toNat ∧ eLen.toNat ≤ 8 ∧
      (pLen.toNat = 0 ∨ pLen.toNat = outLen.toNat) ∧
      scratchWords outLen.toNat ≤ scratchLen.toNat ∧
      (m.readW state 64).toNat ≤ primeLimit (8 * outLen.toNat)
        (Rsa.os2ip (bytesAt m e eLen.toNat)) ∧
      m.readW (state + 8) 64 = BitVec.ofNat 64 outLen.toNat ∧
      m.readW (state + 16) 64 = BitVec.ofNat 64 (primeEntropy outLen.toNat) ∧
      randLen.toNat ≤ primeEntropy outLen.toNat)
    (post := fun out outLen used e eLen p pLen rand randLen _scratch _scratchLen state m m' r =>
      let result := primeSearch outLen.toNat (bytesAt m e eLen.toNat)
        (bytesAt m p pLen.toNat) (m.readW state 64).toNat (bytesAt m rand randLen.toNat)
      r.toNat = result.status ∧
      bytesAt m' out outLen.toNat =
        (match result.outcome with
          | .accepted c => i2osp c outLen.toNat
          | _ => List.replicate outLen.toNat 0) ∧
      wordsAt m' used 1 = [BitVec.ofNat 64 result.used] ∧
      ∃ requested, wordsAt m' state 4 = [BitVec.ofNat 64 result.remaining,
        BitVec.ofNat 64 outLen.toNat, BitVec.ofNat 64 (primeEntropy outLen.toNat),
        BitVec.ofNat 64 requested] ∧
        result.Requests (primeEntropy outLen.toNat) requested)
    (writeArgs := true) (stack := stack)
    (leak := some fun _out outLen _used e eLen p pLen rand randLen _scratch _scratchLen state m =>
      let result := primeSearch outLen.toNat (bytesAt m e eLen.toNat)
        (bytesAt m p pLen.toNat) (m.readW state 64).toNat (bytesAt m rand randLen.toNat)
      (bytesAt m e eLen.toNat).map (·.toNat) ++ (wordsAt m state 4).map (·.toNat) ++
        [result.status, result.used, result.available] ++ result.trace)

end VG.Proof.RsaKeyGen
