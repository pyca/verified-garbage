module

public import VerifiedGarbage.Spec.RsaKeyGen.Generation
public import VerifiedGarbage.Spec.Rsa.Contract

/-! # Contracts of the RSA prime search over refillable random tapes -/

@[expose] public section

namespace VG.Spec.RsaKeyGen

open VG.Spec.Rsa (bytesAt wordsAt i2osp scratchWords)

/-! ## `vg_rsa_prime_search_init` -/

/-- `vg_rsa_prime_search_init(state: *mut [u64; 4], prime_len: usize,
e: *const u8, e_len: usize) -> u32`. -/
def primeInitSig : Sig where
  params := [("state", .array true .u64 4), ("prime_len", .int .usize true),
    ("e", .slice false .u8 "e_len")]
  ret := some .u32

/-- `primeInit`: 1, its three words and the first tape's length, any that
`Entropy.RequestValid` allows with no octets available, or 0 and four zeros.
Its timing may depend on `e`, which is public. -/
def primeInitContract {M : ISA} (A : Abi M) : Contract M :=
  primeInitSig.contract A
    (post := fun state primeLen e eLen m m' r =>
      match primeInit primeLen.toNat (bytesAt m e eLen.toNat) with
      | none => r.toNat = 0 ∧ wordsAt m' state 4 = List.replicate 4 0
      | some values => r.toNat = 1 ∧ ∃ first,
        wordsAt m' state 4 = (values ++ [first]).map (BitVec.ofNat 64) ∧
        Entropy.RequestValid (primeEntropy primeLen.toNat) 0 first)
    (leak := some fun _state _primeLen e eLen m =>
      (bytesAt m e eLen.toNat).map (·.toNat))

def primeInitApi : Api where
  module := "rsa_keygen"
  name := "vg_rsa_prime_search_init"
  sig := primeInitSig
  contracts := some fun A _ => primeInitContract A
  summary := "Start a search for a prime of an RSA key, of `prime_len` octets, for the \
    public exponent `e` (`e_len` octets, most significant first). Returns 1 and writes \
    the search's four public words to `state`: the rejected candidates it still allows, \
    `prime_len`, its entropy budget, and the length of the first random tape to give \
    `vg_rsa_prime_search`. Returns 0 and writes zeros if `prime_len` is not a multiple \
    of 8 in 32..=512 or `e_len` is not in 1..=8.\n\n\
    Contract: `VG.Spec.RsaKeyGen.primeInitContract`. Timing may depend on `e`."
  safety := []

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

def primeSearchApi : Api where
  module := "rsa_keygen"
  name := "vg_rsa_prime_search"
  sig := primeSearchSig
  writeArgs := true
  contracts := some fun A stack => primeSearchContract A stack
  summary := "Search for a prime of an RSA key, of `out_len` octets, for the public \
    exponent `e`, not too close to the prime `p` if `p_len` is not 0, over the random \
    tape `rand`: the candidates and their tests of `vg_rsa_keygen_candidate`, one after \
    another, with the rejected candidates counted in `state` (those too close to `p` are \
    not). Returns 1 and writes the prime to `out` once one is accepted; 3 if the search \
    is exhausted, by too many rejected candidates or by one candidate needing more than \
    the entropy budget; or 0 if the tape ran out inside a candidate. Writes the octets of \
    `rand` it consumed to `used`, and the state for the next call to `state`, whose last \
    word is, for 0, the length of the next tape, more than the octets of `rand` after \
    the first `used` and at most the entropy budget: keep those octets, in order, and \
    append fresh random octets up to that length. `out` is \
    zeros but for 1.\n\n\
    Contract: `VG.Spec.RsaKeyGen.primeSearchContract`. Timing may depend on the \
    pointers, the lengths, `e`, `state`, the status and consumption it returns, \
    and on what `vg_rsa_keygen_candidate`'s timing may depend on for each candidate. \
    Not on `p`, or on the prime it accepts."
  safety := ["`state` must come from `vg_rsa_prime_search_init` for `out_len` and `e`, \
      or from the last call of this function for the same `out_len`, `e` and `p` that \
      returned 0.",
    "`out_len` must be a multiple of 8 in 32..=512.", "`e_len` must be in 1..=8.",
    "`p_len` must be 0 or `out_len`.",
    "`rand_len` must be at most the entropy budget, `state[2]`.",
    "`scratch_len` must be at least `16 * out_len + 32`.",
    "The contents of `scratch` on return are unspecified and may contain secrets, and \
      `rand` holds secrets; the caller must destroy both after use."]

end VG.Spec.RsaKeyGen
