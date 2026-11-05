module

public import VerifiedGarbage.Spec.Dsa.ParameterSearch

/-! # Contracts of DSA parameter generation over refillable random tapes -/

@[expose] public section

namespace VG.Spec.Dsa

open VG.Spec.Rsa (bytesAt wordsAt)

/-! ## `vg_dsa_parameter_search_init` -/

/-- `vg_dsa_parameter_search_init(state: *mut [u64; 4], p_len: usize) -> u32`. -/
def parameterInitSig : Sig where
  params := [("state", .array true .u64 4), ("p_len", .int .usize true)]
  ret := some .u32

/-- `parameterInit`: 1 and its four words, or 0 and four zeros. -/
def parameterInitContract {M : ISA} (A : Abi M) : Contract M :=
  parameterInitSig.contract A
    (post := fun state pLen _m m' r =>
      match parameterInit pLen.toNat with
      | none => r.toNat = 0 ∧ wordsAt m' state 4 = List.replicate 4 0
      | some values => r.toNat = 1 ∧ wordsAt m' state 4 = values.map (BitVec.ofNat 64))
    (leak := some fun _state _pLen _m => [])

def parameterInitApi : Api where
  module := "dsa"
  name := "vg_dsa_parameter_search_init"
  sig := parameterInitSig
  contracts := some fun A _ => parameterInitContract A
  summary := "Start a search for DSA domain parameters with a modulus of `p_len` octets \
    (128, 256 or 384: 1024, 2048 or 3072 bits, with a subgroup of 160, 256 and 256 \
    bits). Returns 1 and writes the search's four public words to `state`: the seeds \
    it may still reject, `p_len`, its entropy budget, and the length of the first \
    random tape to give `vg_dsa_parameter_search`. Returns 0 and writes zeros for any \
    other `p_len`.\n\n\
    Contract: `VG.Spec.Dsa.parameterInitContract`."
  safety := []

/-! ## `vg_dsa_parameter_search` -/

/-- `vg_dsa_parameter_search(out: *mut u8, out_len: usize, used: *mut [u64; 1],
rand: *const u8, rand_len: usize, scratch: *mut u64, scratch_len: usize,
state: *mut [u64; 4]) -> u32`. -/
def parameterSearchSig : Sig where
  params := [("out", .slice true .u8 "out_len"), ("used", .array true .u64 1),
    ("rand", .slice false .u8 "rand_len"), ("scratch", .slice true .u64 "scratch_len"),
    ("state", .array true .u64 4)]
  ret := some .u32

/-- `parameterSearch` on `rand`, from the seeds left in `state`, for the
modulus width in `state[1]`: its status (`Entropy.Outcome.status`), the
parameters `p || q || g` at `out` (zeros otherwise), the octets it consumed at
`used`, and the state for the next call, whose last word is the next tape's
length (0 if there is none). Everything here is public: its timing may depend
on all of it, the tape included. -/
def parameterSearchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  parameterSearchSig.contract A
    (pre := fun _out outLen _used _rand randLen _scratch scratchLen state m =>
      let pLen := (m.readW (state + 8) 64).toNat
      generationPLenValid pLen ∧
      outLen.toNat = 2 * pLen + generationQLen pLen ∧
      generationScratchWords pLen ≤ scratchLen.toNat ∧
      (m.readW state 64).toNat ≤ parameterSeeds ∧
      m.readW (state + 16) 64 = BitVec.ofNat 64 (parameterEntropy pLen) ∧
      randLen.toNat ≤ parameterEntropy pLen)
    (post := fun out outLen used rand randLen _scratch _scratchLen state m m' r =>
      let pLen := (m.readW (state + 8) 64).toNat
      let result := parameterSearch pLen (m.readW state 64).toNat (bytesAt m rand randLen.toNat)
      r.toNat = result.status ∧
      bytesAt m' out outLen.toNat =
        (match result.outcome with
          | .accepted a => encodeParams pLen (generationQLen pLen) a
          | _ => List.replicate outLen.toNat 0) ∧
      wordsAt m' used 1 = [BitVec.ofNat 64 result.used] ∧
      wordsAt m' state 4 = [BitVec.ofNat 64 result.remaining, BitVec.ofNat 64 pLen,
        BitVec.ofNat 64 (parameterEntropy pLen), BitVec.ofNat 64 result.requested])
    (writeArgs := true) (stack := stack)
    (leak := some fun _out _outLen _used rand randLen _scratch _scratchLen state m =>
      (wordsAt m state 4).map (·.toNat) ++ (bytesAt m rand randLen.toNat).map (·.toNat))

def parameterSearchApi : Api where
  module := "dsa"
  name := "vg_dsa_parameter_search"
  sig := parameterSearchSig
  writeArgs := true
  contracts := some fun A stack => parameterSearchContract A stack
  summary := "Search for DSA domain parameters (FIPS 186-4 A.1.1.2 and A.2.1) over the \
    random tape `rand`, for the modulus width in `state`: each seed, its `q`, the `p` \
    candidates from it and the generator's `h` candidates are read from `rand` in turn, \
    with the rejected seeds counted in `state`. Returns 1 and writes `p || q || g` to \
    `out` once parameters are found; 3 if the search is exhausted, by too many rejected \
    seeds or by one seed needing more than the entropy budget; or 0 if the tape ran out \
    inside a seed. Writes the octets of `rand` it consumed to `used`, and the state for \
    the next call to `state`, whose last word is, for 0, the length of the next tape: \
    keep the octets of `rand` after the first `used`, in order, and append fresh random \
    octets up to that length. `out` is zeros but for 1. Accepted parameters pass \
    probable-prime tests, not primality certification.\n\n\
    Contract: `VG.Spec.Dsa.parameterSearchContract`. Timing may depend on everything, \
    `rand` included: these are public domain parameters."
  safety := ["`state` must come from `vg_dsa_parameter_search_init`, or from the last \
      call of this function that returned 0.",
    "`out_len` must be `2 * state[1]` plus 20 if `state[1]` is 128, else plus 32.",
    "`rand_len` must be at most the entropy budget, `state[2]`.",
    "`scratch_len` must be at least `64 * state[1] + 1024` words.",
    "`rand` must hold independent uniform random octets. They are public under this \
      contract and must never be used for private scalars or nonces."]

end VG.Spec.Dsa
