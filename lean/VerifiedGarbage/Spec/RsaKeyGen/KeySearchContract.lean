module

public import VerifiedGarbage.Spec.RsaKeyGen.KeySearch
public import VerifiedGarbage.Spec.Rsa.Contract

/-!
# Contracts of RSA key generation over refillable random tapes

**Trusted.** `vg_rsa_generate_init` checks the size and the exponent
(`keySearchInit`) and writes the search's state; `vg_rsa_generate` runs
`keySearch` on each tape. The state is seven public words: the four of the
prime search being run (`primeSearchContract`: its rejected candidates left,
the primes' octets `pLen`, its budget of entropy and the next tape's
length), then the phase (0 for `p`, 1 for `q`), the generations left, and
the exponent as 8 octets, most significant first, in that word's memory.

The key is written to one buffer of `9 pLen` octets (`keyBytes`): `n` and
`d` of `2 pLen`, then `p`, `q`, `dP`, `dQ` and `qInv` of `pLen`. While the
search asks for more entropy in the phase of `q`, the octets of `p` are the
buffer's `p` (at `4 pLen`), the rest zeros: the next call reads `p` from
there, so the host passes the buffer back unchanged. Otherwise it is zeros,
but for a key.
-/

@[expose] public section

namespace VG.Spec.RsaKeyGen

open VG.Spec.Rsa (bytesAt wordsAt os2ip i2osp scratchWords)

/-! ## `vg_rsa_generate_init` -/

/-- `vg_rsa_generate_init(state: *mut [u64; 7], bits: usize, e: *const u8,
e_len: usize) -> u32`. -/
def keyInitSig : Sig where
  params := [("state", .array true .u64 7), ("bits", .int .usize true),
    ("e", .slice false .u8 "e_len")]
  ret := some .u32

/-- `keySearchInit`: 1, its three words, the first tape's length (any that
`Entropy.RequestValid` allows with no octets available), the phase of `p`,
`keyGenerations`, and the exponent's word; or its error and seven zeros. Its
timing may depend on `bits` and `e`, which are public. -/
def keyInitContract {M : ISA} (A : Abi M) : Contract M :=
  keyInitSig.contract A
    (post := fun state bits e eLen m m' r =>
      let eB := bytesAt m e eLen.toNat
      match keySearchInit bits.toNat eB with
      | .error c => r.toNat = c ∧ wordsAt m' state 7 = List.replicate 7 0
      | .ok values => r.toNat = 1 ∧ ∃ first,
        wordsAt m' state 6 = (values ++ [first, 0, keyGenerations]).map (BitVec.ofNat 64) ∧
        bytesAt m' (state + 48) 8 = i2osp (os2ip eB) 8 ∧
        Entropy.RequestValid (primeEntropy (values.getD 1 0)) 0 first)
    (leak := some fun _state bits e eLen m =>
      bits.toNat :: (bytesAt m e eLen.toNat).map (·.toNat))

def keyInitApi : Api where
  module := "rsa_keygen"
  name := "vg_rsa_generate_init"
  sig := keyInitSig
  contracts := some fun A _ => keyInitContract A
  summary := "Start generating an RSA key, as BoringSSL's `RSA_generate_key_ex` (FIPS \
    186-5 Appendix A.1.3), with a modulus of `bits` bits rounded down to a multiple of \
    128, and the public exponent `e` (`e_len` octets, most significant first, with any \
    number of leading zeros). Returns 0 if `e` is not odd from 3 to `2^32 - 1`, or 2 if \
    `bits` is above 8192 or, rounded down, below 512, and writes zeros to `state`. \
    Otherwise returns 1 and writes the search's seven public words to `state`: the \
    rejected candidates the first prime's search allows, the primes' length in octets \
    (`nlen / 16`), the entropy budget, the length of the first random tape to give \
    `vg_rsa_generate`, the phase (0), the generations allowed (4), and the exponent's \
    eight octets, most significant first.\n\n\
    Contract: `VG.Spec.RsaKeyGen.keyInitContract`. Timing may depend on `bits` and `e`."
  safety := []

/-! ## `vg_rsa_generate` -/

/-- `vg_rsa_generate(key: *mut u8, key_len: usize, used: *mut [u64; 1],
rand: *const u8, rand_len: usize, scratch: *mut u64, scratch_len: usize,
state: *mut [u64; 7]) -> u32`. -/
def keySearchSig : Sig where
  params := [("key", .slice true .u8 "key_len"), ("used", .array true .u64 1),
    ("rand", .slice false .u8 "rand_len"), ("scratch", .slice true .u64 "scratch_len"),
    ("state", .array true .u64 7)]
  ret := some .u32

/-- The state a call of `vg_rsa_generate` starts from: its words, and, in the
phase of `q`, the octets of `p` in the key's buffer. -/
def keyProgressAt (m : Mem) (key state : Addr) (pLen : Nat) : KeyProgress :=
  ⟨(m.readW (state + 40) 64).toNat,
    if (m.readW (state + 32) 64).toNat = 0 then .p
    else .q (bytesAt m (key + BitVec.ofNat 64 (4 * pLen)) pLen),
    (m.readW state 64).toNat⟩

/-- The key's buffer after a key search: the key; in the phase of `q`, when it
asks for more entropy, the octets of `p` where the key's `p` goes, after `4
pLen` zeros and before `4 pLen` zeros; otherwise zeros. -/
def keySearchBytes (pLen : Nat) (r : KeySearchResult) : List Byte :=
  match r.outcome with
  | .accepted (.ok k) => keyBytes pLen k
  | .entropy ⟨_, .q pB, _⟩ _ =>
    List.replicate (4 * pLen) 0 ++ pB ++ List.replicate (4 * pLen) 0
  | _ => List.replicate (9 * pLen) 0

/-- `keySearch` on `rand`, for the primes' length in `state[1]` and the
exponent in `state[6]`, from the state in `state` and the key's buffer: its
status (`KeySearchResult.keyStatus`), the key's buffer (`keySearchBytes`), the
octets it consumed at `used`, and the state for the next call, whose fourth
word is the next tape's length: any that `Entropy.Result.Requests` allows
(0 if there is none); the exponent is kept. Its timing may depend on the
state's words, the result's status, consumption and octets left, and its
trace: each prime search's (`primeSearchContract`) and each key's status
(`keyContract`). -/
def keySearchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  keySearchSig.contract A
    (pre := fun _key keyLen _used _rand randLen _scratch scratchLen state m =>
      let pLen := (m.readW (state + 8) 64).toNat
      let eB := bytesAt m (state + 48) 8
      primeLenValid pLen ∧ keyLen.toNat = 9 * pLen ∧
      scratchWords (2 * pLen) ≤ scratchLen.toNat ∧
      (m.readW state 64).toNat ≤ primeLimit (8 * pLen) (os2ip eB) ∧
      m.readW (state + 16) 64 = BitVec.ofNat 64 (primeEntropy pLen) ∧
      (m.readW (state + 32) 64).toNat ≤ 1 ∧
      randLen.toNat ≤ primeEntropy pLen)
    (post := fun key _keyLen used rand randLen _scratch _scratchLen state m m' r =>
      let pLen := (m.readW (state + 8) 64).toNat
      let eB := bytesAt m (state + 48) 8
      let result := keySearch pLen eB (keyProgressAt m key state pLen)
        (bytesAt m rand randLen.toNat)
      let s := result.progress
      r.toNat = result.keyStatus ∧
      bytesAt m' key (9 * pLen) = keySearchBytes pLen result ∧
      wordsAt m' used 1 = [BitVec.ofNat 64 result.used] ∧
      ∃ requested, wordsAt m' state 6 = [BitVec.ofNat 64 s.remaining,
        BitVec.ofNat 64 pLen, BitVec.ofNat 64 (primeEntropy pLen), BitVec.ofNat 64 requested,
        BitVec.ofNat 64 (if s.phase = .p then 0 else 1), BitVec.ofNat 64 s.left] ∧
        bytesAt m' (state + 48) 8 = eB ∧
        result.Requests (primeEntropy pLen) requested)
    (writeArgs := true) (stack := stack)
    (leak := some fun key _keyLen _used rand randLen _scratch _scratchLen state m =>
      let pLen := (m.readW (state + 8) 64).toNat
      let result := keySearch pLen (bytesAt m (state + 48) 8) (keyProgressAt m key state pLen)
        (bytesAt m rand randLen.toNat)
      (wordsAt m state 7).map (·.toNat) ++
        [result.keyStatus, result.used, result.available] ++ result.trace)

def keySearchApi : Api where
  module := "rsa_keygen"
  name := "vg_rsa_generate"
  sig := keySearchSig
  writeArgs := true
  contracts := some fun A stack => keySearchContract A stack
  summary := "Generate an RSA key, as BoringSSL's `RSA_generate_key_ex` (FIPS 186-5 \
    Appendix A.1.3), over the random tape `rand`, from the state `state` that \
    `vg_rsa_generate_init` started: the search for `p`, then for `q` not too close to \
    `p`, each that of `vg_rsa_prime_search`; then the key, that of `vg_rsa_keygen_key`, \
    drawing both primes again if `d` is too small; a generation whose prime's search is \
    exhausted is started again, up to four in all. Returns 1 and writes the key to `key` \
    (`key_len` is `9 p_len`, for the primes' length `p_len = state[1]`): `n` and `d` \
    (`2 p_len` octets each), then `p`, `q`, `dP`, `dQ` and `qInv` (`p_len` each), all most \
    significant first; 2 if the key failed a check; 3 if every generation was exhausted; \
    or 0 if the tape ran out inside a candidate. Writes the octets of `rand` it consumed \
    to `used`, and the state for the next call to `state`, whose fourth word is, for 0, \
    the length of the next tape, more than the octets of `rand` after the first `used` \
    and at most the entropy budget: keep those octets, in order, and append fresh random \
    octets up to that length. For 0, `key` holds the search's `p` once it is found, which \
    the next call reads: pass it back unchanged. `key` is otherwise zeros but for 1.\n\n\
    Contract: `VG.Spec.RsaKeyGen.keySearchContract`. Timing may depend on the pointers, \
    the lengths, `state`, the status and consumption it returns, and on what \
    `vg_rsa_prime_search`'s timing may depend on for each prime and \
    `vg_rsa_keygen_key`'s for each key. Not on the primes or the key."
  safety := ["`state` must come from `vg_rsa_generate_init`, or from the last call of \
      this function, with the same `key`, that returned 0.",
    "`key_len` must be `9 * state[1]`.",
    "`rand_len` must be at most the entropy budget, `state[2]`.",
    "`scratch_len` must be at least `32 * state[1] + 32`.",
    "The contents of `scratch` on return are unspecified and may contain secrets, and \
      `rand` and `key` hold secrets; the caller must destroy them after use."]

end VG.Spec.RsaKeyGen
