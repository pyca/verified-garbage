import VerifiedGarbage.Spec.RsaKeyGen
import VerifiedGarbage.Spec.Rsa.Contract

/-!
# RSA key generation: the contracts, on every target

**Trusted** (as every file in `Spec/`). In the module `rsa_keygen`, the two
parts of `RsaKeyGen.generate` that compute with secrets; the Rust that calls
them runs the loops, counts the tries, supplies the randomness and runs the
pairwise consistency test with `vg_rsa_private_crt` and `vg_rsa_public`:

* `vg_rsa_keygen_candidate`: one candidate for a prime
  (`RsaKeyGen.candidateStep`), from the random octets given;
* `vg_rsa_keygen_key`: the key from its two primes
  (`RsaKeyGen.keyFromPrimes`).

Every number is a slice of octets, most significant first, with a length of
its own. A prime is `p_len` octets (`out_len` for a candidate), a multiple of
8 from 32 to 512 (primes of 256 to 4096 bits), and so are `dP`, `dQ` and
`qInv`; `n` and `d` are `2 p_len` octets; `e` is 1 to 8 octets. These are
preconditions, on the public lengths; everything about the values is
checked.

The randomness is a slice `rand`, read from the front as
`RsaKeyGen.generate` reads its randomness. A candidate may need more octets
than `rand` has (a probable prime needs at least 16 Miller–Rabin witnesses
and may need more); the function then says so, and the caller calls it
again with `rand` extended by more random octets, which gives the result for
the longer `rand`.

What timing may depend on (`leak`) is what BoringSSL lets it depend on.
Everything about a rejected candidate may leak (its octets, and the
witnesses read for it), but for a candidate rejected for being too close to
`p`, only that: the candidate is then not independent of `p`. Of a candidate
accepted as a probable prime, only how many octets of `rand` were read (the
number of Miller–Rabin witnesses BoringSSL's blinding needed, which it
declassifies); of `vg_rsa_keygen_key`, only whether the primes gave a key,
`d` was too small (so both primes are generated again), or a check failed.
The public exponent is public; the primes, the private key and the octets of
`rand` are secret.

`scratch` is working space of at least `16 n_len` `u64`s (`16 out_len` for
a candidate), whose contents on return are unspecified. `stack` is the
number of bytes below the stack pointer that an implementation's calls and
frames use. The functions may overwrite their arguments passed in memory,
where the calling convention allows it (`writeArgs`).
-/

namespace VG.Spec.RsaKeyGen

open VG.Spec.Rsa (bytesAt wordsAt os2ip i2osp scratchWords scratchSafety)

/-- The bounds on a prime's length, in octets: a multiple of 8 (whole 64-bit
words) from 32 to 512, which `generate` makes `nlen / 16` for its modulus of
`nlen` bits from 512 to 8192, a multiple of 128. -/
def primeLenValid (pLen : Nat) : Prop := 32 ≤ pLen ∧ pLen ≤ 512 ∧ pLen % 8 = 0

/-- The other prime a candidate must not be too close to: none for no
octets. -/
def otherPrime (pB : List Byte) : Option Nat := if pB = [] then none else some (os2ip pB)

/-- `candidateStep` for a prime of `pLen` octets and the public exponent `eB`,
not too close to the prime `pB` (none if empty), from the random octets
`rand`. -/
def candidateOp (pLen : Nat) (eB pB rand : List Byte) : Option (Candidate × Rand) :=
  candidateStep (8 * pLen) (os2ip eB) (otherPrime pB) rand

/-- The status `vg_rsa_keygen_candidate` returns. -/
def candidateStatus : Option (Candidate × Rand) → Nat
  | none => 0
  | some (.prime _, _) => 1
  | some (.close, _) => 2
  | some (.rejected, _) => 3

/-- What a candidate's timing may depend on, beyond the lengths and `e`: what
became of it; for a probable prime, how many octets of `rand` were read; for
a rejected one, but too close to `p`, the octets read. -/
def candidateLeak (pLen : Nat) (eB pB rand : List Byte) : List Nat :=
  match candidateOp pLen eB pB rand with
  | none => [0]
  | some (.prime _, rest) => [1, rand.length - rest.length]
  | some (.close, _) => [2]
  | some (.rejected, rest) => 3 :: (rand.take (rand.length - rest.length)).map (·.toNat)

/-! ## `vg_rsa_keygen_candidate` -/

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

def candidateApi : Api where
  module := "rsa_keygen"
  name := "vg_rsa_keygen_candidate"
  sig := candidateSig
  writeArgs := true
  contracts := some fun A stack => candidateContract A stack
  summary := "One candidate for a prime of an RSA key, as BoringSSL's `generate_prime` \
    tests it (FIPS 186-5 Appendix A.1.3 steps 4 and 5). Reads from the front of `rand` \
    `out_len` octets, most significant first, sets the two most significant bits and the \
    least significant bit, and tests the candidate `c`: too close to `p` \
    (`|p − c| ≤ 2^(8 out_len − 100)`, if `p_len` is not 0); then divisible by one of the \
    first 512 primes (1024 above 1024 bits) but 2; then `gcd(c − 1, e) ≠ 1`; then \
    Miller–Rabin (FIPS 186-5 B.3.1), with the witnesses read from `rand` after the \
    candidate, at least 16 of them and as many as it takes for `BN_prime_checks_for_size` \
    of them to be uniform. Returns 1 and writes `c` to `out` if it passes, 2 if it is too \
    close to `p`, 3 if it fails otherwise, and writes the number of octets of `rand` it \
    read to `used`; or returns 0 if `rand` is too short, for which the caller calls it \
    again with `rand` extended by more random octets. `out` is zeros but for 1, and `used` \
    is 0 for 0. `e` (`e_len` bytes) and `p` (`p_len` bytes) are most significant first.\n\n\
    Contract: `VG.Spec.RsaKeyGen.candidateContract`. Timing may depend on the pointers, \
    the lengths, `e`, and on what became of the candidate: for a probable prime, on how \
    many octets of `rand` were read; for a candidate rejected for being too close to `p`, \
    on nothing else; for a candidate rejected otherwise, on the octets of `rand` read. Not \
    on `p`, or on the candidate if it is accepted."
  safety := ["`out_len` must be a multiple of 8 in 32..=512.", "`e_len` must be in 1..=8.",
    "`p_len` must be 0 or `out_len`.",
    "`scratch_len` must be at least `16 * out_len`.",
    "The contents of `scratch` on return are unspecified and may contain secrets; the caller \
      must destroy them after use."]

/-! ## `vg_rsa_keygen_key` -/

/-- `keyFromPrimes` for primes of `pLen` octets: the key, as octets: `n` and
`d` of `2 pLen`, and `p`, `q`, `dP`, `dQ` and `qInv` of `pLen`. -/
def keyOp (pLen : Nat) (eB pB qB : List Byte) : Except Failure (List (List Byte)) ⊕ Unit :=
  match keyFromPrimes (16 * pLen) (os2ip eB) (os2ip pB) (os2ip qB) with
  | .inl (.ok k) =>
    .inl (.ok [i2osp k.n (2 * pLen), i2osp k.d (2 * pLen), i2osp k.p pLen, i2osp k.q pLen,
      i2osp k.dP pLen, i2osp k.dQ pLen, i2osp k.qInv pLen])
  | .inl (.error f) => .inl (.error f)
  | .inr () => .inr ()

/-- The status `vg_rsa_keygen_key` returns. -/
def keyStatus : Except Failure (List (List Byte)) ⊕ Unit → Nat
  | .inl (.ok _) => 1
  | .inr () => 2
  | .inl (.error _) => 0

/-- `vg_rsa_keygen_key(n: *mut u8, n_len: usize, d: *mut u8, d_len: usize,
p: *mut u8, p_len: usize, q: *mut u8, q_len: usize, dp: *mut u8,
dp_len: usize, dq: *mut u8, dq_len: usize, qinv: *mut u8, qinv_len: usize,
e: *const u8, e_len: usize, scratch: *mut u64, scratch_len: usize) -> u32`. -/
def keySig : Sig where
  params := [("n", .slice true .u8 "n_len"), ("d", .slice true .u8 "d_len"),
    ("p", .slice true .u8 "p_len"), ("q", .slice true .u8 "q_len"),
    ("dp", .slice true .u8 "dp_len"), ("dq", .slice true .u8 "dq_len"),
    ("qinv", .slice true .u8 "qinv_len"), ("e", .slice false .u8 "e_len"),
    ("scratch", .slice true .u64 "scratch_len")]
  ret := some .u32

/-- The key from the primes at `p` and `q` (`keyOp`): 1 and the key at `n`,
`d`, `p`, `q`, `dp`, `dq` and `qinv`; 2 if `d` is too small, to generate the
primes again; 0 if a check failed; zeros at all seven but for 1. Constant
time but for `e` and the status. -/
def keyContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  keySig.contract A
    (pre := fun _n nLen _d dLen _p pLen _q qLen _dp dpLen _dq dqLen _qinv qinvLen _e eLen
        _scratch scratchLen _ =>
      primeLenValid pLen.toNat ∧ nLen.toNat = 2 * pLen.toNat ∧ dLen.toNat = nLen.toNat ∧
        qLen.toNat = pLen.toNat ∧ dpLen.toNat = pLen.toNat ∧ dqLen.toNat = pLen.toNat ∧
        qinvLen.toNat = pLen.toNat ∧ 1 ≤ eLen.toNat ∧ eLen.toNat ≤ 8 ∧
        scratchWords nLen.toNat ≤ scratchLen.toNat)
    (post := fun n nLen d _dLen p pLen q _qLen dp _dpLen dq _dqLen qinv _qinvLen e eLen
        _scratch _scratchLen m m' r =>
      let res := keyOp pLen.toNat (bytesAt m e eLen.toNat) (bytesAt m p pLen.toNat)
        (bytesAt m q pLen.toNat)
      let outs := [(n, nLen.toNat), (d, nLen.toNat), (p, pLen.toNat), (q, pLen.toNat),
        (dp, pLen.toNat), (dq, pLen.toNat), (qinv, pLen.toNat)]
      r.toNat = keyStatus res ∧
        match res with
        | .inl (.ok ys) => outs.map (fun o => bytesAt m' o.1 o.2) = ys
        | _ => ∀ o ∈ outs, bytesAt m' o.1 o.2 = List.replicate o.2 0)
    (writeArgs := true) (stack := stack)
    (leak := some fun _n _nLen _d _dLen p pLen q _qLen _dp _dpLen _dq _dqLen _qinv _qinvLen e
        eLen _scratch _scratchLen m =>
      (bytesAt m e eLen.toNat).map (·.toNat) ++
        [keyStatus (keyOp pLen.toNat (bytesAt m e eLen.toNat) (bytesAt m p pLen.toNat)
          (bytesAt m q pLen.toNat))])

def keyApi : Api where
  module := "rsa_keygen"
  name := "vg_rsa_keygen_key"
  sig := keySig
  writeArgs := true
  contracts := some fun A stack => keyContract A stack
  summary := "An RSA private key from its two primes, as BoringSSL's \
    `rsa_generate_key_impl` derives it (FIPS 186-5 Appendix A.1.3). With the primes `p` \
    and `q` (`p_len` bytes each) and the public exponent `e` (`e_len` bytes), all most \
    significant first, makes `p` the larger and computes \
    `d = e⁻¹ mod lcm(p − 1, q − 1)`; if `d ≤ 2^(8 p_len)`, writes zeros and returns 2, for \
    the caller to generate both primes again. Otherwise writes `n = p q` and `d` \
    (`n_len` bytes each), `p` and `q` (over the primes given), `dP = d mod (p − 1)`, \
    `dQ = d mod (q − 1)` and `qInv = q⁻¹ mod p` (`p_len` bytes each), all most \
    significant first, and returns 1, after checking that `n` has `16 p_len` bits and \
    the key what BoringSSL's `RSA_check_key` checks; or writes zeros to all seven and \
    returns 0 if `e` has no inverse, `q` has no inverse modulo `p`, or a check fails.\n\n\
    Contract: `VG.Spec.RsaKeyGen.keyContract`. Timing may depend on the pointers, the \
    lengths, `e`, and the value returned, not on the primes or the key."
  safety := ["`p_len` must be a multiple of 8 in 32..=512.",
    "`n_len` and `d_len` must be `2 * p_len`.",
    "`q_len`, `dp_len`, `dq_len` and `qinv_len` must be `p_len`.",
    "`e_len` must be in 1..=8."] ++ scratchSafety

end VG.Spec.RsaKeyGen
