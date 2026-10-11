module

public import VerifiedGarbage.Spec.Rsa

/-!
# RSA key generation (FIPS 186-5 Appendix A.1.3, as BoringSSL does it)

**Trusted** (as every file in `Spec/`). `generate bits e rand`: a two-prime
RSA private key with a modulus of `bits` bits and the public exponent `e`,
with probable primes, by FIPS 186-5 Appendix A.1.3 with BoringSSL's concrete
choices, transcribed from `crypto/fipsmodule/rsa/rsa_impl.cc.inc`
(`generate_prime`, `rsa_generate_key_impl`, `RSA_generate_key_ex_maybe_fips`)
and `crypto/fipsmodule/bn/prime.cc.inc` (`BN_primality_test`,
`bn_odd_number_is_obviously_composite`, `bn_miller_rabin_iteration`):

* Sizes and exponents (`params`): a requested size above 8192 bits is
  refused, the size is rounded down to a multiple of 128 bits, and a size
  below 512 bits is refused; `e` must be odd and from 3 to `2^32 - 1`.
  BoringSSL's upper bound is 16384 bits; ours is the bound of the modulus
  `Rsa.modulusValid` takes.
* Each prime has `nlen / 2` bits, its two most significant bits and its least
  significant bit set (`candidate`, BoringSSL's
  `BN_rand(…, BN_RAND_TOP_TWO, BN_RAND_BOTTOM_ODD)`), which is A.1.3 steps
  4.2–4.4 and 5.2–5.4: it is odd and above `√2 · 2^(nlen/2 - 1)`.
* `q` is rejected if `|p − q| ≤ 2^(nlen/2 − 100)` (step 5.5), without counting
  it as a try.
* A candidate divisible by one of the first 512 primes (1024 above 1024
  bits) but 2 is rejected (`obviouslyComposite`), then one with
  `gcd(c − 1, e) ≠ 1` (steps 4.5 and 5.6), then one that fails Miller–Rabin
  (`primalityTest`, FIPS 186-5 B.3.1, with `BN_prime_checks_for_size`'s
  rounds and BoringSSL's blinding: at least 16 witnesses, and as many as it
  takes for that many of them to be uniform). After `5 · nlen / 2` rejected
  candidates (`8 · nlen / 2` for `e = 3`) the prime's generation fails
  (steps 4.7 and 5.8).
* `p` is the larger prime, `d = e⁻¹ mod lcm(p − 1, q − 1)`, and both primes
  are generated again if `d ≤ 2^(nlen/2)` (FIPS 186-5's lower bound on `d`).
* The key is checked as `RSA_check_key` checks it (`keyValid`, which is
  `Rsa.checkKey`), and its modulus must have `nlen` bits.
* A generation that fails for too many tries is started again, up to four
  times in all (`RSA_generate_key_ex_maybe_fips`).
* Finally, beyond what `RSA_generate_key_ex` does, the key must pass the
  pairwise consistency test of BoringSSL's `RSA_check_fips` (`pairwiseOk`):
  the signature of a fixed message with the private key, by the private
  operation checked against `e` (`Rsa.privateChecked`), verifies with the
  public key.

The randomness is an explicit input, the octet string `rand`, read from the
front: each draw of `len` octets (`draw`) takes the next `len` octets as an
integer, most significant first (where BoringSSL fills words with random
octets; the distribution is the same). So `generate` is deterministic given
`rand`; it returns `none` if `rand` runs out, and a caller supplying more
randomness gets the same result for any extension of a `rand` that
sufficed. Every loop draws at least one octet in each iteration, which is
why it terminates (`loop`).

Primality is probable: nothing here proves that `p` and `q` are prime (as
nothing in A.1.3 does). The key check and the pairwise consistency test do
not depend on it.

What timing may depend on is the contracts' business (`RsaKeyGen/Contract`):
as in BoringSSL, on how many candidates were rejected and on everything about
a rejected candidate (only on the rejection, for one too close to `p`), not
on the primes or the private key.
-/

@[expose] public section

namespace VG.Spec.RsaKeyGen

open VG.Spec.Rsa (os2ip i2osp powMod inverse splitTwos)

/-! ## Randomness -/

/-- The random octets still to be read. -/
abbrev Rand := List Byte

/-- The next `len` octets of `r`, as an integer most significant first, and
the octets after them; `none` if `r` has fewer than `len` octets. -/
def draw (len : Nat) (r : Rand) : Option (Nat × Rand) :=
  let x := r.take len
  if x.length = len then some (os2ip x, r.drop len) else none

/-- Iterate `step` from the state `s`: `step s r` either finishes with
`.inl a` or goes on with the state `.inr s'`, and returns the octets it did
not read. An iteration that goes on must have read at least one octet (every
step here does), so the loop ends; one that did not is a failure, `none`,
as is a step that ran out of octets. -/
def loop {σ α : Type} (step : σ → Rand → Option ((α ⊕ σ) × Rand)) (s : σ) (r : Rand) :
    Option (α × Rand) :=
  match step s r with
  | none => none
  | some (.inl a, r') => some (a, r')
  | some (.inr s', r') => if r'.length < r.length then loop step s' r' else none
termination_by r.length

/-! ## Integers -/

/-- The number of bits of `n` (`BN_num_bits`), 0 for 0. -/
def bitLength (n : Nat) : Nat := if n = 0 then 0 else n.log2 + 1

/-- `|a − b|`. -/
def absDiff (a b : Nat) : Nat := if a ≤ b then b - a else a - b

/-! ## Sizes and exponents (`rsa_generate_key_impl`) -/

/-- The largest modulus generated, in bits: `Rsa.modulusValid`'s bound
(BoringSSL's `OPENSSL_RSA_MAX_MODULUS_BITS` is 16384). -/
def maxBits : Nat := 8192

/-- The smallest modulus generated, in bits (`OPENSSL_RSA_MIN_MODULUS_BITS`). -/
def minBits : Nat := 512

/-- The size of the modulus generated for the requested `bits`: refused above
`maxBits`, rounded down to a multiple of 128 bits, and refused below
`minBits`. -/
def modulusBits (bits : Nat) : Option Nat :=
  if maxBits < bits then none else
    let b := bits / 128 * 128
    if b < minBits then none else some b

/-- A public exponent keys are generated with: odd, at least 3, and at most
32 bits. -/
def exponentValid (e : Nat) : Bool := e % 2 == 1 && 3 ≤ e && e < 2 ^ 32

/-! ## Trial division (`bn_odd_number_is_obviously_composite`) -/

/-- Whether `n` is prime, by trial division (for the small primes only). -/
def smallPrime (n : Nat) : Bool := 2 ≤ n && (List.range n).all fun d => d < 2 || n % d != 0

/-- BoringSSL's `kPrimes`: the first 1024 primes, which are the primes below
8162 (the 1024th is 8161). -/
def smallPrimes : List Nat := (List.range 8162).filter smallPrime

/-- How many of `smallPrimes` trial division uses for a candidate of `bits`
bits (`num_trial_division_primes`): all of them above 1024 bits, else half. -/
def trialPrimes (bits : Nat) : Nat := if 1024 < bits then 1024 else 512

/-- `bn_odd_number_is_obviously_composite` of the odd candidate `c` of
`bits` bits: whether one of the first `trialPrimes bits` primes but 2
divides `c` and is not `c`. -/
def obviouslyComposite (bits c : Nat) : Bool :=
  ((smallPrimes.take (trialPrimes bits)).drop 1).any fun s => c % s == 0 && c != s

/-! ## Miller–Rabin (`BN_primality_test`, FIPS 186-5 B.3.1) -/

/-- `BN_prime_checks_for_size`: the uniform Miller–Rabin witnesses a
candidate of `bits` bits needs. -/
def checksForSize (bits : Nat) : Nat :=
  if 3747 ≤ bits then 3 else if 1345 ≤ bits then 4 else if 476 ≤ bits then 5 else
  if 400 ≤ bits then 6 else if 347 ≤ bits then 7 else if 308 ≤ bits then 8 else
  if 55 ≤ bits then 27 else 34

/-- `BN_PRIME_CHECKS_BLINDED`: the least number of witnesses tried for a
probable prime. -/
def blindedChecks : Nat := 16

/-- The octets drawn for a witness for `w`: whole 64-bit words, as many as
`w − 1` has. -/
def witnessBytes (w : Nat) : Nat := 8 * ((bitLength (w - 1) + 63) / 64)

/-- `bn_rand_secret_range(b, …, 2, w1)` from the random `x`: `x` cut to the
bits of `w1`; if that is in `[2, w1 − 1]` it is the witness, uniform;
otherwise it is forced into the range, by setting bit 1 and clearing the
most significant bit of `w1`'s length, and is not uniform. -/
def witness (w1 x : Nat) : Nat × Bool :=
  let l := bitLength w1
  let x := x % 2 ^ l
  if 2 ≤ x ∧ x < w1 then (x, true) else ((x ||| 2) % 2 ^ (l - 1), false)

/-- B.3.1 step 4.5's loop of `bn_miller_rabin_iteration`, from `j` with
`fuel` iterations left (up to `w_bits − 1`): square `z`; `w − 1` makes `w`
possibly prime; `1` before that, or `j = a` without it, proves `w`
composite. -/
def mrSquarings (w a : Nat) : (fuel j z : Nat) → (possible : Bool) → Bool
  | 0, _, _, possible => possible
  | fuel + 1, j, z, possible =>
    if j = a ∧ !possible then possible else
      let z := z * z % w
      let possible := possible || z == w - 1
      if z == 1 && !possible then possible else mrSquarings w a fuel (j + 1) z possible

/-- `bn_miller_rabin_iteration` (B.3.1 steps 4.3–4.5) for the odd `w` with
`w − 1 = 2^a m`, `m` odd, and the witness `b`: `false` if `b` proves `w`
composite. -/
def mrIteration (w a m b : Nat) : Bool :=
  let z := powMod b m w
  mrSquarings w a (bitLength w - 1) 1 z (z == 1 || z == w - 1)

/-- One iteration of `BN_primality_test`'s loop (B.3.1 step 4) for the odd
`w > 3` with `w − 1 = 2^a m`, after `i − 1` witnesses of which `uniform`
were uniform: done, probably prime, after at least `blindedChecks` witnesses
of which `checks` were uniform; otherwise draw a witness: composite if it
proves so, else go on. -/
def mrStep (w checks a m : Nat) (s : Nat × Nat) (r : Rand) :
    Option ((Bool ⊕ (Nat × Nat)) × Rand) :=
  let (i, uniform) := s
  if i ≤ blindedChecks ∨ uniform < checks then do
    let (x, r) ← draw (witnessBytes w) r
    let (b, u) := witness (w - 1) x
    if mrIteration w a m b then
      return (.inr (i + 1, uniform + if u then 1 else 0), r)
    else return (.inl false, r)
  else some (.inl true, r)

/-- `BN_primality_test(w, BN_prime_checks_for_generation, …,
do_trial_division = 0)`: whether `w` is probably prime, drawing its
witnesses from `r`, and the octets left. -/
def primalityTest (w : Nat) (r : Rand) : Option (Bool × Rand) :=
  if w ≤ 1 then some (false, r)
  else if w % 2 = 0 then some (w == 2, r)
  else if w = 3 then some (true, r)
  else
    let (a, m) := splitTwos (w - 1)
    loop (mrStep w (checksForSize (bitLength w)) a m) (1, 0) r

/-! ## Primes (`generate_prime`, A.1.3 steps 4 and 5) -/

/-- Why a generation failed. -/
inductive Failure where
  /-- The size or the public exponent is refused. -/
  | badParameters
  /-- Too many candidates were rejected (`RSA_R_TOO_MANY_ITERATIONS`). -/
  | tooManyIterations
  /-- A check failed that the construction should make impossible. -/
  | internal
  deriving DecidableEq, Repr

/-- `BN_rand(…, bits, BN_RAND_TOP_TWO, BN_RAND_BOTTOM_ODD)` from the random
`x`: `x` cut to `bits` bits, with its two most significant bits and its least
significant bit set. -/
def candidate (bits x : Nat) : Nat := x % 2 ^ bits ||| 3 * 2 ^ (bits - 2) ||| 1

/-- Step 5.5: whether the candidate `c` for `q` is too close to `p`:
`|p − c| ≤ 2^(bits − 100)`. No `p` (for `p` itself): never. -/
def tooClose (bits : Nat) (p : Option Nat) (c : Nat) : Bool :=
  match p with
  | none => false
  | some p => absDiff c p ≤ 2 ^ (bits - 100)

/-- The most candidates for one prime that may be rejected (steps 4.7 and
5.8): `5 · bits`, or `8 · bits` for `e = 3`. -/
def primeLimit (bits e : Nat) : Nat := if e = 3 then 8 * bits else 5 * bits

/-- What became of a candidate for a prime. -/
inductive Candidate where
  /-- It is a probable prime, accepted. -/
  | prime (c : Nat)
  /-- It was too close to `p` (step 5.5), which does not count as a try. -/
  | close
  /-- It was rejected, by trial division, `gcd(c − 1, e) ≠ 1` or
  Miller–Rabin. -/
  | rejected
  deriving DecidableEq, Repr

/-- One candidate of `generate_prime`'s loop: draw a candidate `c` of `bits`
bits; reject it if it is too close to `p`; accept it if it passes trial
division, `gcd(c − 1, e) = 1` and Miller–Rabin (in that order, each only if
the one before passed); otherwise reject it. -/
def candidateStep (bits e : Nat) (p : Option Nat) (r : Rand) : Option (Candidate × Rand) := do
  let (x, r) ← draw (bits / 8) r
  let c := candidate bits x
  if tooClose bits p c then return (.close, r)
  let (prime, r) ←
    if !obviouslyComposite bits c && Nat.gcd (c - 1) e == 1 then primalityTest c r
    else some (false, r)
  if prime then return (.prime c, r) else return (.rejected, r)

/-- One iteration of `generate_prime`'s loop, after `tries` counted
rejections: a candidate (`candidateStep`); a candidate too close to `p` is
not counted, and after `primeLimit` rejected ones the prime's generation
fails. -/
def primeStep (bits e : Nat) (p : Option Nat) (tries : Nat) (r : Rand) :
    Option ((Except Failure Nat ⊕ Nat) × Rand) := do
  let (res, r) ← candidateStep bits e p r
  match res with
  | .prime c => return (.inl (.ok c), r)
  | .close => return (.inr tries, r)
  | .rejected =>
    if primeLimit bits e ≤ tries + 1 then return (.inl (.error .tooManyIterations), r)
    else return (.inr (tries + 1), r)

/-- `generate_prime(out, bits, e, p, …)`: a probable prime of `bits` bits
(a multiple of 64, at least 128) with `gcd(c − 1, e) = 1`, not too close to
`p` if there is one. -/
def generatePrime (bits e : Nat) (p : Option Nat) (r : Rand) :
    Option (Except Failure Nat × Rand) :=
  if bits < 128 ∨ bits % 64 ≠ 0 then some (.error .internal, r)
  else loop (primeStep bits e p) 0 r

/-! ## Keys (`rsa_generate_key_impl`) -/

/-- A two-prime RSA private key, with its CRT values (RFC 8017 §3.2). -/
structure Key where
  n : Nat
  e : Nat
  d : Nat
  p : Nat
  q : Nat
  dP : Nat
  dQ : Nat
  qInv : Nat
  deriving DecidableEq, Repr

/-- The octets of the modulus `n`: `⌈bits / 8⌉`. -/
def Key.len (k : Key) : Nat := (bitLength k.n + 7) / 8

/-- An integer of the key as `k.len` octets, most significant first, as a
private key is given to the private operations. -/
def Key.octets (k : Key) (x : Nat) : List Byte := i2osp x k.len

/-- The key check, `RSA_check_key` (`Rsa.checkKey`, which a private key
must pass to be imported), of the key as octets. -/
def keyValid (k : Key) : Bool :=
  Rsa.checkKey (k.octets k.n) (k.octets k.e) (k.octets k.d) (k.octets k.p) (k.octets k.q)
    (k.octets k.dP) (k.octets k.dQ) (k.octets k.qInv)

/-- The rest of an iteration of `rsa_generate_key_impl`'s loop, and what
follows it, from the primes of `nlen / 2` bits: make `p` the larger;
`d = e⁻¹ mod lcm(p − 1, q − 1)`, or `.inr ()` to start again if
`d ≤ 2^(nlen/2)`; then the key, with `n = p q`, `dP = d mod (p − 1)`,
`dQ = d mod (q − 1)` and `qInv = q⁻¹ mod p`, checked to have a modulus of
`nlen` bits and by `keyValid`. (BoringSSL computes `qInv` as `q^(p−2) mod p`,
the same for a prime `p`; `inverse` is the inverse for any `p`, or none.) -/
def keyFromPrimes (nlen e p q : Nat) : Except Failure Key ⊕ Unit :=
  let (p, q) := if p < q then (q, p) else (p, q)
  match inverse e (Nat.lcm (p - 1) (q - 1)) with
  | none => .inl (.error .internal)
  | some d =>
    if d ≤ 2 ^ (nlen / 2) then .inr ()
    else
      match inverse q p with
      | none => .inl (.error .internal)
      | some qInv =>
        let k : Key := ⟨p * q, e, d, p, q, d % (p - 1), d % (q - 1), qInv⟩
        if bitLength k.n = nlen ∧ keyValid k then .inl (.ok k) else .inl (.error .internal)

/-- One iteration of `rsa_generate_key_impl`'s loop: generate `p`, then `q`
(not too close to `p`), with `nlen / 2` bits each, and then
`keyFromPrimes`. -/
def keyStep (nlen e : Nat) (_ : Unit) (r : Rand) : Option ((Except Failure Key ⊕ Unit) × Rand) := do
  let (p, r) ← generatePrime (nlen / 2) e none r
  match p with
  | .error f => return (.inl (.error f), r)
  | .ok p =>
    let (q, r) ← generatePrime (nlen / 2) e (some p) r
    match q with
    | .error f => return (.inl (.error f), r)
    | .ok q => return (keyFromPrimes nlen e p q, r)

/-- `rsa_generate_key_impl` for a size `nlen` and an exponent `e` already
validated. -/
def generateOnce (nlen e : Nat) (r : Rand) : Option (Except Failure Key × Rand) :=
  loop (keyStep nlen e) () r

/-! ## The pairwise consistency test (`RSA_check_fips`) -/

/-- The DER encoding of SHA-256's `DigestInfo` but for the digest (RFC 8017
§9.2, note 1). -/
def sha256DigestInfoPrefix : List Byte :=
  [0x30, 0x31, 0x30, 0x0d, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x01,
    0x05, 0x00, 0x04, 0x20]

/-- The message representative `RSA_check_fips` signs, for a modulus of `k`
octets: EMSA-PKCS1-v1_5 (RFC 8017 §9.2) of SHA-256 with the digest of 32
zero octets, `0x00 ‖ 0x01 ‖ PS ‖ 0x00 ‖ T`. -/
def pairwiseMessage (k : Nat) : List Byte :=
  let t := sha256DigestInfoPrefix ++ List.replicate 32 0
  [0x00, 0x01] ++ List.replicate (k - 3 - t.length) 0xff ++ [0x00] ++ t

/-- The pairwise consistency test: the message representative, signed with
the private key by the private operation checked against `e`
(`Rsa.privateChecked`), verifies with the public key (RSAVP1). -/
def pairwiseOk (k : Key) : Bool :=
  let em := pairwiseMessage k.len
  match Rsa.privateChecked (k.octets k.n) (k.octets k.e) em (k.octets k.p) (k.octets k.q)
      (k.octets k.dP) (k.octets k.dQ) (k.octets k.qInv) with
  | .ok s => Rsa.publicOp (k.octets k.n) (k.octets k.e) s == some em
  | .invalid | .fault => false

/-! ## `generate` -/

/-- The size and exponent of a key generation (`modulusBits`,
`exponentValid`): the modulus' size in bits, or `none` if refused. -/
def params (bits e : Nat) : Option Nat :=
  if exponentValid e then modulusBits bits else none

/-- `RSA_generate_key_ex` of `bits` and `e` from the randomness `rand`, and
then the pairwise consistency test: `some (.ok key)`, `some (.error f)`, or
`none` if `rand` ran out. A generation that fails with too many tries is
started again, from where it stopped reading `rand`, up to four times in
all. -/
def generate (bits e : Nat) (rand : Rand) : Option (Except Failure Key) :=
  match params bits e with
  | none => some (.error .badParameters)
  | some nlen => attempts nlen 4 rand
where
  /-- At most `left` generations. -/
  attempts (nlen : Nat) : Nat → Rand → Option (Except Failure Key)
    | 0, _ => some (.error .tooManyIterations)
    | left + 1, r =>
      match generateOnce nlen e r with
      | none => none
      | some (.error .tooManyIterations, r) => attempts nlen left r
      | some (.error f, _) => some (.error f)
      | some (.ok k, _) => if pairwiseOk k then some (.ok k) else some (.error .internal)

end VG.Spec.RsaKeyGen
