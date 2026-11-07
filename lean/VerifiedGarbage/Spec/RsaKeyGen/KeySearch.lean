module

public import VerifiedGarbage.Spec.RsaKeyGen.Generation

/-!
# RSA key generation over refillable random tapes

**Trusted.** The whole of `generate` (`RsaKeyGen.lean`), but for where the
random octets come from, over the protocol of `Spec/Entropy.lean`: verified
code, rather than its host, validates the size and the exponent, draws `p`,
then `q` not too close to `p`, derives the key, draws both primes again when
`d` is too small, and starts a generation again when a prime's search is
exhausted, up to `keyGenerations` in all. Its host only refills the tape.

Each prime is searched for by `primeSearch` (`Generation.lean`), unchanged:
the candidates, their tests and their counted rejections are its; the key is
`keyFromPrimes`, of the primes' octets. The search's state across a refill
(`KeyProgress`) is public but for `p`, once it is found: the generations
left, which prime is being searched for, and the rejected candidates its
search still allows. `p` stays in the key's buffer, where the host passes it
back, so that its octets are consumed once it is found, and only an
unfinished candidate is ever run again. `KeySearchAgrees.lean` proves that
over the stream of octets the host hands out, the search is `generate`, but
where a candidate does not finish within its search's budget of entropy,
`primeEntropy`.

What timing may depend on is each prime search's trace (`primeSearch`'s: its
candidates' `candidateLeak`) and each key's status (`keyResultStatus`), in
order (`keySearch`'s trace): which
candidates were rejected, too close to `p` or accepted, how much the accepted
ones read, and whether a pair of primes gave a key, was refused for its small
`d`, or failed a check. Not on the primes or the key.
-/

@[expose] public section

namespace VG.Spec.RsaKeyGen

open VG.Spec.Rsa (os2ip i2osp)

/-- The generations `generate` allows (`RSA_generate_key_ex_maybe_fips`). -/
def keyGenerations : Nat := 4

/-! ## Starting -/

/-- The size and the exponent of a key search, of the requested `bits` and
the exponent's octets `eB` (any number of them, most significant first), as
`params` checks them: the exponent first (`exponentValid`), then the size
(`modulusBits`). `.error 0` for an invalid exponent, `.error 2` for an
invalid size; otherwise the search's first three public words, as the prime
search's (`primeInit`) for the primes of `nlen / 2` bits: the rejected
candidates its first prime may have, the primes' octets, `nlen / 16`, and
its budget of entropy. -/
def keySearchInit (bits : Nat) (eB : List Byte) : Except Nat (List Nat) :=
  let e := os2ip eB
  if !exponentValid e then .error 0 else
    match modulusBits bits with
    | none => .error 2
    | some nlen =>
      let pLen := nlen / 16
      .ok [primeLimit (8 * pLen) e, pLen, primeEntropy pLen]

/-! ## The search -/

/-- Which prime a key search is drawing: `p`, or `q`, not too close to `p`,
whose octets `pB` it has. -/
inductive KeyPhase where
  | p
  | q (pB : List Byte)
  deriving DecidableEq, Repr

/-- The prime the prime being drawn must not be too close to: none for `p`. -/
def KeyPhase.other : KeyPhase → List Byte
  | .p => []
  | .q pB => pB

/-- A key search's state across a refill: the generations it has left, this
one included; which prime it is drawing; and the rejected candidates that
prime's search still allows. -/
structure KeyProgress where
  left : Nat
  phase : KeyPhase
  remaining : Nat
  deriving DecidableEq, Repr

/-- A key search's result: its state across a refill, and its result the key,
or the failure of a check of `keyFromPrimes`; exhausted if every generation
was. -/
abbrev KeySearchResult := Entropy.Result KeyProgress (Except Failure Key)

/-- The status of a key from its primes, as `vg_rsa_keygen_key` returns it
(`keyStatus`): 1 for a key, 2 for a `d` too small, 0 for a failed check. -/
def keyResultStatus : Except Failure Key ⊕ Unit → Nat
  | .inl (.ok _) => 1
  | .inr () => 2
  | .inl (.error _) => 0

/-- Search the tape for a key with primes of `pLen` octets and the public
exponent `eB`, from the state `s`: the prime it is drawing (`primeSearch`),
and then:

* if that search asks for more entropy, so does the key search, with that
  search's state;
* if it is exhausted, this generation fails: the search is exhausted if it
  was the last (`s.left ≤ 1`), and otherwise starts the next one with `p`,
  where that search stopped;
* if it accepts `p`, it goes on to `q`, not too close to `p`, where that
  search stopped;
* if it accepts `q`, the key from the two (`keyFromPrimes`, of their
  octets), unless `d` is too small: then it goes on to draw both again, in
  the same generation.

Each prime's search starts with `primeLimit` rejected candidates allowed. Its
trace is each prime search's status, consumption, octets left and trace, each
after its length and a 0, and each key's status after a 1. A search that
accepts a prime having read nothing (which none does: a candidate reads its
`pLen` octets) ends the key search, exhausted. -/
def keySearch (pLen : Nat) (eB : List Byte) (s : KeyProgress) (rand : Rand) :
    KeySearchResult :=
  let limit := primeLimit (8 * pLen) (os2ip eB)
  let r := primeSearch pLen eB s.phase.other s.remaining rand
  let body := [r.status, r.used, r.available] ++ r.trace
  let trace := 0 :: body.length :: body
  match r.outcome with
  | .entropy remaining available => ⟨.entropy { s with remaining } available, r.used, trace⟩
  | .exhausted =>
    if s.left ≤ 1 then ⟨.exhausted, r.used, trace⟩
    else (keySearch pLen eB ⟨s.left - 1, .p, limit⟩ (rand.drop r.used)).consume r.used trace
  | .accepted c =>
    if _h : (rand.drop r.used).length < rand.length then
      match s.phase with
      | .p =>
        (keySearch pLen eB ⟨s.left, .q (i2osp c pLen), limit⟩ (rand.drop r.used)).consume
          r.used trace
      | .q pB =>
        let k := keyFromPrimes (16 * pLen) (os2ip eB) (os2ip pB) (os2ip (i2osp c pLen))
        let trace := trace ++ [1, keyResultStatus k]
        match k with
        | .inl res => ⟨.accepted res, r.used, trace⟩
        | .inr () =>
          (keySearch pLen eB ⟨s.left, .p, limit⟩ (rand.drop r.used)).consume r.used trace
    else ⟨.exhausted, r.used, trace⟩
termination_by (rand.length, s.left)
decreasing_by
  · rw [List.length_drop, Prod.lex_def]
    omega
  all_goals exact Prod.Lex.left _ _ _h

/-! ## What a search reports -/

/-- The status a key search returns: 0 for more entropy, 1 for a key, 2 for a
failed check of the key, 3 if every generation was exhausted. -/
def KeySearchResult.keyStatus (r : KeySearchResult) : Nat :=
  match r.outcome with
  | .entropy .. => 0
  | .accepted (.ok _) => 1
  | .accepted (.error _) => 2
  | .exhausted => 3

/-- The state a key search leaves for the next call: its state across the
refill, or none left (no generations, `p`'s phase, no candidates) if it
ended. -/
def KeySearchResult.progress (r : KeySearchResult) : KeyProgress :=
  match r.outcome with
  | .entropy s _ => s
  | _ => ⟨0, .p, 0⟩

/-- A key as octets, most significant first: `n` and `d` of `2 pLen`, then
`p`, `q`, `dP`, `dQ` and `qInv` of `pLen`, each after the other. -/
def keyBytes (pLen : Nat) (k : Key) : List Byte :=
  i2osp k.n (2 * pLen) ++ i2osp k.d (2 * pLen) ++ i2osp k.p pLen ++ i2osp k.q pLen ++
    i2osp k.dP pLen ++ i2osp k.dQ pLen ++ i2osp k.qInv pLen

end VG.Spec.RsaKeyGen
