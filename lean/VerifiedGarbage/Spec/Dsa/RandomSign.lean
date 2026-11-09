module

public import VerifiedGarbage.Spec.Dsa.Random
public import VerifiedGarbage.Spec.Dsa.SignVerify

/-!
# Bounded randomized DSA signing (trusted)

Moves the specification boundary beyond supplied-nonce signing: eight signing
attempts, each with at most 128 rejection-sampling draws, matching src/dsa.rs.
`vg_dsa_sign_random_prevalidated`'s contract (`PrevalidatedSign.lean`) states
its result with `randomSignBytes`, for a key validated beforehand.
The tape is fresh independent random octets, consumed from its front without
reuse. A caller may extend an exhausted tape and replay this operation, but
must never reuse that tape for another message or another completed signing.

The leakage includes public key components, sampling decisions, and each
signing attempt's success bit (already allowed by signContract). It excludes
nonce values, private scalars, digests, and unused random bytes. This is not
an unconditional secret-independent timing claim. The probability/security
interpretation of those decisions is outside this deterministic contract.
-/

@[expose] public section

namespace VG.Spec.Dsa

open VG.Spec.Rsa (bytesAt wordsAt)

/-- Status: 0 invalid key or retry limit, 1 signature, 2 insufficient tape. -/
structure RandomSignResult where
  signature : Option (List Byte)
  status : Nat
  used : Nat
  trace : List Nat
  deriving DecidableEq, Repr

/-- The inner retry loop. Every successful draw is used once, even when
signing returns zero r/s or rejects an inconsistent key. -/
def randomSignLoop (pLen qLen : Nat) (key digest : List Byte) :
    Nat → List Byte → RandomSignResult
  | 0, _ => ⟨none, 0, 0, [3]⟩
  | fuel + 1, rand =>
    let q := (privateKeyBytes pLen qLen key).params.q
    let draw := Random.sample q 128 rand
    match draw.scalar with
    | none => ⟨none, if draw.trace.getLast? == some 2 then 2 else 0,
        draw.used, draw.trace⟩
    | some k =>
      match signBytes pLen qLen key (encodeBE qLen k) digest with
      | some signature => ⟨some signature, 1, draw.used, draw.trace ++ [5]⟩
      | none =>
        let next := randomSignLoop pLen qLen key digest fuel (rand.drop draw.used)
        { next with
          used := draw.used + next.used
          trace := draw.trace ++ [6] ++ next.trace }

/-- Full randomized signing on the existing packed-key encoding. -/
def randomSignBytes (pLen qLen : Nat) (key digest rand : List Byte) : RandomSignResult :=
  if !(lengthsValid pLen qLen) || key.length != 3 * pLen + 2 * qLen then
    ⟨none, 0, 0, [4]⟩
  else randomSignLoop pLen qLen key digest 8 rand

/-- Space for the single-attempt signer, sampled nonce and loop state. -/
def randomSignScratchWords (pLen : Nat) : Nat := scratchWords pLen + 64

def randomSignSig : Sig where
  params := [("out", .slice true .u8 "out_len"), ("used", .array true .u64 1),
    ("key", .slice false .u8 "key_len"), ("p_len", .int .usize true),
    ("q_len", .int .usize true), ("digest", .slice false .u8 "digest_len"),
    ("rand", .slice false .u8 "rand_len"), ("scratch", .slice true .u64 "scratch_len")]
  ret := some .u32

end VG.Spec.Dsa
