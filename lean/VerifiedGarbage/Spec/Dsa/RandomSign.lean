module

public import VerifiedGarbage.Spec.Dsa.Random
public import VerifiedGarbage.Spec.Dsa.SignVerify

/-!
# Bounded randomized DSA signing (trusted)

Moves the specification boundary beyond supplied-nonce signing: eight signing
attempts, each with at most 128 rejection-sampling draws, matching src/dsa.rs.
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

def randomSignContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  randomSignSig.contract A
    (pre := fun _out outLen _used _key keyLen pLen qLen _digest _digestLen
        _rand _randLen _scratch scratchLen _ =>
      lengthsValid pLen.toNat qLen.toNat ∧ outLen.toNat = 2 * qLen.toNat ∧
        keyLen.toNat = 3 * pLen.toNat + 2 * qLen.toNat ∧
        randomSignScratchWords pLen.toNat ≤ scratchLen.toNat)
    (post := fun out outLen used key keyLen pLen qLen digest digestLen
        rand randLen _scratch _scratchLen m m' r =>
      let res := randomSignBytes pLen.toNat qLen.toNat (bytesAt m key keyLen.toNat)
        (bytesAt m digest digestLen.toNat) (bytesAt m rand randLen.toNat)
      r.toNat = res.status ∧
        bytesAt m' out outLen.toNat = res.signature.getD (List.replicate outLen.toNat 0) ∧
        wordsAt m' used 1 = [BitVec.ofNat 64 res.used])
    (writeArgs := true) (stack := stack)
    (leak := some fun _out _outLen _used key keyLen pLen qLen digest digestLen
        rand randLen _scratch _scratchLen m =>
      let kb := bytesAt m key keyLen.toNat
      let res := randomSignBytes pLen.toNat qLen.toNat kb
        (bytesAt m digest digestLen.toNat) (bytesAt m rand randLen.toNat)
      publicBytesLeak pLen.toNat qLen.toNat kb ++ [res.status, res.used] ++ res.trace)

def randomSignApi : Api where
  module := "dsa"
  name := "vg_dsa_sign_random"
  sig := randomSignSig
  writeArgs := true
  contracts := some fun A stack => randomSignContract A stack
  summary := "Randomized DSA signing of a prehashed digest from fresh independent random \
    octets. Up to eight signing attempts, each with 128 nonce draws. Returns 1 with \
    fixed-width r||s, 0 for invalid key/retry exhaustion, or 2 for insufficient random \
    bytes. On failure out is zero. used counts consumed complete draws on every return. \
    Checks algebraic consistency, not primality. Timing may depend on public p,q,g,y, \
    sampling decisions, signing success bits and consumption, not otherwise on secrets. \
    Contract: `VG.Spec.Dsa.randomSignContract`."
  safety := ["(p_len, q_len) must be (128,20), (256,20), (256,28), (256,32), or (384,32).",
    "key_len must be 3*p_len + 2*q_len; out_len must be 2*q_len.",
    "scratch_len must be at least 16*p_len + 64 words; destroy scratch after use.",
    "Caller must assure domain validity and provide fresh independent random octets; \
      never reuse a completed signing tape for another signature."]

end VG.Spec.Dsa
