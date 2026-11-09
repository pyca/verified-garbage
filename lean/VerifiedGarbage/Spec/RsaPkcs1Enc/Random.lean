module

public import VerifiedGarbage.Spec.RsaPkcs1Enc.Contract
public import VerifiedGarbage.Spec.Entropy

/-!
# RSAES-PKCS1-v1_5 encryption from a random tape

**Trusted** (as every file in `Spec/`). `vg_rsa_pkcs1_encrypt_random`:
RSAES-PKCS1-V1_5-ENCRYPT (`encrypt`) with the padding string `PS` drawn by
the verified code from a tape of random octets, and the modulus given also
by the values `vg_rsa_public_precompute` computed for it
(`Rsa.publicPrecompute`). RFC 8017 §7.2.1 step 2.a asks
for `PS` to be `k - mLen - 3` "pseudo-randomly generated nonzero octets"; here
`PS` is the first `k - mLen - 3` nonzero octets of the tape (`nonzeroPrefix`):
each zero octet is rejected, and the octets kept are, for a tape of
independent uniform octets, independent and uniform over 1–255.

The tape is served by the protocol of `Spec/Entropy.lean`, the whole of `PS`
being one step (`padSearch`): if the tape has too few nonzero octets, the
function consumes none of it and asks for a longer one (status 0), which the
host makes by appending fresh random octets to the same tape; once `PS` is
drawn it encrypts (status 1, or 2 if `n` or `e` is not a number
`Rsa.publicOpChecked` takes); it gives up (status 3) only if a tape of its
whole budget, `padEntropy`, `PS`'s length and 128 octets more, has too few
nonzero octets: more than 128 of at most 1149 uniform octets are zero, which
has a probability below 2⁻⁴⁰⁰, so in practice only a broken random number
generator.

The public key, its precomputed values and the lengths are public, and may
affect timing; the message and `PS` are secret. So is which octets of the tape
were zero (`zeroMask`, the trace of `padSearch`), among those it consumed,
or all of them when it asks for more or gives up, but it may affect timing
too. Those octets are discarded,
and the positions of the zero octets of a uniform tape are independent of the
values of the others, so they reveal nothing about `PS`; `PS`'s octets and
the message never affect timing.
-/

@[expose] public section

namespace VG.Spec.RsaPkcs1Enc

open Rsa (bytesAt wordsAt lenValid publicScratchWords publicScratchSafety exponentDoc)

/-! ## Drawing the padding string -/

/-- The entropy budget of a padding string of `psLen` octets: `psLen + 128`
octets, the longest tape the function asks for. -/
def padEntropy (psLen : Nat) : Nat := psLen + 128

/-- The first `n` nonzero octets of `rand`, and the number of octets of
`rand` up to and including the last of them; `none` if `rand` has fewer than
`n` nonzero octets. -/
def nonzeroPrefix : Nat → List Byte → Option (List Byte × Nat)
  | 0, _ => some ([], 0)
  | _ + 1, [] => none
  | n + 1, b :: rand =>
    if b = 0 then (nonzeroPrefix (n + 1) rand).map fun r => (r.1, r.2 + 1)
    else (nonzeroPrefix n rand).map fun r => (b :: r.1, r.2 + 1)

/-- Which octets of `xs` are zero: 1 for each zero octet, 0 for each other. -/
def zeroMask (xs : List Byte) : List Nat := xs.map fun b => if b = 0 then 1 else 0

/-- The result of drawing a padding string: the outcome of `Spec/Entropy.lean`,
with no state across a refill, and the padding string. -/
abbrev PadResult := Entropy.Result Unit (List Byte)

/-- Drawing a padding string of `psLen` octets from the tape `rand`
(`Spec/Entropy.lean`): if `rand` has `psLen` nonzero octets, the first
`psLen` of them (`nonzeroPrefix`), having consumed the octets up to the last;
otherwise, if `rand` is as long as the budget `padEntropy psLen`, giving up;
or else asking for more, having consumed nothing, with all of `rand` left.
The trace is which consumed octets were zero, or which of `rand` were. -/
def padSearch (psLen : Nat) (rand : List Byte) : PadResult :=
  match nonzeroPrefix psLen rand with
  | some (ps, used) => ⟨.accepted ps, used, zeroMask (rand.take used)⟩
  | none =>
    if padEntropy psLen ≤ rand.length then ⟨.exhausted, rand.length, zeroMask rand⟩
    else ⟨.entropy () rand.length, 0, zeroMask rand⟩

/-! ## `vg_rsa_pkcs1_encrypt_random` -/

/-- The postcondition of encryption with a drawn padding string, for the
`nLen` octets at `out`: for a ciphertext, return 1 and the ciphertext; for
a key `encrypt` refuses, return 2 and zeros. -/
def writtenRandom (m' : Mem) (out : Addr) (nLen : Nat) (r : BitVec 32) :
    Option (List Byte) → Prop
  | some C => r = 1 ∧ bytesAt m' out nLen = C
  | none => r = 2 ∧ bytesAt m' out nLen = List.replicate nLen 0

/-- `vg_rsa_pkcs1_encrypt_random(out: *mut u8, out_len: usize,
tape: *mut [u64; 2], n: *const u8, n_len: usize, e: *const u8, e_len: usize,
msg: *const u8, msg_len: usize, rand: *const u8, rand_len: usize,
scratch: *mut u64, scratch_len: usize, pre: *const u64, pre_len: usize) -> u32`. -/
def encryptRandomSig : Sig where
  params := [("out", .slice true .u8 "out_len"), ("tape", .array true .u64 2),
    ("n", .slice false .u8 "n_len"), ("e", .slice false .u8 "e_len"),
    ("msg", .slice false .u8 "msg_len"), ("rand", .slice false .u8 "rand_len"),
    ("scratch", .slice true .u64 "scratch_len"), ("pre", .slice false .u64 "pre_len")]
  ret := some .u32

/-- RSAES-PKCS1-V1_5-ENCRYPT of the message with the public key `(n, e)` and
the padding string `padSearch` draws from `rand` (`n_len - msg_len - 3`
octets), for a message of at most `n_len - 11` octets and a tape of at most
the budget `padEntropy`: `tape` is the octets consumed and the length of the
next tape (any that `Entropy.Result.Requests` allows, 0 but for status 0);
if no padding string was drawn, the status (0 for more entropy, 3 if
exhausted) and zeros at `out`; otherwise, if `pre` holds the precomputed
values of `n`, `writtenRandom` of the encryption. Constant time but for the
public key, its precomputed values and which octets of the tape were zero
(`padSearch`'s trace). -/
def encryptRandomContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  encryptRandomSig.contract A
    (pre := fun _out outLen _tape _n nLen _e eLen _msg msgLen _rand randLen _scratch scratchLen
        _pre preLen _ =>
      lenValid nLen.toNat ∧ outLen.toNat = nLen.toNat ∧ 1 ≤ eLen.toNat ∧
        eLen.toNat ≤ nLen.toNat ∧ msgLen.toNat + 11 ≤ nLen.toNat ∧
        randLen.toNat ≤ padEntropy (nLen.toNat - msgLen.toNat - 3) ∧
        publicScratchWords nLen.toNat ≤ scratchLen.toNat ∧
        preLen.toNat = Rsa.precomputedWords nLen.toNat)
    (post := fun out _outLen tape n nLen e eLen msg msgLen rand randLen _scratch _scratchLen pre
        preLen m m' r =>
      let psLen := nLen.toNat - msgLen.toNat - 3
      let res := padSearch psLen (bytesAt m rand randLen.toNat)
      (∃ requested, wordsAt m' tape 2 = [BitVec.ofNat 64 res.used, BitVec.ofNat 64 requested] ∧
        res.Requests (padEntropy psLen) requested) ∧
      match res.outcome with
      | .accepted ps =>
        Rsa.publicPrecompute (bytesAt m n nLen.toNat) = some (wordsAt m pre preLen.toNat) →
          writtenRandom m' out nLen.toNat r
            (encrypt (bytesAt m n nLen.toNat) (bytesAt m e eLen.toNat)
              (bytesAt m msg msgLen.toNat) ps)
      | .entropy .. => r = 0 ∧ bytesAt m' out nLen.toNat = List.replicate nLen.toNat 0
      | .exhausted => r = 3 ∧ bytesAt m' out nLen.toNat = List.replicate nLen.toNat 0)
    (writeArgs := true) (stack := stack)
    (leak := some fun _out _outLen _tape n nLen e eLen _msg msgLen rand randLen _scratch
        _scratchLen pre preLen m =>
      (bytesAt m n nLen.toNat ++ bytesAt m e eLen.toNat).map (·.toNat) ++
        (wordsAt m pre preLen.toNat).map (·.toNat) ++
        (padSearch (nLen.toNat - msgLen.toNat - 3) (bytesAt m rand randLen.toNat)).trace)

def encryptRandomApi : Api where
  module := "rsa_pkcs1_enc"
  name := "vg_rsa_pkcs1_encrypt_random"
  sig := encryptRandomSig
  writeArgs := true
  contracts := some fun A stack => encryptRandomContract A stack
  summary := s!"RSAES-PKCS1-v1_5 encryption: RSAES-PKCS1-V1_5-ENCRYPT (RFC 8017 §7.2.1), with \
    the padding string drawn from the random tape `rand` (`rand_len` bytes). With the \
    modulus `n` (`n_len` bytes, most significant first, odd, from 512 to 8192 bits, its \
    first byte not zero), {exponentDoc}, and `pre`, the `pre_len` words \
    `vg_rsa_public_precompute` wrote for `n`, takes as the padding string `PS` the first \
    `n_len - msg_len - 3` nonzero bytes of `rand`, encrypts the encoded message \
    `0x00 ‖ 0x02 ‖ PS ‖ 0x00 ‖ M`, for the message `M` (`msg_len` bytes), with RSAEP, \
    writes the ciphertext (`n_len` bytes, most significant first) to `out` and returns \
    1; or writes zeros and returns 2 if `n` or `e` is not such a number. Writes to \
    `tape[0]` the bytes of `rand` it consumed, up to the last byte of `PS`. If `rand` \
    has fewer nonzero bytes, writes zeros to `out` and: if `rand_len` is the entropy \
    budget, `n_len - msg_len + 125` bytes, returns 3 (which only a broken random number \
    generator makes likely); otherwise consumes none of `rand`, writes to `tape[1]` the \
    length of the next tape, more than `rand_len` and at most the budget, and returns 0: \
    keep `rand`, append fresh random bytes up to that length, and call again. \
    `tape[1]` is 0 but for 0. If `pre` does not hold the values for `n`, what it \
    writes to `out` and returns once it has drawn `PS` is unspecified; memory safety, \
    `tape` and the timing guarantee still apply.\n\n\
    Contract: `VG.Spec.RsaPkcs1Enc.encryptRandomContract`. Constant time but for the \
    public key and the tape's zero bytes: timing may depend on the pointers, the \
    lengths, the contents of `n`, `e` and `pre`, and which bytes of `rand` are zero, not \
    on the message or the other bytes of `rand`."
  safety := ["`n_len` must be in 64..=1024.", "`out_len` must be `n_len`.",
    "`e_len` must be in 1..=`n_len`.", "`msg_len + 11` must be at most `n_len`.",
    "`rand_len` must be at most `n_len - msg_len + 125`.",
    "`pre_len` must be `2 * ⌈n_len / 8⌉`.",
    "For the result to be encryption's, `pre` must hold what \
      `vg_rsa_public_precompute` wrote for `n` (returning 1).",
    "`rand` must hold independent uniform random bytes, fresh for this encryption, \
      extended only as `tape[1]` asks; never reuse them for another encryption."] ++
    publicScratchSafety

end VG.Spec.RsaPkcs1Enc
