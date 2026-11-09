module

public import VerifiedGarbage.Spec.RsaPkcs1Enc.Contract

/-!
# RSAES-PKCS1-v1_5 encryption: the contract of its internal function

Not trusted: the contract of `vg_rsa_pkcs1_encrypt_precomputed`, an internal
function that only verified code calls (`vg_rsa_pkcs1_encrypt_random`, whose
contract, `Spec.RsaPkcs1Enc.encryptRandomContract`, is the trusted one), and
that the proofs of its callers compose.

`vg_rsa_pkcs1_encrypt_precomputed`: RSAES-PKCS1-V1_5-ENCRYPT
(`Spec.RsaPkcs1Enc.encrypt`) with the padding string given by the caller,
and the modulus also given by the values `vg_rsa_public_precompute` computed
(`Rsa.publicPrecompute`), so that it can call
`vg_rsa_public_precomputed_checked`. The ciphertext and result are
encryption's when `pre` holds the values for `n`; otherwise they are
unspecified, but memory safety and the timing guarantee still hold. The
arguments are as in `Spec/RsaPkcs1Enc/Contract.lean`.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc

open VG.Spec.RsaPkcs1Enc
open VG.Spec.Rsa (bytesAt lenValid publicScratchWords written)

/-- `vg_rsa_pkcs1_encrypt_precomputed(out: *mut u8, out_len: usize,
n: *const u8, n_len: usize, e: *const u8, e_len: usize, msg: *const u8,
msg_len: usize, ps: *const u8, ps_len: usize, scratch: *mut u64,
scratch_len: usize, pre: *const u64, pre_len: usize) -> u32`. -/
def encryptPrecomputedSig : Sig where
  params := [("out", .slice true .u8 "out_len"), ("n", .slice false .u8 "n_len"),
    ("e", .slice false .u8 "e_len"), ("msg", .slice false .u8 "msg_len"),
    ("ps", .slice false .u8 "ps_len"), ("scratch", .slice true .u64 "scratch_len"),
    ("pre", .slice false .u64 "pre_len")]
  ret := some .u32

/-- RSAES-PKCS1-V1_5-ENCRYPT of the message with the public key `(n, e)` and
the padding string `ps` (`encrypt`), for a message of at most `n_len - 11`
octets and a padding string of `n_len - msg_len - 3`, if `pre` holds the
precomputed values of `n`. Constant time but for the public key and its
precomputed values. -/
def encryptPrecomputedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  encryptPrecomputedSig.contract A
    (pre := fun _out outLen _n nLen _e eLen _msg msgLen _ps psLen _scratch scratchLen _pre preLen _ =>
      lenValid nLen.toNat ∧ outLen.toNat = nLen.toNat ∧ 1 ≤ eLen.toNat ∧
        eLen.toNat ≤ nLen.toNat ∧ msgLen.toNat + 11 ≤ nLen.toNat ∧
        psLen.toNat = nLen.toNat - msgLen.toNat - 3 ∧ publicScratchWords nLen.toNat ≤ scratchLen.toNat ∧
        preLen.toNat = Spec.Rsa.precomputedWords nLen.toNat)
    (post := fun out _outLen n nLen e eLen msg msgLen ps psLen _scratch _scratchLen pre preLen m m' r =>
      Spec.Rsa.publicPrecompute (bytesAt m n nLen.toNat) = some (Spec.Rsa.wordsAt m pre preLen.toNat) →
        written m' out nLen.toNat r
          (encrypt (bytesAt m n nLen.toNat) (bytesAt m e eLen.toNat) (bytesAt m msg msgLen.toNat)
            (bytesAt m ps psLen.toNat)))
    (writeArgs := true) (stack := stack)
    (leak := some fun _out _outLen n nLen e eLen _msg _msgLen _ps _psLen _scratch _scratchLen pre preLen
        m =>
      (bytesAt m n nLen.toNat ++ bytesAt m e eLen.toNat).map (·.toNat) ++
        (Spec.Rsa.wordsAt m pre preLen.toNat).map (·.toNat))

end VG.Proof.RsaPkcs1Enc
