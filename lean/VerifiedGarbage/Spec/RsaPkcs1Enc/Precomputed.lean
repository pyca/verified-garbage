module

public import VerifiedGarbage.Spec.RsaPkcs1Enc.Contract

/-!
# RSAES-PKCS1-v1_5 encryption with a precomputed public key

**Trusted** (as every file in `Spec/`). This contract adds the modulus'
`Rsa.publicPrecompute` values to encryption, so implementations can reuse
key setup and call `vg_rsa_public_precomputed_checked` and its variants.
The ciphertext and result are exactly those of `encryptContract` when `pre`
holds the values for `n`. An inconsistent `pre` leaves the ciphertext and
result unspecified, as in `Rsa.publicPrecomputedCheckedContract`; memory
safety and the timing guarantee still apply. Existing contracts are
unchanged.
-/

@[expose] public section

namespace VG.Spec.RsaPkcs1Enc

open Rsa (bytesAt lenValid publicScratchWords written)

/-- `encryptSig` with a final read-only slice of precomputed `u64` words. -/
def encryptPrecomputedSig : Sig where
  params := [("out", .slice true .u8 "out_len"), ("n", .slice false .u8 "n_len"),
    ("e", .slice false .u8 "e_len"), ("msg", .slice false .u8 "msg_len"),
    ("ps", .slice false .u8 "ps_len"), ("scratch", .slice true .u64 "scratch_len"),
    ("pre", .slice false .u64 "pre_len")]
  ret := some .u32

/-- `encryptContract` with precomputed values for the modulus. The result
uses the original encryption specification; the cache only supplies an
alternative representation of the public modulus. Constant time but for the
public key and its precomputed values. -/
def encryptPrecomputedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  encryptPrecomputedSig.contract A
    (pre := fun _out outLen _n nLen _e eLen _msg msgLen _ps psLen _scratch scratchLen _pre preLen _ =>
      lenValid nLen.toNat ∧ outLen.toNat = nLen.toNat ∧ 1 ≤ eLen.toNat ∧
        eLen.toNat ≤ nLen.toNat ∧ msgLen.toNat + 11 ≤ nLen.toNat ∧
        psLen.toNat = nLen.toNat - msgLen.toNat - 3 ∧ publicScratchWords nLen.toNat ≤ scratchLen.toNat ∧
        preLen.toNat = Rsa.precomputedWords nLen.toNat)
    (post := fun out _outLen n nLen e eLen msg msgLen ps psLen _scratch _scratchLen pre preLen m m' r =>
      Rsa.publicPrecompute (bytesAt m n nLen.toNat) = some (Rsa.wordsAt m pre preLen.toNat) →
        written m' out nLen.toNat r
          (encrypt (bytesAt m n nLen.toNat) (bytesAt m e eLen.toNat) (bytesAt m msg msgLen.toNat)
            (bytesAt m ps psLen.toNat)))
    (writeArgs := true) (stack := stack)
    (leak := some fun _out _outLen n nLen e eLen _msg _msgLen _ps _psLen _scratch _scratchLen pre preLen
        m =>
      (bytesAt m n nLen.toNat ++ bytesAt m e eLen.toNat).map (·.toNat) ++
        (Rsa.wordsAt m pre preLen.toNat).map (·.toNat))

/-- Precomputed encryption on every target, with the original timing policy. -/
def encryptPrecomputedApi : Api where
  module := "rsa_pkcs1_enc"
  name := "vg_rsa_pkcs1_encrypt_precomputed"
  sig := encryptPrecomputedSig
  writeArgs := true
  contracts := some fun A stack => encryptPrecomputedContract A stack
  summary := encryptSummary ++ "\n\n\
    This entry point also takes `pre`, the `pre_len` words written by \
    `vg_rsa_public_precompute` for `n` (returning 1). With those values, it \
    writes and returns exactly what is specified above. If `pre` does not hold \
    those values, what it writes and returns is unspecified; memory safety and \
    the timing guarantee still apply. Timing may additionally depend on the \
    contents of `pre`.\n\n\
    Contract: `VG.Spec.RsaPkcs1Enc.encryptPrecomputedContract`."
  safety := encryptSafety ++
    ["`pre_len` must be `2 * ⌈n_len / 8⌉`.",
      "For the result to be encryption's, `pre` must hold what \
        `vg_rsa_public_precompute` wrote for `n` (returning 1)."]

end VG.Spec.RsaPkcs1Enc
