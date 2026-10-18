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
  summary := encryptApi.summary ++ "\n\n\
    This entry point also takes `pre`, the `pre_len` words written by \
    `vg_rsa_public_precompute` for `n` (returning 1). With those values, it \
    writes and returns exactly what is specified above. If `pre` does not hold \
    those values, what it writes and returns is unspecified; memory safety and \
    the timing guarantee still apply. Timing may additionally depend on the \
    contents of `pre`.\n\n\
    Contract: `VG.Spec.RsaPkcs1Enc.encryptPrecomputedContract`."
  safety := encryptApi.safety ++
    ["`pre_len` must be `2 * ⌈n_len / 8⌉`.",
      "For the result to be encryption's, `pre` must hold what \
        `vg_rsa_public_precompute` wrote for `n` (returning 1)."]

/-! ## `vg_rsa_pkcs1_decrypt_precomputed` -/

/-- `decryptSig` with a final read-only slice of precomputed `u64` words. -/
def decryptPrecomputedSig : Sig where
  params := decryptSig.params ++ [("pre", .slice false .u64 "pre_len")]
  ret := some .u32

/-- `decryptContract` with the precomputed values of the private key
(`Rsa.privatePrecompute`): its outcome when `pre` holds them. -/
def decryptPrecomputedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  decryptPrecomputedSig.contract A
    (pre := fun _out outLen _msgLen _n nLen _e eLen _d dLen _input inputLen _p pLen _q qLen _dp
        dpLen _dq dqLen _qinv qinvLen _scratch scratchLen _pre preLen _ =>
      lenValid nLen.toNat ∧ outLen.toNat = nLen.toNat ∧ inputLen.toNat = nLen.toNat ∧
        1 ≤ eLen.toNat ∧ eLen.toNat ≤ nLen.toNat ∧ 1 ≤ dLen.toNat ∧ dLen.toNat ≤ nLen.toNat ∧
        1 ≤ pLen.toNat ∧ pLen.toNat < nLen.toNat ∧ 1 ≤ qLen.toNat ∧ qLen.toNat < nLen.toNat ∧
        dpLen.toNat = pLen.toNat ∧ qinvLen.toNat = pLen.toNat ∧ dqLen.toNat = qLen.toNat ∧
        Rsa.scratchWords nLen.toNat ≤ scratchLen.toNat ∧
        preLen.toNat = Rsa.privatePrecomputedWords nLen.toNat pLen.toNat qLen.toNat)
    (post := fun out _outLen msgLen n nLen e eLen d dLen input _inputLen p pLen q qLen dp _dpLen
        dq _dqLen qinv _qinvLen _scratch _scratchLen pre preLen m m' r =>
      Rsa.privatePreOk m n nLen.toNat p pLen.toNat q qLen.toNat pre preLen.toNat →
        writtenMsg m' out msgLen nLen.toNat r
          (decrypt (bytesAt m n nLen.toNat) (bytesAt m e eLen.toNat) (bytesAt m d dLen.toNat)
            (bytesAt m p pLen.toNat) (bytesAt m q qLen.toNat) (bytesAt m dp pLen.toNat)
            (bytesAt m dq qLen.toNat) (bytesAt m qinv pLen.toNat) (bytesAt m input nLen.toNat)))
    (writeArgs := true) (stack := stack)
    (leak := some fun _out _outLen _msgLen n nLen e eLen _d _dLen _input _inputLen _p _pLen _q
        _qLen _dp _dpLen _dq _dqLen _qinv _qinvLen _scratch _scratchLen pre _preLen m =>
      (bytesAt m n nLen.toNat ++ bytesAt m e eLen.toNat).map (·.toNat) ++
        Rsa.privatePreLeak m pre nLen.toNat)

def decryptPrecomputedApi : Api where
  module := "rsa_pkcs1_enc"
  name := "vg_rsa_pkcs1_decrypt_precomputed"
  sig := decryptPrecomputedSig
  writeArgs := true
  contracts := some fun A stack => decryptPrecomputedContract A stack
  summary := decryptApi.summary ++ "\n\n\
    This entry point also takes `pre`, the `pre_len` words `vg_rsa_private_precompute` \
    wrote for `n`, `p` and `q` (returning 1), and calls `vg_rsa_private_checked_precomputed` \
    in place of `vg_rsa_private_checked`. With those values, it returns exactly the result \
    specified above. If `pre` does not hold those values, the result is unspecified; memory \
    safety and the timing guarantee still apply. Timing may additionally depend on the \
    first `2 * ⌈n_len / 8⌉` words of `pre` (the values of `n`), not on the rest.\n\n\
    Contract: `VG.Spec.RsaPkcs1Enc.decryptPrecomputedContract`."
  safety := decryptApi.safety ++
    ["`pre_len` must be `2 * ⌈n_len / 8⌉ + max(2, ⌈p_len / 8⌉) + max(2, ⌈q_len / 8⌉)`.",
      "For the result to be the one specified above, `pre` must hold what \
        `vg_rsa_private_precompute` wrote for `n`, `p` and `q` (returning 1)."]

end VG.Spec.RsaPkcs1Enc
