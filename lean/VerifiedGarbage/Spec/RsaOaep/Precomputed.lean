module

public import VerifiedGarbage.Spec.RsaOaep.Contract

/-!
# RSAES-OAEP encryption with a precomputed public key

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

namespace VG.Spec.RsaOaep

open Mgf1 (Hash)
open Rsa (bytesAt lenValid written)
open RsaPss (publicScratchWords)

variable (H G : Hash)

/-- `encryptSig` with a final read-only slice of precomputed `u64` words. -/
def encryptPrecomputedSig : Sig where
  params := [("out", .slice true .u8 "out_len"), ("n", .slice false .u8 "n_len"),
    ("e", .slice false .u8 "e_len"), ("label", .slice false .u8 "label_len"),
    ("msg", .slice false .u8 "msg_len"), ("seed", .array false .u8 H.len),
    ("scratch", .slice true .u64 "scratch_len"), ("pre", .slice false .u64 "pre_len")]
  ret := some .u32

/-- `encryptContract` with precomputed values for the modulus. The result
uses the original encryption specification; the cache only supplies an
alternative representation of the public modulus. Constant time but for the
public key, its precomputed values and the lengths. -/
def encryptPrecomputedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  (encryptPrecomputedSig H).contract A
    (pre := fun _out outLen _n nLen _e eLen _label _labelLen _msg _msgLen _seed _scratch
        scratchLen _pre preLen _ =>
      lenValid nLen.toNat ∧ outLen.toNat = nLen.toNat ∧ 1 ≤ eLen.toNat ∧
        eLen.toNat ≤ nLen.toNat ∧ publicScratchWords nLen.toNat ≤ scratchLen.toNat ∧
        preLen.toNat = Rsa.precomputedWords nLen.toNat)
    (post := fun out _outLen n nLen e eLen label labelLen msg msgLen seed _scratch _scratchLen
        pre preLen m m' r =>
      Rsa.publicPrecompute (bytesAt m n nLen.toNat) = some (Rsa.wordsAt m pre preLen.toNat) →
        written m' out nLen.toNat r
          (encrypt H G (bytesAt m n nLen.toNat) (bytesAt m e eLen.toNat)
            (bytesAt m label labelLen.toNat) (bytesAt m msg msgLen.toNat) (bytesAt m seed H.len)))
    (writeArgs := true) (stack := stack)
    (leak := some fun _out _outLen n nLen e eLen _label _labelLen _msg _msgLen _seed _scratch
        _scratchLen pre preLen m =>
      (bytesAt m n nLen.toNat ++ bytesAt m e eLen.toNat).map (·.toNat) ++
        (Rsa.wordsAt m pre preLen.toNat).map (·.toNat))

/-- Precomputed encryption on every target, with the original timing policy. -/
def encryptPrecomputedApi : Api where
  module := s!"rsa_oaep_{H.rust}_mgf1_{G.rust}"
  name := s!"vg_rsa_oaep_{H.rust}_mgf1_{G.rust}_encrypt_precomputed"
  sig := encryptPrecomputedSig H
  writeArgs := true
  contracts := some fun A stack => encryptPrecomputedContract H G A stack
  summary := (encryptApi H G).summary ++ "\n\n\
    This entry point also takes `pre`, the `pre_len` words written by \
    `vg_rsa_public_precompute` for `n` (returning 1). With those values, it \
    writes and returns exactly what is specified above. If `pre` does not hold \
    those values, what it writes and returns is unspecified; memory safety and \
    the timing guarantee still apply. Timing may additionally depend on the \
    contents of `pre`.\n\n\
    Contract: `VG.Spec.RsaOaep.encryptPrecomputedContract`."
  safety := (encryptApi H G).safety ++
    ["`pre_len` must be `2 * ⌈n_len / 8⌉`.",
      "For the result to be encryption's, `pre` must hold what \
        `vg_rsa_public_precompute` wrote for `n` (returning 1)."]

/-! ## `vg_rsa_oaep_<H>_mgf1_<G>_decrypt_precomputed` -/

/-- `decryptSig` with a final read-only slice of precomputed `u64` words. -/
def decryptPrecomputedSig : Sig where
  params := decryptSig.params ++ [("pre", .slice false .u64 "pre_len")]
  ret := some .u32

/-- `decryptContract` with the precomputed values of the private key
(`Rsa.privatePrecompute`): its outcome when `pre` holds them. -/
def decryptPrecomputedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  decryptPrecomputedSig.contract A
    (pre := fun _out outLen _msgLen _n nLen _e eLen _p pLen _q qLen _dp dpLen _dq dqLen _qinv
        qinvLen _label _labelLen _ct ctLen _scratch scratchLen _pre preLen _ =>
      lenValid nLen.toNat ∧ outLen.toNat = nLen.toNat ∧ ctLen.toNat = nLen.toNat ∧
        1 ≤ eLen.toNat ∧ eLen.toNat ≤ nLen.toNat ∧
        1 ≤ pLen.toNat ∧ pLen.toNat < nLen.toNat ∧ 1 ≤ qLen.toNat ∧ qLen.toNat < nLen.toNat ∧
        dpLen.toNat = pLen.toNat ∧ qinvLen.toNat = pLen.toNat ∧ dqLen.toNat = qLen.toNat ∧
        RsaPss.scratchWords nLen.toNat ≤ scratchLen.toNat ∧
        preLen.toNat = Rsa.privatePrecomputedWords nLen.toNat pLen.toNat qLen.toNat)
    (post := fun out _outLen msgLen n nLen e eLen p pLen q qLen dp _dpLen dq _dqLen qinv
        _qinvLen label labelLen ct _ctLen _scratch _scratchLen pre preLen m m' r =>
      Rsa.privatePreOk m n nLen.toNat p pLen.toNat q qLen.toNat pre preLen.toNat →
        writtenDecrypt m' out msgLen nLen.toNat r
          (decrypt H G (bytesAt m n nLen.toNat) (bytesAt m e eLen.toNat) (bytesAt m p pLen.toNat)
            (bytesAt m q qLen.toNat) (bytesAt m dp pLen.toNat) (bytesAt m dq qLen.toNat)
            (bytesAt m qinv pLen.toNat) (bytesAt m label labelLen.toNat)
            (bytesAt m ct nLen.toNat)))
    (writeArgs := true) (stack := stack)
    (leak := some fun _out _outLen _msgLen n nLen e eLen _p _pLen _q _qLen _dp _dpLen _dq
        _dqLen _qinv _qinvLen _label _labelLen _ct _ctLen _scratch _scratchLen pre _preLen m =>
      (bytesAt m n nLen.toNat ++ bytesAt m e eLen.toNat).map (·.toNat) ++
        Rsa.privatePreLeak m pre nLen.toNat)

/-- `vg_rsa_oaep_<H>_mgf1_<G>_decrypt_precomputed` on every target. -/
def decryptPrecomputedApi : Api where
  module := s!"rsa_oaep_{H.rust}_mgf1_{G.rust}"
  name := s!"vg_rsa_oaep_{H.rust}_mgf1_{G.rust}_decrypt_precomputed"
  sig := decryptPrecomputedSig
  writeArgs := true
  contracts := some fun A stack => decryptPrecomputedContract H G A stack
  summary := (decryptApi H G).summary ++ "\n\n\
    This entry point also takes `pre`, the `pre_len` words `vg_rsa_private_precompute` \
    wrote for `n`, `p` and `q` (returning 1), and calls `vg_rsa_private_checked_precomputed` \
    in place of `vg_rsa_private_checked`. With those values, it returns exactly the result \
    specified above. If `pre` does not hold those values, the result is unspecified; memory \
    safety and the timing guarantee still apply. Timing may additionally depend on the \
    first `2 * ⌈n_len / 8⌉` words of `pre` (the values of `n`), not on the rest.\n\n\
    Contract: `VG.Spec.RsaOaep.decryptPrecomputedContract`."
  safety := (decryptApi H G).safety ++
    ["`pre_len` must be `2 * ⌈n_len / 8⌉ + max(2, ⌈p_len / 8⌉) + max(2, ⌈q_len / 8⌉)`.",
      "For the result to be the one specified above, `pre` must hold what \
        `vg_rsa_private_precompute` wrote for `n`, `p` and `q` (returning 1)."]

end VG.Spec.RsaOaep
