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

end VG.Spec.RsaOaep
