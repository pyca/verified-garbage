module

public import VerifiedGarbage.Spec.RsaPkcs1Sig.Contract

/-!
# RSASSA-PKCS1-v1_5 verification and recovery with a precomputed public key

**Trusted** (as every file in `Spec/`). These contracts add the modulus'
`Rsa.publicPrecompute` values to verification and recovery, so
implementations can reuse key setup and call
`vg_rsa_public_precomputed_checked` and its variants. The accepted
signatures are exactly those of `verifyContract`, and the recovered values
those of `recoverContract`, when `pre` holds the values for `n`. An inconsistent `pre` leaves the result
unspecified, as in `Rsa.publicPrecomputedCheckedContract`; memory safety
and the timing guarantee still apply. Existing contracts are unchanged.
-/

@[expose] public section

namespace VG.Spec.RsaPkcs1Sig

open Rsa (bytesAt lenValid publicScratchWords)

/-- `verifySig` with a final read-only slice of precomputed `u64` words. -/
def verifyPrecomputedSig : Sig where
  params := [("n", .slice false .u8 "n_len"), ("e", .slice false .u8 "e_len"),
    ("hash", .int .u32 true), ("digest", .slice false .u8 "digest_len"),
    ("sig", .slice false .u8 "sig_len"), ("scratch", .slice true .u64 "scratch_len"),
    ("pre", .slice false .u64 "pre_len")]
  ret := some .u32

/-- `verifyContract` with precomputed values for the modulus. The result
uses the original verification specification; the cache only supplies an
alternative representation of the public modulus. -/
def verifyPrecomputedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  verifyPrecomputedSig.contract A
    (pre := fun _n nLen _e eLen _hash _digest _digestLen _sig _sigLen _scratch scratchLen _pre preLen _ =>
      lenValid nLen.toNat ∧ 1 ≤ eLen.toNat ∧ eLen.toNat ≤ nLen.toNat ∧
        publicScratchWords nLen.toNat ≤ scratchLen.toNat ∧
        preLen.toNat = Rsa.precomputedWords nLen.toNat)
    (post := fun n nLen e eLen hash digest digestLen sig sigLen _scratch _scratchLen pre preLen m _m' r =>
      Rsa.publicPrecompute (bytesAt m n nLen.toNat) = some (Rsa.wordsAt m pre preLen.toNat) →
        r = if verifyId (bytesAt m n nLen.toNat) (bytesAt m e eLen.toNat) hash.toNat
          (bytesAt m digest digestLen.toNat) (bytesAt m sig sigLen.toNat) then 1 else 0)
    (writeArgs := true) (stack := stack)
    (leak := some fun n nLen e eLen _hash digest digestLen sig sigLen _scratch _scratchLen pre preLen m =>
      (bytesAt m n nLen.toNat ++ bytesAt m e eLen.toNat ++ bytesAt m digest digestLen.toNat ++
        bytesAt m sig sigLen.toNat).map (·.toNat) ++ (Rsa.wordsAt m pre preLen.toNat).map (·.toNat))

/-- Precomputed verification on every target, with the original timing policy. -/
def verifyPrecomputedApi : Api where
  module := "rsa_pkcs1_sig"
  name := "vg_rsa_pkcs1_verify_precomputed"
  sig := verifyPrecomputedSig
  writeArgs := true
  contracts := some fun A stack => verifyPrecomputedContract A stack
  summary := verifyApi.summary ++ "\n\n\
    This entry point also takes `pre`, the `pre_len` words written by \
    `vg_rsa_public_precompute` for `n` (returning 1). With those values, it \
    returns exactly the result specified above. If `pre` does not hold those \
    values, the result is unspecified; memory safety and the timing guarantee \
    still apply. Timing may additionally depend on the contents of `pre`.\n\n\
    Contract: `VG.Spec.RsaPkcs1Sig.verifyPrecomputedContract`."
  safety := verifyApi.safety ++
    ["`pre_len` must be `2 * ⌈n_len / 8⌉`.",
      "For the result to be signature verification's, `pre` must hold what \
        `vg_rsa_public_precompute` wrote for `n` (returning 1)."]

/-! ## `vg_rsa_pkcs1_recover_precomputed` -/

/-- `recoverSig` with a final read-only slice of precomputed `u64` words. -/
def recoverPrecomputedSig : Sig where
  params := [("out", .slice true .u8 "out_len"), ("n", .slice false .u8 "n_len"),
    ("e", .slice false .u8 "e_len"), ("hash", .int .u32 true),
    ("sig", .slice false .u8 "sig_len"), ("scratch", .slice true .u64 "scratch_len"),
    ("pre", .slice false .u64 "pre_len")]
  ret := some .u32

/-- `recoverContract` with precomputed values for the modulus. The result
uses the original recovery specification; the cache only supplies an
alternative representation of the public modulus. Not constant time:
everything it reads is public. -/
def recoverPrecomputedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  recoverPrecomputedSig.contract A
    (pre := fun _out outLen _n nLen _e eLen hash _sig _sigLen _scratch scratchLen _pre preLen _ =>
      lenValid nLen.toNat ∧ 1 ≤ eLen.toNat ∧ eLen.toNat ≤ nLen.toNat ∧
        (∃ h, Hash.ofId hash.toNat = some h ∧ outLen.toNat = h.len) ∧
        publicScratchWords nLen.toNat ≤ scratchLen.toNat ∧
        preLen.toNat = Rsa.precomputedWords nLen.toNat)
    (post := fun out outLen n nLen e eLen hash sig sigLen _scratch _scratchLen pre preLen m m' r =>
      Rsa.publicPrecompute (bytesAt m n nLen.toNat) = some (Rsa.wordsAt m pre preLen.toNat) →
        ∀ h, Hash.ofId hash.toNat = some h →
          Rsa.written m' out outLen.toNat r
            (recover (bytesAt m n nLen.toNat) (bytesAt m e eLen.toNat) h
              (bytesAt m sig sigLen.toNat)))
    (writeArgs := true) (stack := stack)
    (leak := some fun _out _outLen n nLen e eLen _hash sig sigLen _scratch _scratchLen pre preLen m =>
      (bytesAt m n nLen.toNat ++ bytesAt m e eLen.toNat ++ bytesAt m sig sigLen.toNat).map
        (·.toNat) ++ (Rsa.wordsAt m pre preLen.toNat).map (·.toNat))

/-- Precomputed recovery on every target, with the original timing policy. -/
def recoverPrecomputedApi : Api where
  module := "rsa_pkcs1_sig"
  name := "vg_rsa_pkcs1_recover_precomputed"
  sig := recoverPrecomputedSig
  writeArgs := true
  contracts := some fun A stack => recoverPrecomputedContract A stack
  summary := recoverApi.summary ++ "\n\n\
    This entry point also takes `pre`, the `pre_len` words written by \
    `vg_rsa_public_precompute` for `n` (returning 1). With those values, it \
    writes and returns exactly what is specified above. If `pre` does not hold \
    those values, what it writes and returns is unspecified; memory safety \
    still applies.\n\n\
    Contract: `VG.Spec.RsaPkcs1Sig.recoverPrecomputedContract`."
  safety := recoverApi.safety ++
    ["`pre_len` must be `2 * ⌈n_len / 8⌉`.",
      "For the result to be recovery's, `pre` must hold what \
        `vg_rsa_public_precompute` wrote for `n` (returning 1)."]

end VG.Spec.RsaPkcs1Sig
