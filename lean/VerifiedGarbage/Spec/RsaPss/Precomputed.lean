module

public import VerifiedGarbage.Spec.RsaPss.Contract

/-!
# RSASSA-PSS verification with a precomputed public key

**Trusted** (as every file in `Spec/`). These contracts add the modulus'
`Rsa.publicPrecompute` values to verification, so implementations can reuse
key setup and call `vg_rsa_public_precomputed_checked` and its variants.
The accepted signatures are exactly those of `verifyContract` when `pre`
holds the values for `n`. An inconsistent `pre` leaves the result
unspecified, as in `Rsa.publicPrecomputedCheckedContract`; memory safety
and the timing guarantee still apply. Existing contracts are unchanged.
-/

@[expose] public section

namespace VG.Spec.RsaPss

open Rsa (bytesAt lenValid scratchWords writtenOutcome)
open Mgf1 (Hash)

variable (H G : Hash)

/-- `verifySig` with a final read-only slice of precomputed `u64` words. -/
def verifyPrecomputedSig : Sig where
  params := [("n", .slice false .u8 "n_len"), ("e", .slice false .u8 "e_len"),
    ("digest", .array false .u8 H.len), ("sig", .slice false .u8 "sig_len"),
    ("salt_len", .int .usize true), ("any_salt_len", .int .u32 true),
    ("scratch", .slice true .u64 "scratch_len"),
    ("pre", .slice false .u64 "pre_len")]
  ret := some .u32

/-- `verifyContract` with precomputed values for the modulus. The result
uses the original verification specification; the cache only supplies an
alternative representation of the public modulus. -/
def verifyPrecomputedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  (verifyPrecomputedSig H).contract A
    (pre := fun _n nLen _e eLen _digest _sig sigLen _saltLen _anySaltLen _scratch scratchLen _pre preLen _ =>
      lenValid nLen.toNat ∧ 1 ≤ eLen.toNat ∧ eLen.toNat ≤ nLen.toNat ∧
        sigLen.toNat = nLen.toNat ∧ publicScratchWords nLen.toNat ≤ scratchLen.toNat ∧
        preLen.toNat = Rsa.precomputedWords nLen.toNat)
    (post := fun n nLen e eLen digest sig _sigLen saltLen anySaltLen _scratch _scratchLen pre preLen m _m'
        r =>
      Rsa.publicPrecompute (bytesAt m n nLen.toNat) = some (Rsa.wordsAt m pre preLen.toNat) →
        r = if verify H G (bytesAt m n nLen.toNat) (bytesAt m e eLen.toNat) (bytesAt m digest H.len)
          (bytesAt m sig nLen.toNat) (expectedSaltLen saltLen anySaltLen) then 1 else 0)
    (writeArgs := true) (stack := stack)
    (leak := some fun n nLen e eLen _digest _sig _sigLen _saltLen _anySaltLen _scratch
        _scratchLen pre preLen m =>
      (bytesAt m n nLen.toNat ++ bytesAt m e eLen.toNat).map (·.toNat) ++
        (Rsa.wordsAt m pre preLen.toNat).map (·.toNat))

/-- Precomputed verification on every target, with the original timing policy. -/
def verifyPrecomputedApi : Api where
  module := s!"rsa_pss_{H.rust}_mgf1_{G.rust}"
  name := s!"vg_rsa_pss_{H.rust}_mgf1_{G.rust}_verify_precomputed"
  sig := verifyPrecomputedSig H
  writeArgs := true
  contracts := some fun A stack => verifyPrecomputedContract H G A stack
  summary := (verifyApi H G).summary ++ "\n\n\
    This entry point also takes `pre`, the `pre_len` words written by \
    `vg_rsa_public_precompute` for `n` (returning 1). With those values, it \
    returns exactly the result specified above. If `pre` does not hold those \
    values, the result is unspecified; memory safety and the timing guarantee \
    still apply. Timing may additionally depend on the contents of `pre`.\n\n\
    Contract: `VG.Spec.RsaPss.verifyPrecomputedContract`."
  safety := (verifyApi H G).safety ++
    ["`pre_len` must be `2 * ⌈n_len / 8⌉`.",
      "For the result to be signature verification's, `pre` must hold what \
        `vg_rsa_public_precompute` wrote for `n` (returning 1)."]

/-! ## `vg_rsa_pss_<H>_mgf1_<G>_sign_precomputed` -/

/-- `signSig` with a final read-only slice of precomputed `u64` words. -/
def signPrecomputedSig : Sig where
  params := (signSig H).params ++ [("pre", .slice false .u64 "pre_len")]
  ret := some .u32

/-- `signContract` with the precomputed values of the private key
(`Rsa.privatePrecompute`): its outcome when `pre` holds them. -/
def signPrecomputedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  (signPrecomputedSig H).contract A
    (pre := fun _out outLen _n nLen _e eLen _p pLen _q qLen _dp dpLen _dq dqLen _qinv qinvLen
        _digest _salt _saltLen _scratch scratchLen _pre preLen _ =>
      lenValid nLen.toNat ∧ outLen.toNat = nLen.toNat ∧
        1 ≤ eLen.toNat ∧ eLen.toNat ≤ nLen.toNat ∧
        1 ≤ pLen.toNat ∧ pLen.toNat < nLen.toNat ∧ 1 ≤ qLen.toNat ∧ qLen.toNat < nLen.toNat ∧
        dpLen.toNat = pLen.toNat ∧ qinvLen.toNat = pLen.toNat ∧ dqLen.toNat = qLen.toNat ∧
        scratchWords nLen.toNat ≤ scratchLen.toNat ∧
        preLen.toNat = Rsa.privatePrecomputedWords nLen.toNat pLen.toNat qLen.toNat)
    (post := fun out _outLen n nLen e eLen p pLen q qLen dp _dpLen dq _dqLen qinv _qinvLen
        digest salt saltLen _scratch _scratchLen pre preLen m m' r =>
      Rsa.privatePreOk m n nLen.toNat p pLen.toNat q qLen.toNat pre preLen.toNat →
        writtenOutcome m' out nLen.toNat r
          (sign H G (bytesAt m n nLen.toNat) (bytesAt m e eLen.toNat) (bytesAt m p pLen.toNat)
            (bytesAt m q qLen.toNat) (bytesAt m dp pLen.toNat) (bytesAt m dq qLen.toNat)
            (bytesAt m qinv pLen.toNat) (bytesAt m digest H.len) (bytesAt m salt saltLen.toNat)))
    (writeArgs := true) (stack := stack)
    (leak := some fun _out _outLen n nLen e eLen _p _pLen _q _qLen _dp _dpLen _dq _dqLen _qinv
        _qinvLen _digest _salt _saltLen _scratch _scratchLen pre _preLen m =>
      (bytesAt m n nLen.toNat ++ bytesAt m e eLen.toNat).map (·.toNat) ++
        Rsa.privatePreLeak m pre nLen.toNat)

/-- `vg_rsa_pss_<H>_mgf1_<G>_sign_precomputed` on every target. -/
def signPrecomputedApi : Api where
  module := s!"rsa_pss_{H.rust}_mgf1_{G.rust}"
  name := s!"vg_rsa_pss_{H.rust}_mgf1_{G.rust}_sign_precomputed"
  sig := signPrecomputedSig H
  writeArgs := true
  contracts := some fun A stack => signPrecomputedContract H G A stack
  summary := (signApi H G).summary ++ "\n\n\
    This entry point also takes `pre`, the `pre_len` words `vg_rsa_private_precompute` \
    wrote for `n`, `p` and `q` (returning 1), and calls `vg_rsa_private_checked_precomputed` \
    in place of `vg_rsa_private_checked`. With those values, it returns exactly the result \
    specified above. If `pre` does not hold those values, the result is unspecified; memory \
    safety and the timing guarantee still apply. Timing may additionally depend on the \
    first `2 * ⌈n_len / 8⌉` words of `pre` (the values of `n`), not on the rest.\n\n\
    Contract: `VG.Spec.RsaPss.signPrecomputedContract`."
  safety := (signApi H G).safety ++
    ["`pre_len` must be `2 * ⌈n_len / 8⌉ + max(2, ⌈p_len / 8⌉) + max(2, ⌈q_len / 8⌉)`.",
      "For the result to be the one specified above, `pre` must hold what \
        `vg_rsa_private_precompute` wrote for `n`, `p` and `q` (returning 1)."]

end VG.Spec.RsaPss
