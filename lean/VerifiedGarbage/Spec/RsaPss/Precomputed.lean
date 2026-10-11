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

open Rsa (bytesAt lenValid)
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
        sigLen.toNat = nLen.toNat ∧ scratchWords nLen.toNat ≤ scratchLen.toNat ∧
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

end VG.Spec.RsaPss
