module

public import VerifiedGarbage.Impl.Dsa.RISCV64.Fn
public import VerifiedGarbage.Proof.Dsa.RISCV64.DeriveVerified
public import VerifiedGarbage.Proof.Dsa.RISCV64.RSVerified
public import VerifiedGarbage.Proof.Dsa.RISCV64.ValidatePrivateVerified
public import VerifiedGarbage.Proof.Dsa.RISCV64.GKVerified
public import VerifiedGarbage.Proof.Dsa.RISCV64.ValidateVerified
public import VerifiedGarbage.Proof.Dsa.RISCV64.PrevalidatedVerified
public import VerifiedGarbage.Proof.Dsa.RISCV64.ParameterSearchInit
public import VerifiedGarbage.Proof.Dsa.RISCV64.PSearch.Instances
public import VerifiedGarbage.Proof.Variants.MillerRabin.RISCV64
public import VerifiedGarbage.Proof.Dsa.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubProved
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubCall

/-!
# DSA on RISC-V, as emitted

Key derivation and generation, the validation of keys, signing and
verification, and the parameter search's start, with their cleanup
(`Impl.Dsa.RISCV64.Fn`): each meets its contract in constant time and
returns without secret residue (`VerifiedScrubbed`, by
`RISCV64.Scrub.verifiedScrubbed`), which is what its registration binds. What
the cleanup needs of each function's code (`Scrub.scrubSide`) is evaluated
here, by the kernel.

The parameter search, `vg_dsa_parameter_search`, is generic over the
Miller-Rabin round (`Proof.Variants.MillerRabin.RISCV64`): as emitted
(`Impl.Dsa.RISCV64.Fn.parameterSearch`), for every round, it meets its
contract and returns without secret residue (`parameterSearch`). What its
cleanup needs of its code (`Scrub.scrubSide`) is evaluated once, with a stub
of 96 bytes of stack in the place of the round (`parameterSearch_stub_side`);
the code with a round is that code filled (`Scrub.Fill`), from what each round
proves of its own code where it is defined (`RoundImpl.stack`,
`RoundImpl.icalls`).
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64.Fn

open VG.RISCV64 VG.RISCV64.Scrub VG.Proof.Dsa.RISCV64.Scrub
open VG.Proof.MillerRabin.RISCV64 (RoundImpl)

theorem deriveKey :
    VerifiedScrubbed target Impl.Dsa.RISCV64.Fn.deriveKey (Spec.Dsa.deriveKeyContract abi) 32 :=
  verifiedScrubbed (api := Spec.Dsa.deriveKeyApi) (W := 0)
    { code := Impl.Dsa.RISCV64.Derive.derive, verified := deriveKey_verified }
    (deriveKeyOut _ []) (by lit_decide)

theorem validatePrivateKey :
    VerifiedScrubbed target Impl.Dsa.RISCV64.Fn.validatePrivateKey
      (Spec.Dsa.validatePrivateKeyContract abi) 32 :=
  verifiedScrubbed (api := Spec.Dsa.validatePrivateKeyApi) (W := 0)
    { code := Impl.Dsa.RISCV64.PrevalidatedSign.validate, verified := validatePrivate_verified }
    (validatePrivateKeyOut _ []) (by lit_decide)

theorem randomSignPrevalidated :
    VerifiedScrubbed target Impl.Dsa.RISCV64.Fn.randomSignPrevalidated
      (Spec.Dsa.randomSignPrevalidatedContract abi 192) 32 :=
  verifiedScrubbed (api := Spec.Dsa.randomSignPrevalidatedApi) (W := 192)
    { code := Impl.Dsa.RISCV64.PrevalidatedSign.randomSign, verified := randomSignPre_verified }
    (randomSignPrevalidatedOut _ []) (by lit_decide)

theorem generateKey :
    VerifiedScrubbed target Impl.Dsa.RISCV64.Fn.generateKey (Spec.Dsa.generateKeyContract abi 192) 32 :=
  verifiedScrubbed (api := Spec.Dsa.generateKeyApi) (W := 192)
    { code := Impl.Dsa.RISCV64.Generate.code, verified := generateKey_verified }
    (generateKeyOut _ []) (by lit_decide)

theorem validatePublicKey :
    VerifiedScrubbed target Impl.Dsa.RISCV64.Fn.validatePublicKey
      (Spec.Dsa.validatePublicKeyContract abi) 32 :=
  verifiedScrubbed (api := Spec.Dsa.validatePublicKeyApi) (W := 0)
    { code := Impl.Dsa.RISCV64.Prevalidated.validate, verified := validate_verified }
    (validatePublicKeyOut _ []) (by lit_decide)

theorem verifyPrevalidated :
    VerifiedScrubbed target Impl.Dsa.RISCV64.Fn.verifyPrevalidated
      (Spec.Dsa.verifyPrevalidatedContract abi) 32 :=
  verifiedScrubbed (api := Spec.Dsa.verifyPrevalidatedApi) (W := 0)
    { code := Impl.Dsa.RISCV64.Prevalidated.verify, verified := prevalidated_verified }
    (verifyPrevalidatedOut _ []) (by lit_decide)

theorem parameterInit :
    VerifiedScrubbed target Impl.Dsa.RISCV64.Fn.parameterInit (Spec.Dsa.parameterInitContract abi) 32 :=
  verifiedScrubbed (api := Spec.Dsa.parameterInitApi) (W := 0)
    { code := Impl.Dsa.RISCV64.ParameterSearch.init, verified := init_verified }
    (parameterInitOut []) (by lit_decide)

/-- What the cleanup needs of the parameter search, with a stub of 96 bytes
of stack in the place of the round. -/
theorem parameterSearch_stub_side :
    scrubSide (Impl.Dsa.RISCV64.Fn.parameterSearchBody "" (holeStub 96)) 512 32 [] = true := by
  lit_decide

open Impl.Dsa.RISCV64.ParameterSearch (Geo) in
/-- A width's hashes of `X`, which do not call the tests. -/
theorem pHashes_fill (g : Geo) (qn pn : String) (qc pc : Prog isa) :
    ∀ m, Fill 0 [] (g.pHashes m) ({ g with qName := qn, qCode := qc, pName := pn, pCode := pc }.pHashes m)
  | 0 => .refl _
  | m + 1 => .seq (pHashes_fill g qn pn qc pc m) (by fill_calls)

open Impl.Dsa.RISCV64.ParameterSearch (Geo) in
/-- A width of the search, with its probable-prime tests filled: whatever
the width, so that the code it shares (its hash function's) is one term. -/
theorem generate_fill (g : Geo) {qn pn : String} {qc pc : Prog isa} (hq : Fill 0 [] g.qCode qc)
    (hp : Fill 0 [] g.pCode pc) :
    Fill 0 [] g.generate { g with qName := qn, qCode := qc, pName := pn, pCode := pc }.generate := by
  fill_calls
  all_goals exact pHashes_fill g qn pn qc pc _

/-- A probable-prime test with the round `round` is its code with the stub,
filled. -/
theorem prime_fill {round : Prog isa} (bits : Nat) (suffix : String) (h : calleeSide round 96 = true) :
    Fill 0 [] (Impl.Dsa.RISCV64.ProbablePrime.code bits "vg_miller_rabin_round" (holeStub 96))
      (Impl.Dsa.RISCV64.ProbablePrime.code bits ("vg_miller_rabin_round" ++ suffix) round) := by
  fill_calls

/-- The parameter search with the round `round` is its code with the stub,
filled. -/
theorem parameterSearch_fill {round : Prog isa} (suffix : String) (h : calleeSide round 96 = true) :
    Fill 0 [] (Impl.Dsa.RISCV64.Fn.parameterSearchBody "" (holeStub 96))
      (Impl.Dsa.RISCV64.Fn.parameterSearchBody suffix round) := by
  have h1 := generate_fill (Impl.Dsa.RISCV64.Fn.geo 128 20 Impl.Dsa.RISCV64.ParameterSearch.sha1 "" (holeStub 96))
    (qn := s!"vg_dsa_probable_prime_{8 * 20}" ++ suffix) (pn := s!"vg_dsa_probable_prime_{8 * 128}" ++ suffix)
    (prime_fill _ suffix h) (prime_fill _ suffix h)
  have h2 := generate_fill (Impl.Dsa.RISCV64.Fn.geo 256 32 Impl.Dsa.RISCV64.ParameterSearch.sha256 "" (holeStub 96))
    (qn := s!"vg_dsa_probable_prime_{8 * 32}" ++ suffix) (pn := s!"vg_dsa_probable_prime_{8 * 256}" ++ suffix)
    (prime_fill _ suffix h) (prime_fill _ suffix h)
  have h3 := generate_fill (Impl.Dsa.RISCV64.Fn.geo 384 32 Impl.Dsa.RISCV64.ParameterSearch.sha256 "" (holeStub 96))
    (qn := s!"vg_dsa_probable_prime_{8 * 32}" ++ suffix) (pn := s!"vg_dsa_probable_prime_{8 * 384}" ++ suffix)
    (prime_fill _ suffix h) (prime_fill _ suffix h)
  exact .seq (.refl _) (.seq (.seq (.refl _) (.seq (.refl _) (.ite _ h1 (.seq (.refl _) (.ite _ h2 h3)))))
    (.refl _))

/-- `vg_dsa_parameter_search` as emitted, with the Miller-Rabin round `v`: it
meets its contract in constant time and returns without secret residue. -/
theorem parameterSearch (v : RoundImpl) :
    VerifiedScrubbed target (Impl.Dsa.RISCV64.Fn.parameterSearch v.suffix v.code)
      (Spec.Dsa.parameterSearchContract (abi.withConsts PSearch.kT) 512) 32 :=
  verifiedScrubbed (api := Spec.Dsa.parameterSearchApi)
    { suffix := v.suffix
      code := Impl.Dsa.RISCV64.Fn.parameterSearchBody v.suffix v.code
      verified := PSearch.params_verified v }
    (parameterSearchOut 512 PSearch.kT)
    (scrubSide_of_fill (parameterSearch_fill v.suffix (calleeSide_of (depth_le_of_sdepth v.stack) v.icalls))
      parameterSearch_stub_side (fun _ h => h) (fun _ h => absurd h List.not_mem_nil))

end VG.Proof.Dsa.RISCV64.Fn
