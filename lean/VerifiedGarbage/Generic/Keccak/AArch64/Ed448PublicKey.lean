module

public import VerifiedGarbage.Proof.Ed448.AArch64.PublicKey.Verified
public import VerifiedGarbage.Proof.Ed448.AArch64.BaseVerified
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity.Finset
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# Ed448 public-key derivation on AArch64

A generic file (see `TCB/Emit.lean`): `vg_ed448_public_key` calls the SHA-3
sponge functions with an implementation `v` of the Keccak permutation
(`Variants/Keccak/AArch64/`), so it is emitted once for each implementation,
named with its suffix, and needs its CPU features. The signature and
documentation come from the reviewed Ed448 API. The correctness of
`vg_ed448_scalar_base` (`Proof/Ed448/AArch64/BaseVerified.lean`) is passed to
the proof here, so that only registration and generic files import its algebra.
-/

@[expose] public section

namespace VG.Generic.Keccak.AArch64.Ed448PublicKey

def artifacts (v : Proof.Sha3.AArch64.Permutation) : List Artifact := [
  Spec.Ed448.publicKeyApi.artifact AArch64.target {
    suffix := v.callee.suffix
    features := v.features
    notes := ["Uses baseline integer instructions, and \
      those of the Keccak permutation it calls. Hashes the private key with \
      `vg_keccak_absorb_scratch`, `vg_keccak_pad_scratch` and `vg_keccak_squeeze_scratch` \
      (SHAKE256, into its stack frame, with the Keccak state in `scratch`), prunes the first 57 \
      bytes of the hash into the frame, encodes `[s]B` \
      with `vg_ed448_scalar_base`, and clears the frame's scalar and hash. The base-point \
      multiplication's working values are left in `scratch`. The function saves `x30` and its \
      arguments on the stack, and the functions it calls use 16 bytes below its frame."]
    consts := Impl.X448.AArch64.Base.combConsts
    code := Impl.Ed448.AArch64.PublicKey.publicKeyWith v.callee
    stack := 352
    verified := Proof.Ed448.AArch64.PublicKey.publicKey_verified v Proof.Ed448.AArch64.scalarBase_baseOk }]

end VG.Generic.Keccak.AArch64.Ed448PublicKey
