module

public import VerifiedGarbage.Proof.X25519.X86_64.Divstep.Sound
public import VerifiedGarbage.Proof.Ed25519.X86_64.PublicKey.Expanded
import VerifiedGarbage.Proof.Ed25519.X86_64.Ifma.ScalarBase
import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarBaseAdx
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity.Finset
import VerifiedGarbage.Proof.Ed25519.X86_64.CombLit
import VerifiedGarbage.Proof.Ed25519.X86_64.Ifma.CombLit
public import VerifiedGarbage.Proof.Framework.Registration
public import Init.Data.String.Defs
public import VerifiedGarbage.Impl.Ed25519.X86_64.ScalarBasePrecomputed
public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.Framework.TaintSum

/-! Ed25519 public-key derivation from the seed's SHA-512 digest, for each base-point
multiplication: the baseline's, BMI2's and ADX's (`_adx`), and AVX512_IFMA's (`_ifma`). -/

@[expose] public section

namespace VG.Artifacts.Ed25519PublicKeyExpanded.X86_64

def notes (fs : String) : List String := ["Copies the seed's SHA-512 digest to `scratch + 1568` \
  and encodes `[s]B` with `vg_ed25519_scalar_base" ++ fs ++ "`, as `vg_ed25519_public_key" ++ fs ++
  "` does after hashing the seed. The pruned scalar `s` is kept in a 56-byte stack frame with the \
  pointers and cleared before the frame is popped; the calls use the 16 bytes below it."]

def artifacts : List Artifact := [
  Spec.Ed25519.publicKeyExpandedApi.artifact X86_64.target {
    notes := notes ""
    consts := Impl.Ed25519.X86_64.combConsts
    code := Impl.Ed25519.X86_64.publicKeyExpanded
      (Impl.Ed25519.X86_64.scalarBase_precomputed Impl.X25519.X86_64.baseline) ""
    stack := 72
    verified := Proof.Ed25519.X86_64.PublicKey.publicKeyExpanded_verified
    spSafe := Proof.Ed25519.X86_64.PublicKey.publicKeyExpanded_spSafe },
  Spec.Ed25519.publicKeyExpandedApi.artifact X86_64.target {
    suffix := "_adx"
    notes := notes "_adx"
    consts := Impl.Ed25519.X86_64.combConsts
    code := Impl.Ed25519.X86_64.publicKeyExpanded Impl.Ed25519.X86_64.scalarBase_adx "_adx"
    stack := 72
    verified := Proof.Ed25519.X86_64.PublicKey.publicKeyExpanded_verified
    spSafe := Proof.Ed25519.X86_64.PublicKey.publicKeyExpanded_spSafe
    features := ["avx", "avx2", "bmi2", "adx"] },
  Spec.Ed25519.publicKeyExpandedApi.artifact X86_64.target {
    suffix := "_ifma"
    notes := notes "_ifma"
    consts := Impl.Ed25519.X86_64.combConsts
    code := Impl.Ed25519.X86_64.publicKeyExpanded Impl.Ed25519.X86_64.scalarBase_ifma "_ifma"
    stack := 72
    verified := Proof.Ed25519.X86_64.PublicKey.publicKeyExpanded_verified
    spSafe := Proof.Ed25519.X86_64.PublicKey.publicKeyExpanded_spSafe
    features := ["avx", "avx2", "bmi2", "adx", "avx512f", "avx512ifma", "avx512vl"] }]

end VG.Artifacts.Ed25519PublicKeyExpanded.X86_64
