module

import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackVerified
public import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.Unpack
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackVerified
public import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.HintUnpack
import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.HighPack
public import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.HintPack
public import VerifiedGarbage.Spec.MlDsa.HighPack

/-! # ML-DSA (FIPS 204) on AArch64: the encodings -/

@[expose] public section

namespace VG.Artifacts.MlDsaPack.AArch64

def artifacts : List Artifact := [
  (Spec.MlDsa.highPackApi 261888).artifact AArch64.target {
    code := Impl.MlDsa.AArch64.Optimized.HighPack.code 261888
    verified := Proof.MlDsa.AArch64.Optimized.HighPack.pack_verified (.inl rfl) },
  (Spec.MlDsa.highPackApi 95232).artifact AArch64.target {
    code := Impl.MlDsa.AArch64.Optimized.HighPack.code 95232
    verified := Proof.MlDsa.AArch64.Optimized.HighPack.pack_verified (.inr rfl) },
  Spec.MlDsa.simpleBitPackApi.artifact AArch64.target {
    code := Impl.MlDsa.AArch64.Optimized.KeygenPack.simple
    verified := Proof.MlDsa.AArch64.Optimized.KeygenPack.simple_verified },
  Spec.MlDsa.bitPackApi.artifact AArch64.target {
    code := Impl.MlDsa.AArch64.Optimized.KeygenPack.signed
    verified := Proof.MlDsa.AArch64.Optimized.KeygenPack.signed_verified },
  Spec.MlDsa.bitUnpackApi.artifact AArch64.target {
    code := Impl.MlDsa.AArch64.Pack.bitUnpack
    verified := Proof.MlDsa.AArch64.Pack.bitUnpack_verified },
  Spec.MlDsa.unpackT1Api.artifact AArch64.target {
    code := Impl.MlDsa.AArch64.Pack.unpackT1
    verified := Proof.MlDsa.AArch64.Pack.unpackT1_verified },
  Spec.MlDsa.hintBitPackApi.artifact AArch64.target {
    code := Impl.MlDsa.AArch64.Pack.hintBitPack
    verified := Proof.MlDsa.AArch64.Pack.hintBitPack_verified },
  Spec.MlDsa.hintBitUnpackApi.artifact AArch64.target {
    code := Impl.MlDsa.AArch64.Pack.hintBitUnpack
    verified := Proof.MlDsa.AArch64.Pack.hintBitUnpack_verified }]

end VG.Artifacts.MlDsaPack.AArch64
