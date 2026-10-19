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
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackVerified
public import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Framework.AArch64.Lit
public import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
public import VerifiedGarbage.Proof.Framework.AArch64.Simd
public import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
public import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Bswap
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Range
public import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Basic
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Butterfly
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackCoefficients
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackEncode
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackLoop
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackVec
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseVec
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackFourBytes
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackFourContracts
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackVec
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackWritten
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Residue
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Vec
public import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.SimpleBitPack
public import VerifiedGarbage.Proof.MlDsa.AArch64.Round.Basic
public import VerifiedGarbage.Proof.MlDsa.Pack.Arith
public import VerifiedGarbage.Proof.MlDsa.Pack.HintMem
public import VerifiedGarbage.Proof.MlDsa.Pack.Stream
public import VerifiedGarbage.Proof.MlKem.AArch64.Reduce
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Basic
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Butterfly
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackCoefficients
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackEncode
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackLoop
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackVec
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseVec
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackFourBytes
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackFourContracts
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackVec
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackWritten
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Residue
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Vec
import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.SimpleBitPack
import VerifiedGarbage.Proof.MlDsa.AArch64.Round.Basic
import VerifiedGarbage.Proof.MlDsa.Pack.Arith
import VerifiedGarbage.Proof.MlDsa.Pack.HintMem
import VerifiedGarbage.Proof.MlDsa.Pack.Stream
import VerifiedGarbage.Proof.MlKem.AArch64.Reduce

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
