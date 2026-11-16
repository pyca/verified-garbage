module

import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallSelected
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejSelected
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Depth
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Main
public import VerifiedGarbage.Impl.MlDsa.AArch64.KeyGen.Prims
public import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Lay
public import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.PrimsOk
public import VerifiedGarbage.Proof.Sha3.AArch64.Variant
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Mul
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.AddSubVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenRoundVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Round.NormLt
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.RejNttCT
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.RejBoundedCT
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.Unpack
import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.HintUnpack
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Ntt
import VerifiedGarbage.Impl.MlDsa.AArch64.Arith.Neon.Ntt
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Basic
import VerifiedGarbage.Proof.MlDsa.AArch64.Round.Arith
import VerifiedGarbage.Proof.MlDsa.AArch64.Round.Basic

/-!
# ML-DSA key generation on AArch64, with this library's primitives

The AArch64 implementations of the primitives (`primsWith`), with any
implementation of the Keccak permutation, are verified with at most 16 bytes
of stack, and their frames use at most that (`prims_okWith`), which key
generation (`KeyGen/OptimizedVerified.lean`), signing and verification
with them take.
-/

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.KeyGen

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen

theorem prims_okWith : PrimsOk (primsWith keccak.callee) 16 where
  s16 := Nat.le_refl _
  sl := by decide
  ntt := by
    have h := Arith.Neon.ntt_verified
    unfold Proof.MlDsa.nttContract Proof.MlDsa.inPlaceContract at h ⊢
    exact CalleeOk.of_verified (by decide) h (by decide) (by dsimp only [primsWith]; decide)
  add := CalleeOk.of_verified (by decide) Optimized.AddSub.add_verified (by decide) (by dsimp only [primsWith]; decide)
  rejNtt := CalleeOk.of_verified (by decide) (Sample.rejNTT_verifiedWith keccak) (by decide) (by simp [primsWith, Sample.rejNTT_depth keccak])
  rej4 := CalleeOk.of_verified (by decide) (Optimized.ResidentRej.selected_verified keccak.callee.pairedSha3) (by decide)
    (by simp only [primsWith,Optimized.ResidentRej.selected_depth,Nat.mul_zero]; decide)
  rejBounded := CalleeOk.of_verified (by decide) (Sample.rejBounded_verifiedWith keccak) (by decide) (by simp [primsWith, Sample.rejBounded_depth keccak])
  ball := CalleeOk.of_verified (by decide) (Optimized.Ball.selected_verified keccak) (by decide) (by simp [primsWith, Optimized.Ball.selected_depth keccak])
  power2Round := CalleeOk.of_verified (by decide) Optimized.KeygenRound.power2Round_verified (by decide) (by dsimp only [primsWith]; decide)
  normLt := CalleeOk.of_verified (by decide) Round.normLt_verified (by decide) (by dsimp only [primsWith]; decide)
  simpleBitPack := CalleeOk.of_verified (by decide) Optimized.KeygenPack.simple_verified (by decide) (by dsimp only [primsWith]; decide)
  bitPack := CalleeOk.of_verified (by decide) Optimized.KeygenPack.signed_verified (by decide) (by dsimp only [primsWith]; decide)
  bitUnpack := CalleeOk.of_verified (by decide) Pack.bitUnpack_verified (by decide) (by dsimp only [primsWith]; decide)
  unpackT1 := CalleeOk.of_verified (by decide) Pack.unpackT1_verified (by decide) (by dsimp only [primsWith]; decide)
  hintUnpack := CalleeOk.of_verified (by decide) Pack.hintBitUnpack_verified (by decide) (by dsimp only [primsWith]; decide)

end VG.Proof.MlDsa.AArch64.KeyGen
