module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Hashes
public import VerifiedGarbage.Spec.Dsa
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.RsaKeyGen.Table

/-! # One hash selection shared by the subgroup and prime searches -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.Proof.Pbkdf2.Md.AArch64

def GenerationHashes.streamOK (H : GenerationHashes) (len : Nat) :
    Calls.StreamOK (if len = 20 then H.sha1 else H.sha256).stream where
  SH := if len = 20 then H.h1.SH else H.h256.SH
  Wb := if len = 20 then H.h1.Wb else H.h256.Wb
  hS := by
    by_cases h : len = 20
    · simpa [h] using H.h1.hS
    · simpa [h] using H.h256.hS
  hD := by
    by_cases h : len = 20
    · simpa [h] using H.h1.hD
    · simpa [h] using H.h256.hD
  hB := by
    by_cases h : len = 20
    · simpa [h] using H.h1.hB
    · simpa [h] using H.h256.hB
  hDF := by
    by_cases h : len = 20
    · simpa [h] using H.h1.hDF
    · simpa [h] using H.h256.hDF
  hF := by
    by_cases h : len = 20
    · simpa [h] using H.h1.hF
    · simpa [h] using H.h256.hF
  hD0 := by
    by_cases h : len = 20
    · simpa [h] using H.h1.hD0
    · simpa [h] using H.h256.hD0
  hS0 := by
    by_cases h : len = 20
    · simpa [h] using H.h1.hS0
    · simpa [h] using H.h256.hS0
  hSB := by
    by_cases h : len = 20
    · simpa [h] using H.h1.hSB
    · simpa [h] using H.h256.hSB
  hB0 := by
    by_cases h : len = 20
    · simpa [h] using H.h1.hB0
    · simpa [h] using H.h256.hB0
  hBB := by
    by_cases h : len = 20
    · simpa [h] using H.h1.hBB
    · simpa [h] using H.h256.hBB
  hWb := by
    by_cases h : len = 20
    · simpa [h] using H.h1.hWb
    · simpa [h] using H.h256.hWb
  hW := by
    by_cases h : len = 20
    · simpa [h] using H.h1.hW
    · simpa [h] using H.h256.hW
  repr := by
    by_cases h : len = 20
    · simpa [h] using H.h1.repr
    · simpa [h] using H.h256.repr
  init := by
    by_cases h : len = 20
    · simpa [h] using H.h1.init
    · simpa [h] using H.h256.init
  upd := by
    by_cases h : len = 20
    · simpa [h] using H.h1.upd
    · simpa [h] using H.h256.upd
  fin := by
    by_cases h : len = 20
    · simpa [h] using H.h1.fin
    · simpa [h] using H.h256.fin
  initDepth := by
    by_cases h : len = 20
    · simpa [h] using H.h1.initDepth
    · simpa [h] using H.h256.initDepth
  updDepth := by
    by_cases h : len = 20
    · simpa [h] using H.h1.updDepth
    · simpa [h] using H.h256.updDepth
  finDepth := by
    by_cases h : len = 20
    · simpa [h] using H.h1.finDepth
    · simpa [h] using H.h256.finDepth

def generationHash (len : Nat) : Spec.Mgf1.Hash :=
  if len = 20 then Spec.Mgf1.sha1 else Spec.Mgf1.sha256

theorem GenerationHashes.hash_matches (H : GenerationHashes) (len : Nat) :
    ∀ x, (generationHash len).hash x = (H.streamOK len).SH.H.hash x := by
  intro x
  by_cases h : len = 20
  · simpa [generationHash, GenerationHashes.streamOK, h] using H.hash1 x
  · simpa [generationHash, GenerationHashes.streamOK, h] using H.hash256 x

theorem GenerationHashes.hash_size (H : GenerationHashes) (len : Nat) :
    ∀ x, ((generationHash len).hash x).length = (if len = 20 then H.sha1 else H.sha256).D := by
  intro x
  unfold generationHash
  split
  · exact H.size1 x
  · exact H.size256 x

theorem GenerationHashes.hash_width (H : GenerationHashes) {len : Nat} (hw : len = 20 ∨ len = 32) :
    (if len = 20 then H.sha1 else H.sha256).D = len := by
  rcases hw with rfl | rfl
  · simpa using H.width1
  · simpa using H.width256

theorem generationHash_seed {len : Nat} (hw : len = 20 ∨ len = 32) (bs : List Byte) :
    (generationHash len).hash bs = Spec.Dsa.seedHash (8 * len) bs := by
  rcases hw with rfl | rfl <;> rfl

theorem GenerationHashes.seed_size (H : GenerationHashes) {len : Nat} (hw : len = 20 ∨ len = 32)
    (bs : List Byte) : 8 * (Spec.Dsa.seedHash (8 * len) bs).length = 8 * len := by
  rw [← generationHash_seed hw, H.hash_size, H.hash_width hw]

end VG.Proof.Dsa.AArch64.Generation
