module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Hash
public import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Instances
public import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Sha224
public import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Sha256
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.AnyHash
import VerifiedGarbage.Proof.Sha256.Md
import VerifiedGarbage.Proof.Hmac.Generic.Common
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# Deterministic ECDSA on 32-bit ARM: the hash functions

The hash functions the code dispatches on (`hsArm`): SHA-1 and the SHA-2
functions, in `HashId`'s order, each with the functions PBKDF2's code calls
(`Proof.Pbkdf2.Whole.Arm`), and, for a curve, each as the hash function of a
run (`hashOf`), for every number in `hashIds`.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.Arm

open VG VG.Arm VG.Impl.Ecdsa.Rfc6979.Arm
open VG.Proof.Pbkdf2.Whole.Arm (sha1F sha224F sha256F sha384F sha512F sha512_224F sha512_256F sha1OKF
  sha224OKF sha256OKF sha384OKF sha512OKF sha512_224OKF sha512_256OKF)

/-- SHA-1, SHA-224, SHA-256, SHA-384, SHA-512, SHA-512/224 and SHA-512/256. -/
def hsArm : List Impl.Pbkdf2.Whole.Arm.Fns :=
  [sha1F, sha224F, sha256F, sha384F, sha512F, sha512_224F, sha512_256F]

theorem hsArm_nodup : (hsArm.map code).Nodup := by decide

theorem hsArm_codes : ∀ F ∈ hsArm, code F < 256 := by
  simp only [hsArm, List.mem_cons, List.not_mem_nil, or_false]
  rintro F (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> decide

variable (R : RfcCurve)

/-- SHA-1 (1). -/
def sha1R : RfcHash where
  R := R
  hs := hsArm
  nodup := hsArm_nodup
  codes := hsArm_codes
  k := 1
  F := sha1F
  mem := List.mem_cons_self
  ok := sha1OKF
  hash := rfl
  len := ⟨_, rfl, rfl⟩
  blk := rfl
  hk := by decide
  macLen x := by
    show (Spec.Sha1.hash x).length = 20
    simp [Spec.Sha1.hash, Spec.Sha1.wordBytes, List.length_flatMap, List.map_const']
  hDB := .inl ⟨rfl, rfl⟩
  hS := by decide
  hWi := by decide
  hWf := by decide
  hWb := by decide

/-- SHA-224 (2). -/
def sha224R : RfcHash where
  R := R
  hs := hsArm
  nodup := hsArm_nodup
  codes := hsArm_codes
  k := 2
  F := sha224F
  mem := List.mem_cons_of_mem _ List.mem_cons_self
  ok := sha224OKF
  hash := rfl
  len := ⟨_, rfl, rfl⟩
  blk := rfl
  hk := by decide
  macLen x := by
    show (Spec.Sha256.sha224 x).length = 28
    simp [Spec.Sha256.sha224, Spec.Sha256.finalHash, Spec.Sha256.wordBytes,
      List.length_flatMap, List.map_const']
  hDB := .inr (.inl ⟨rfl, rfl⟩)
  hS := by decide
  hWi := by decide
  hWf := by decide
  hWb := by decide

/-- SHA-256 (3). -/
def sha256R : RfcHash where
  R := R
  hs := hsArm
  nodup := hsArm_nodup
  codes := hsArm_codes
  k := 3
  F := sha256F
  mem := List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  ok := sha256OKF
  hash := rfl
  len := ⟨_, rfl, rfl⟩
  blk := rfl
  hk := by decide
  macLen x := by
    show (Spec.Sha256.hash x).length = 32
    rw [Proof.Sha256.hash_eq]; exact Proof.Sha256.md.digest_length _
  hDB := .inr (.inr (.inl ⟨rfl, rfl⟩))
  hS := by decide
  hWi := by decide
  hWf := by decide
  hWb := by decide

/-- SHA-384 (4). -/
def sha384R : RfcHash where
  R := R
  hs := hsArm
  nodup := hsArm_nodup
  codes := hsArm_codes
  k := 4
  F := sha384F
  mem := List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  ok := sha384OKF
  hash := rfl
  len := ⟨_, rfl, rfl⟩
  blk := rfl
  hk := by decide
  macLen x := by
    show ((Spec.Sha512.finalHash Spec.Sha512.H0_384 x).take 48).length = 48
    rw [List.length_take, Proof.Hmac.Generic.Common.finalHash_length]; rfl
  hDB := .inr (.inr (.inr (.inl ⟨rfl, rfl⟩)))
  hS := by decide
  hWi := by decide
  hWf := by decide
  hWb := by decide

/-- SHA-512 (5). -/
def sha512R : RfcHash where
  R := R
  hs := hsArm
  nodup := hsArm_nodup
  codes := hsArm_codes
  k := 5
  F := sha512F
  mem := List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ List.mem_cons_self)))
  ok := sha512OKF
  hash := rfl
  len := ⟨_, rfl, rfl⟩
  blk := rfl
  hk := by decide
  macLen x := by
    show (Spec.Sha512.finalHash Spec.Sha512.H0_512 x).length = 64
    exact Proof.Hmac.Generic.Common.finalHash_length _ _
  hDB := .inr (.inr (.inr (.inr (.inl ⟨rfl, rfl⟩))))
  hS := by decide
  hWi := by decide
  hWf := by decide
  hWb := by decide

/-- SHA-512/224 (6). -/
def sha512_224R : RfcHash where
  R := R
  hs := hsArm
  nodup := hsArm_nodup
  codes := hsArm_codes
  k := 6
  F := sha512_224F
  mem := List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))
  ok := sha512_224OKF
  hash := rfl
  len := ⟨_, rfl, rfl⟩
  blk := rfl
  hk := by decide
  macLen x := by
    show ((Spec.Sha512.finalHash Spec.Sha512.H0_512_224 x).take 28).length = 28
    rw [List.length_take, Proof.Hmac.Generic.Common.finalHash_length]; rfl
  hDB := .inr (.inr (.inr (.inr (.inr (.inl ⟨rfl, rfl⟩)))))
  hS := by decide
  hWi := by decide
  hWf := by decide
  hWb := by decide

/-- SHA-512/256 (7). -/
def sha512_256R : RfcHash where
  R := R
  hs := hsArm
  nodup := hsArm_nodup
  codes := hsArm_codes
  k := 7
  F := sha512_256F
  mem := List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))))
  ok := sha512_256OKF
  hash := rfl
  len := ⟨_, rfl, rfl⟩
  blk := rfl
  hk := by decide
  macLen x := by
    show ((Spec.Sha512.finalHash Spec.Sha512.H0_512_256 x).take 32).length = 32
    rw [List.length_take, Proof.Hmac.Generic.Common.finalHash_length]; rfl
  hDB := .inr (.inr (.inr (.inr (.inr (.inr ⟨rfl, rfl⟩)))))
  hS := by decide
  hWi := by decide
  hWf := by decide
  hWb := by decide

/-- The hash function `k` names, with the curve `R`, for each of `hashIds`. -/
theorem hashOf {k : Nat} (hk : k ∈ Spec.Ecdsa.Rfc6979.hashIds) :
    ∃ P : RfcHash, P.R = R ∧ P.hs = hsArm ∧ P.k = k := by
  simp only [Spec.Ecdsa.Rfc6979.hashIds, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [⟨sha1R R, rfl, rfl, rfl⟩, ⟨sha224R R, rfl, rfl, rfl⟩, ⟨sha256R R, rfl, rfl, rfl⟩,
    ⟨sha384R R, rfl, rfl, rfl⟩, ⟨sha512R R, rfl, rfl, rfl⟩, ⟨sha512_224R R, rfl, rfl, rfl⟩,
    ⟨sha512_256R R, rfl, rfl, rfl⟩]

end VG.Proof.Ecdsa.Rfc6979.Arm
