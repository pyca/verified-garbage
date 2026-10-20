module
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeState
public import VerifiedGarbage.Proof.Dsa.AArch64.Run
public import VerifiedGarbage.Proof.RsaOaep.AArch64.Label
public import VerifiedGarbage.Spec.Dsa
public import VerifiedGarbage.Impl.Dsa.Generation.Layout

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.Generation.QCandidate
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.Arithmetic

/-! # State connecting subgroup hashing to the complete native primality call -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.RsaOaep.AArch64 VG.Proof.RsaOaep.AArch64

structure SubgroupPlan where
  prime : PrimeParams
  F : Addr
  hash : Addr
  seedPtr : Addr
  output : Addr
  seed : List Byte
  W : Nat → BitVec 64
  width : prime.len = 20 ∨ prime.len = 32
  words : prime.w = 4
  size : prime.Z = Impl.Dsa.Generation.Layout.arithmeticBytes
  draw : prime.drawBytes = if prime.len = 20 then 24 else 32
  checks : prime.checks = 64
  seedLength : seed.length = prime.len
  modulus : prime.N = Spec.Dsa.qCandidate (8 * prime.len) seed
  base : W 5 + BitVec.ofNat 64 Impl.Dsa.Generation.Layout.arithmetic = prime.B
  outputPtr : W 5 + BitVec.ofNat 64 Impl.Dsa.Generation.Layout.q = output
  outputSlot : W 0 = output
  witnessPtr : W 5 + BitVec.ofNat 64 Impl.Dsa.Generation.Layout.witness = prime.p
  tapePtr : W 14 = prime.rp
  tapeLength : W 15 = BitVec.ofNat 64 prime.rand.length
  frameHeaders : ∀ k < 34, ∀ j < 32,
    Mem.Sep (VG.Proof.Bignum.off F (8 * k)) 8 (VG.Proof.Bignum.off prime.B (8 * j)) 8
  frameOutside : ∀ k < 34, ∀ i < 8, prime.Z ≤ ofs prime.B (VG.Proof.Bignum.off (VG.Proof.Bignum.off F (8 * k)) i)
  outputOutside : ∀ i < prime.len, prime.Z ≤ ofs prime.B (VG.Proof.Bignum.off output i)
  outputFrame : (⟨output, prime.len⟩ : Region).Disjoint ⟨F, frameBytes⟩
  outputScratch : Region.Disjoint ⟨hash, oRsa⟩ ⟨output, prime.len⟩
  tapeHash : ∀ r ∈ [⟨output, prime.len⟩, ⟨hash, oRsa⟩, retR F],
    (⟨prime.rp, prime.rand.length⟩ : Region).Disjoint r
  framePrime : ∀ r ∈ [⟨prime.B, Impl.Dsa.Generation.Layout.arithmeticBytes⟩,
      ⟨prime.p, prime.len⟩], (⟨F, frameBytes⟩ : Region).Disjoint r
  hashPrime : ∀ r ∈ [⟨prime.B, Impl.Dsa.Generation.Layout.arithmeticBytes⟩,
      ⟨prime.p, prime.len⟩], (⟨hash, oRsa⟩ : Region).Disjoint r
  outputPrime : ∀ r ∈ [⟨prime.B, Impl.Dsa.Generation.Layout.arithmeticBytes⟩,
      ⟨prime.p, prime.len⟩], (⟨output, prime.len⟩ : Region).Disjoint r

def SubgroupPlan.hashWrites (p : SubgroupPlan) : List Region :=
  [⟨p.output, p.prime.len⟩, ⟨p.hash, oRsa⟩, retR p.F]

def SubgroupPlan.primeWrites (p : SubgroupPlan) : List Region :=
  [⟨p.prime.B, Impl.Dsa.Generation.Layout.arithmeticBytes⟩, ⟨p.prime.p, p.prime.len⟩]

def SubgroupPlan.changed (p : SubgroupPlan) : List Region :=
  p.hashWrites ++ p.primeWrites ++ [⟨p.F, frameBytes⟩]

structure SubgroupState (p : SubgroupPlan) (used : Nat) (s : State) : Prop where
  layout : Lay s p.F p.hash
  rep : ∃ V, Rep s.mem p.F p.hash V p.W
  label : LabAt s p.F p.hash p.W p.seedPtr p.prime.len
  seed : Spec.Rsa.bytesAt s.mem p.seedPtr p.prime.len = p.seed
  scratch : Scr s p.prime.B p.prime.Z
  tape : Src s p.prime.B p.prime.Z p.prime.rp p.prime.rand
  outputWrite : ∀ i < p.prime.len, InRegions s.wr (VG.Proof.Bignum.off p.output i) 1
  witnessWrite : ∀ i < p.prime.len, InRegions s.wr (VG.Proof.Bignum.off p.prime.p i) 1
  usedSlot : p.W 16 = BitVec.ofNat 64 used
  usedBound : used ≤ p.prime.rand.length

theorem SubgroupPlan.bits (p : SubgroupPlan) : Spec.Dsa.bitLength p.prime.N = 8 * p.prime.len := by
  rw [p.modulus]
  exact VG.Proof.Dsa.Generation.qCandidate_bitLength (by rcases p.width with h | h <;> omega) _

theorem SubgroupPlan.large (p : SubgroupPlan) : 8161 < p.prime.N := by
  have hshape := VG.Proof.Dsa.Generation.qCandidate_shape
    (show 2 ≤ 8 * p.prime.len by rcases p.width with h | h <;> omega) p.seed
  rw [← p.modulus] at hshape
  have hbig : 8161 < 2 ^ (8 * p.prime.len - 1) := by
    rcases p.width with h | h <;> rw [h] <;> decide
  exact Nat.lt_of_lt_of_le hbig hshape.2.1

theorem SubgroupPlan.encoding (p : SubgroupPlan) :
    Spec.Rsa.os2ip (Spec.Dsa.encodeBE p.prime.len p.prime.N) = p.prime.N := by
  rw [← VG.Proof.Dsa.decodeBE_os2ip]
  apply VG.Proof.Dsa.decodeBE_encodeBE
  have hshape := VG.Proof.Dsa.Generation.qCandidate_shape
    (show 2 ≤ 8 * p.prime.len by rcases p.width with h | h <;> omega) p.seed
  rw [← p.modulus] at hshape
  have hp : 256 ^ p.prime.len = 2 ^ (8 * p.prime.len) := by
    rw [Nat.pow_mul]
  rw [hp]
  exact hshape.2.2

end VG.Proof.Dsa.AArch64.Generation
