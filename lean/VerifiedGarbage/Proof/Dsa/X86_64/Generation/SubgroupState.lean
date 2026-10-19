module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.QBuild
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CheckPrime
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeFootprint
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeResult
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.WorkspaceBase
public import VerifiedGarbage.Proof.Dsa.Generation.Memory
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Subgroup
import VerifiedGarbage.Proof.Framework.Omega

/-! # State connecting subgroup hashing to the complete native primality call -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.RsaOaep.X86_64 VG.Proof.RsaOaep.X86_64

structure SubgroupPlan where
  prime : PrimeParams
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
  tapePtr : W 13 = prime.rp
  tapeLength : W 15 = BitVec.ofNat 64 prime.rand.length
  frameHeaders : ∀ k < 37, ∀ j < 32,
    Mem.Sep (off prime.sp (8 * k)) 8 (off prime.B (8 * j)) 8
  frameOutside : ∀ k < 37, ∀ i < 8, prime.Z ≤ ofs prime.B (off (off prime.sp (8 * k)) i)
  outputOutside : ∀ i < prime.len, prime.Z ≤ ofs prime.B (off output i)
  outputFrame : (⟨output, prime.len⟩ : Region).Disjoint ⟨prime.sp, frameBytes⟩
  outputHash : HashBufferSeparate prime.sp hash output prime.len
  tapeHash : ∀ r ∈ [⟨output, prime.len⟩, ⟨hash, oRsa⟩, retR prime.sp],
    (⟨prime.rp, prime.rand.length⟩ : Region).Disjoint r
  framePrime : ∀ r ∈ [⟨prime.B, Impl.Dsa.Generation.Layout.arithmeticBytes⟩,
      ⟨prime.p, prime.len⟩, below prime.sp 128], (⟨prime.sp, frameBytes⟩ : Region).Disjoint r
  hashPrime : ∀ r ∈ [⟨prime.B, Impl.Dsa.Generation.Layout.arithmeticBytes⟩,
      ⟨prime.p, prime.len⟩, below prime.sp 128], (⟨hash, oRsa⟩ : Region).Disjoint r
  outputPrime : ∀ r ∈ [⟨prime.B, Impl.Dsa.Generation.Layout.arithmeticBytes⟩,
      ⟨prime.p, prime.len⟩, below prime.sp 128], (⟨output, prime.len⟩ : Region).Disjoint r

def SubgroupPlan.hashWrites (p : SubgroupPlan) : List Region :=
  [⟨p.output, p.prime.len⟩, ⟨p.hash, oRsa⟩, retR p.prime.sp]

def SubgroupPlan.primeWrites (p : SubgroupPlan) : List Region :=
  [⟨p.prime.B, Impl.Dsa.Generation.Layout.arithmeticBytes⟩, ⟨p.prime.p, p.prime.len⟩, below p.prime.sp 128]

def SubgroupPlan.changed (p : SubgroupPlan) : List Region :=
  p.hashWrites ++ p.primeWrites ++ [⟨p.prime.sp, frameBytes⟩]

structure SubgroupState (p : SubgroupPlan) (used : Nat) (s : State) : Prop where
  layout : Lay s p.prime.sp p.hash
  rep : ∃ V, Rep s.mem p.prime.sp p.hash V p.W
  label : LabAt s p.prime.sp p.hash p.W p.seedPtr p.prime.len
  seed : Spec.Rsa.bytesAt s.mem p.seedPtr p.prime.len = p.seed
  scratch : Scr s p.prime.B p.prime.Z
  tape : Src s p.prime.B p.prime.Z p.prime.rp p.prime.rand
  outputWrite : ∀ i < p.prime.len, InRegions s.wr (off p.output i) 1
  witnessWrite : ∀ i < p.prime.len, InRegions s.wr (off p.prime.p i) 1
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

end VG.Proof.Dsa.X86_64.Generation
