module
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Memory
public import VerifiedGarbage.Proof.RsaOaep.AArch64.Label
public import VerifiedGarbage.Spec.Dsa

import VerifiedGarbage.Proof.Framework.Offset
public import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.Contract

/-! # Layout and progress for the bounded sequence of p hash contributions -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum.AArch64
open VG.Impl.RsaOaep.AArch64 VG.Proof.RsaOaep.AArch64

structure HashPlan where
  F : Addr
  S : Addr
  seedPtr : Addr
  wrapped : Addr
  output : Addr
  len : Nat
  count : Nat
  offset : Nat
  seed : List Byte
  W : Nat → BitVec 64
  width : len = 20 ∨ len = 32
  count_le : count ≤ 11
  carry : offset + count < 2 ^ 32
  seed_len : seed.length = len
  seed_slot : W 1 = seedPtr
  wrapped_slot : W 3 = wrapped
  output_slot : W 4 = output
  offset_slot : W 2 = BitVec.ofNat 64 offset
  wrapped_sep : HashBufferSeparate F S wrapped len
  output_sep : HashBufferSeparate F S output ((count + 1) * len)
  seed_wrap : (⟨seedPtr, len⟩ : Region).Disjoint ⟨wrapped, len⟩
  seed_output : (⟨seedPtr, len⟩ : Region).Disjoint ⟨output, (count + 1) * len⟩
  seed_scratch : (⟨seedPtr, len⟩ : Region).Disjoint ⟨S, oRsa⟩
  seed_stack : (⟨seedPtr, len⟩ : Region).Disjoint (retR F)
  output_wrap : (⟨output, (count + 1) * len⟩ : Region).Disjoint ⟨wrapped, len⟩
  output_scratch : (⟨output, (count + 1) * len⟩ : Region).Disjoint ⟨S, oRsa⟩
  output_stack : (⟨output, (count + 1) * len⟩ : Region).Disjoint (retR F)

def HashPlan.dest (p : HashPlan) (j : Nat) : Addr := off p.output ((p.count - j) * p.len)
def HashPlan.changed (p : HashPlan) : List Region :=
  [⟨p.output, (p.count + 1) * p.len⟩, ⟨p.wrapped, p.len⟩, ⟨p.S, oRsa⟩, retR p.F]

theorem HashPlan.size (p : HashPlan) :
    0 < p.len ∧ p.len ≤ 32 ∧ (p.count + 1) * p.len < 2 ^ 31 := by
  have hc := p.count_le
  rcases p.width with h | h <;> rw [h] <;> omega

theorem HashPlan.dest_sub (p : HashPlan) (j : Nat) :
    Region.Sub ⟨p.dest j, p.len⟩ ⟨p.output, (p.count + 1) * p.len⟩ := by
  apply Offset.sub_base
  have h := Nat.mul_le_mul_right p.len (show p.count - j + 1 ≤ p.count + 1 by omega)
  simpa only [Nat.add_mul, Nat.one_mul] using h

theorem HashPlan.dest_sep (p : HashPlan) (j : Nat) : HashBufferSeparate p.F p.S (p.dest j) p.len where
  frame i hi k hk := by
    have hbound : (p.count - j) * p.len + i < (p.count + 1) * p.len := by
      have h := Nat.mul_le_mul_right p.len (show p.count - j + 1 ≤ p.count + 1 by omega)
      rw [Nat.add_mul, Nat.one_mul] at h
      omega
    simpa only [HashPlan.dest, off_off] using p.output_sep.frame _ hbound k hk
  scratch i hi k hk := by
    have hbound : (p.count - j) * p.len + i < (p.count + 1) * p.len := by
      have h := Nat.mul_le_mul_right p.len (show p.count - j + 1 ≤ p.count + 1 by omega)
      rw [Nat.add_mul, Nat.one_mul] at h
      omega
    simpa only [HashPlan.dest, off_off] using p.output_sep.scratch _ hbound k hk

theorem HashPlan.dest_disjoint (p : HashPlan) {j k : Nat} (hj : j ≤ p.count)
    (hk : k ≤ p.count) (hne : j ≠ k) :
    Region.Disjoint ⟨p.dest j, p.len⟩ ⟨p.dest k, p.len⟩ := by
  apply Offset.disjoint
  · rcases Nat.lt_or_gt_of_ne hne with h | h
    · right
      have hm := Nat.mul_le_mul_right p.len (show p.count - k + 1 ≤ p.count - j by omega)
      simpa only [Nat.add_mul, Nat.one_mul] using hm
    · left
      have hm := Nat.mul_le_mul_right p.len (show p.count - j + 1 ≤ p.count - k by omega)
      simpa only [Nat.add_mul, Nat.one_mul] using hm
  all_goals
    have hmj := Nat.mul_le_mul_right p.len (show p.count - j + 1 ≤ p.count + 1 by omega)
    have hmk := Nat.mul_le_mul_right p.len (show p.count - k + 1 ≤ p.count + 1 by omega)
    rw [Nat.add_mul, Nat.one_mul] at hmj hmk
    omega_using [p.size.2.2, hmj, hmk]

def HashPlan.digest (p : HashPlan) (H : Spec.Mgf1.Hash) (j : Nat) : List Byte :=
  H.hash (Spec.Dsa.encodeBE p.len (Spec.Dsa.decodeBE p.seed + (p.offset + j)))

structure HashState (p : HashPlan) (H : Spec.Mgf1.Hash) (k : Nat) (s : State) : Prop where
  layout : Lay s p.F p.S
  rep : ∃ V, Rep s.mem p.F p.S V p.W
  hashArgs : LabAt s p.F p.S p.W p.wrapped p.len
  seedRead : ∀ i < p.len, InRegions (s.rd ++ s.wr) (off p.seedPtr i) 1
  wrappedWrite : ∀ i < p.len, InRegions s.wr (off p.wrapped i) 1
  outputWrite : ∀ i < (p.count + 1) * p.len, InRegions s.wr (off p.output i) 1
  seed : Spec.Rsa.bytesAt s.mem p.seedPtr p.len = p.seed
  hashes : ∀ j < k, Spec.Rsa.bytesAt s.mem (p.dest j) p.len = p.digest H j

end VG.Proof.Dsa.AArch64.Generation
