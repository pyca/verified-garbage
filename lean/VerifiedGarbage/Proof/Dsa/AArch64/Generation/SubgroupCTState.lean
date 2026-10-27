module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SubgroupState
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.QBuildCT
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeCallCT
import VerifiedGarbage.Proof.Framework.Omega

/-! # Public subgroup-generation data excludes unused frame contents -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.RsaOaep.AArch64 VG.Proof.RsaOaep.AArch64

structure SubgroupPublic where
  plan : SubgroupPlan
  used : Nat

def SubgroupPlan.withWords (p : SubgroupPlan) (W : Nat → BitVec 64)
    (hw : ∀ i ∈ [0, 5, 14, 15], W i = p.W i) : SubgroupPlan :=
  { p with W := W
           base := by rw [hw 5 (by simp)]; exact p.base
           outputPtr := by rw [hw 5 (by simp)]; exact p.outputPtr
           outputSlot := (hw 0 (by simp)).trans p.outputSlot
           witnessPtr := by rw [hw 5 (by simp)]; exact p.witnessPtr
           tapePtr := (hw 14 (by simp)).trans p.tapePtr
           tapeLength := (hw 15 (by simp)).trans p.tapeLength
           geometry := by rw [hw 5 (by simp)]; exact p.geometry }

def SubgroupBefore (p : SubgroupPublic) (s : State) : Prop :=
  ∃ W, ∃ hw : ∀ i ∈ [0, 5, 14, 15], W i = p.plan.W i,
    SubgroupState (p.plan.withWords W hw) p.used s

def SubgroupPublic.hash (p : SubgroupPublic) : QHashPlan :=
  ⟨p.plan.F, p.plan.hash, p.plan.seedPtr, p.plan.prime.len, p.plan.output, p.plan.width⟩

theorem subgroup_hash {p : SubgroupPublic} {s : State} (h : SubgroupBefore p s) : QHashState p.hash s := by
  obtain ⟨W, hw, hs⟩ := h
  obtain ⟨V, R⟩ := hs.rep
  exact ⟨hs.layout, V, W, R, hs.label, (p.plan.withWords W hw).outputSlot⟩

def SubgroupPublic.primeCall (p : SubgroupPublic) : PrimeTestPublic (8 * p.plan.prime.len) where
  F := p.plan.F
  S := p.plan.hash
  A := p.plan.W 5
  rp := p.plan.prime.rp
  rand := p.plan.prime.rand
  N := p.plan.prime.N
  used := p.used
  geometry := p.plan.geometry

end VG.Proof.Dsa.AArch64.Generation
