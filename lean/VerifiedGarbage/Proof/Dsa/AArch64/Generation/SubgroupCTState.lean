module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SubgroupState
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.QBuildCT
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeFrameCTState
public import VerifiedGarbage.Proof.Dsa.Encoding
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
           tapeLength := (hw 15 (by simp)).trans p.tapeLength }

def SubgroupBefore (p : SubgroupPublic) (s : State) : Prop :=
  ∃ W, ∃ hw : ∀ i ∈ [0, 5, 14, 15], W i = p.plan.W i,
    SubgroupState (p.plan.withWords W hw) p.used s

def SubgroupPublic.hash (p : SubgroupPublic) : QHashPlan :=
  ⟨p.plan.F, p.plan.hash, p.plan.seedPtr, p.plan.prime.len, p.plan.output, p.plan.width⟩

theorem subgroup_hash {p : SubgroupPublic} {s : State} (h : SubgroupBefore p s) : QHashState p.hash s := by
  obtain ⟨W, hw, hs⟩ := h
  obtain ⟨V, R⟩ := hs.rep
  exact ⟨hs.layout, V, W, R, hs.label, (p.plan.withWords W hw).outputSlot⟩

def SubgroupPublic.call (p : SubgroupPublic) : PrimeFramePublic where
  bytes := {
    call := {
      draw := ⟨p.plan.prime, p.used⟩
      arena := p.plan.W 5
      base := p.plan.base.symm
      width := by rw [p.plan.words]; decide
      tab := by rw [p.plan.words, p.plan.size]; decide +kernel
      large := p.plan.large
      policy := by
        rw [p.plan.bits, p.plan.words]
        rcases p.plan.width with h | h <;> rw [h] <;> decide }
    source := p.plan.output
    bytes := Spec.Dsa.encodeBE p.plan.prime.len p.plan.prime.N
    length := VG.Proof.Dsa.encodeBE_length _ _
    value := p.plan.encoding }
  F := p.plan.F
  candidate := Impl.Dsa.Generation.Layout.q
  candidateBound := by decide
  checksBound := by change p.plan.prime.checks < 2 ^ 16; rw [p.plan.checks]; decide
  checks := by
    change p.plan.prime.checks = Spec.Dsa.primeChecks (Spec.Dsa.bitLength p.plan.prime.N)
    rw [p.plan.checks, p.plan.bits]
    rcases p.plan.width with h | h <;> rw [h] <;> decide
  source := p.plan.outputPtr.symm
  witness := p.plan.witnessPtr.symm
  separate := p.plan.frameHeaders
  outside := p.plan.frameOutside

end VG.Proof.Dsa.AArch64.Generation
