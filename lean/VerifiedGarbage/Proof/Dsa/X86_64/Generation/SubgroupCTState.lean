module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SubgroupState
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.QBuildCT
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeCallCT
import VerifiedGarbage.Proof.Framework.Omega

/-! # Public subgroup-generation data excludes unused frame contents -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.RsaOaep.X86_64 VG.Proof.RsaOaep.X86_64

structure SubgroupPublic where
  plan : SubgroupPlan
  used : Nat
  ws : List Region
  wr : List Region
  header : PrimeHeaderLayout (plan.W 5) wr

def SubgroupPlan.withWords (p : SubgroupPlan) (W : Nat → BitVec 64)
    (hw : ∀ i ∈ [0, 5, 13, 15], W i = p.W i) : SubgroupPlan :=
  { p with W := W
           base := by rw [hw 5 (by simp)]; exact p.base
           outputPtr := by rw [hw 5 (by simp)]; exact p.outputPtr
           outputSlot := (hw 0 (by simp)).trans p.outputSlot
           witnessPtr := by rw [hw 5 (by simp)]; exact p.witnessPtr
           tapePtr := (hw 13 (by simp)).trans p.tapePtr
           tapeLength := (hw 15 (by simp)).trans p.tapeLength }

def SubgroupBefore (n : Nat) (p : SubgroupPublic) (s : State) : Prop :=
  ∃ W, ∃ hw : ∀ i ∈ [0, 5, 13, 15], W i = p.plan.W i,
    SubgroupState (p.plan.withWords W hw) p.used s ∧
      FrV n p.plan.prime.sp p.ws s ∧ s.wr = p.wr

def SubgroupPublic.hash (p : SubgroupPublic) : QHashPlan :=
  ⟨⟨p.plan.prime.sp, p.plan.hash, p.ws, p.plan.seedPtr, p.plan.prime.len⟩,
    p.plan.output, p.plan.width⟩

theorem subgroup_hash {n : Nat} {p : SubgroupPublic} {s : State}
    (h : SubgroupBefore n p s) : QHashState n p.hash s := by
  obtain ⟨W, hw, hs, hf, _⟩ := h
  obtain ⟨V, R⟩ := hs.rep
  exact ⟨hf, hs.layout, V, W, R, hs.label, (p.plan.withWords W hw).outputSlot⟩

def SubgroupPublic.call (p : SubgroupPublic) : PrimeFramePublic where
  bytes := {
    call := {
      draw := ⟨p.plan.prime, p.used⟩
      arena := p.plan.W 5
      wr := p.wr
      layout := p.header
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
  candidate := Impl.Dsa.Generation.Layout.q
  candidateBound := by decide
  checksBound := by change p.plan.prime.checks < 2 ^ 31; rw [p.plan.checks]; decide
  checks := by
    change p.plan.prime.checks = Spec.Dsa.primeChecks (Spec.Dsa.bitLength p.plan.prime.N)
    rw [p.plan.checks, p.plan.bits]
    rcases p.plan.width with h | h <;> rw [h] <;> decide
  source := p.plan.outputPtr.symm
  witness := p.plan.witnessPtr.symm
  separate := p.plan.frameHeaders
  outside := p.plan.frameOutside

end VG.Proof.Dsa.X86_64.Generation
