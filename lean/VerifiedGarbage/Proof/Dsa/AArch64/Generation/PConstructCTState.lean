module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PConstructPlan
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PShapeCT
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PBuildValue
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CandidateWorkspaceCT
import VerifiedGarbage.Proof.Framework.Omega

/-! # Public data connecting p hashing to native reduction -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

def PConstructPlan.withWords (p : PConstructPlan) (W : Nat → BitVec 64)
    (hw : ∀ i < 6, W i = p.hash.W i) : PConstructPlan :=
  { p with
    hash := p.hash.withWords W (fun i hi => hw i (by omega))
    base := by simpa only [HashPlan.withWords, hw 5 (by decide)] using p.base
    shapedSlot := by simpa only [HashPlan.withWords, hw 0 (by decide), hw 5 (by decide)] using p.shapedSlot
    shapedOutside := by simpa only [HashPlan.withWords, hw 5 (by decide)] using p.shapedOutside
    shapedHash := by simpa only [HashPlan.withWords, hw 5 (by decide)] using p.shapedHash
    shapedInput := by simpa only [HashPlan.withWords, hw 5 (by decide)] using p.shapedInput
    qHash := by simpa only [HashPlan.withWords, HashPlan.changed, hw 5 (by decide)] using p.qHash
    pOutside := by simpa only [HashPlan.withWords, hw 5 (by decide)] using p.pOutside
    exponentOutside := by simpa only [HashPlan.withWords, hw 5 (by decide)] using p.exponentOutside
    pExponent := by simpa only [HashPlan.withWords, hw 5 (by decide)] using p.pExponent
    frameArithmetic := by simpa only [HashPlan.withWords, hw 5 (by decide)] using p.frameArithmetic
    hashArithmetic := by simpa only [HashPlan.withWords, hw 5 (by decide)] using p.hashArithmetic }

structure PConstructPublic where
  plan : PConstructPlan

def PConstructBefore (H : Spec.Mgf1.Hash) (pLen qLen : Nat)
    (p : PConstructPublic) (s : State) : Prop :=
  (∃ W, ∃ hw : ∀ i < 6, W i = p.plan.hash.W i,
    PConstructState (p.plan.withWords W hw) H s) ∧
    p.plan.len = pLen ∧ p.plan.hash.len = qLen

def PConstructPublic.hash (p : PConstructPublic) : PHashPublic := ⟨p.plan.hash⟩

theorem pConstruct_hash {pLen qLen : Nat} {H : Spec.Mgf1.Hash} {p : PConstructPublic} {s : State}
    (h : PConstructBefore H pLen qLen p s) :
    ContributionBefore H 0 qLen ((8 * pLen - 1) / (8 * qLen)) p.hash s := by
  obtain ⟨⟨W, hw, hs⟩, hp, hq⟩ := h
  exact ⟨⟨W, (fun i hi => hw i (by omega)), hs.hash⟩, hq,
    p.plan.hashCount.trans (by rw [hp, hq])⟩

def PConstructPublic.workspace (p : PConstructPublic) (H : Spec.Mgf1.Hash) : CandidateWorkspacePublic where
  frame := {
    B := p.plan.B
    F := p.plan.hash.F
    arena := p.plan.hash.W 5
    Z := p.plan.Z
    w := p.plan.len / 8
    width := by rcases p.plan.width with h | h | h <;> omega
    xb := Spec.Dsa.encodeBE p.plan.len (p.plan.hash.shapedValue H p.plan.len)
    qb := p.plan.qb
    xLength := by rw [VG.Proof.Dsa.encodeBE_length]; rcases p.plan.width with h | h | h <;> omega
    qLength := by
      rw [p.plan.qLength]
      rcases p.plan.width with h | h | h <;> rcases p.plan.hash.width with q | q <;> omega
    qNonempty := by rw [p.plan.qLength]; rcases p.plan.hash.width with h | h <;> omega
    qPositive := p.plan.qPositive
    qFits := p.plan.qFits
    separate := p.plan.frameHeaders
    pOutside := by
      have he : 8 * (p.plan.len / 8) = p.plan.len := by rcases p.plan.width with h | h | h <;> omega
      simpa only [he] using p.plan.pOutside
    eOutside := by
      have he : 8 * (p.plan.len / 8) = p.plan.len := by rcases p.plan.width with h | h | h <;> omega
      simpa only [he] using p.plan.exponentOutside }
  base := p.plan.base.symm
  room := p.plan.workspaceRoom
  lower := by rcases p.plan.width with h | h | h <;> dsimp only <;> omega
  upper := by rcases p.plan.width with h | h | h <;> dsimp only <;> omega
  outside := p.plan.frameOutside

end VG.Proof.Dsa.AArch64.Generation
