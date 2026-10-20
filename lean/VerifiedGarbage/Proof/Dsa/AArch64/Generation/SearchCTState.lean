module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SearchEntry
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.AttemptBlocksCT
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PPrimalityCTState
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SearchControl
import VerifiedGarbage.Proof.Framework.Omega

/-! # The p-search counter and entropy cursor determine each public attempt -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

structure SearchPublic where
  plan : SearchPlan
  counter : Nat
  used : Nat
  bound : counter < 32 * plan.attempt.construct.len

def SearchPublic.offset (p : SearchPublic) : Nat :=
  1 + p.counter * (p.plan.attempt.construct.hash.count + 1)

theorem SearchPublic.carry (p : SearchPublic) : p.offset + p.plan.attempt.construct.hash.count < 2 ^ 32 := by
  have hc : p.counter < 12288 := by
    rcases p.plan.attempt.construct.width with h | h | h <;> omega_using [p.bound, h]
  have hm := Nat.mul_le_mul_left p.counter (show p.plan.attempt.construct.hash.count + 1 ≤ 12 by
    have := p.plan.attempt.construct.hash.count_le; omega)
  dsimp only [SearchPublic.offset]
  omega_using [p.plan.attempt.construct.hash.count_le, hc, hm]

def SearchPublic.attemptPlan (p : SearchPublic) : PPrimalityPlan :=
  p.plan.attempt.reframe (attemptWords p.plan.attempt.construct.hash.W p.offset) p.offset
    (attemptWords_slot _ _ (by simp [searchSlots]))
    (attemptWords_slot _ _ (by simp [searchSlots]))
    (attemptWords_slot _ _ (by simp [searchSlots]))
    (attemptWords_slot _ _ (by simp [searchSlots]))
    (attemptWords_slot _ _ (by simp [searchSlots]))
    (attemptWords_slot _ _ (by simp [searchSlots]))
    (by simp [attemptWords, VG.Proof.RsaOaep.AArch64.upd])
    (by simp [attemptWords, VG.Proof.RsaOaep.AArch64.upd]) p.carry

def SearchPublic.attempt (p : SearchPublic) : PPrimalityPublic where
  plan := p.attemptPlan
  used := p.used
def SearchBefore (pLen qLen : Nat) (p : SearchPublic) (s : State) : Prop :=
  (∃ W, SearchMemory p.plan W s ∧ W 16 = BitVec.ofNat 64 p.used) ∧
    SearchControl p.plan.C p.counter (p.plan.attempt.construct.hash.count + 1) s ∧
    p.used ≤ p.plan.attempt.rand.length ∧ p.plan.attempt.construct.len = pLen ∧
    p.plan.attempt.construct.hash.len = qLen

def SearchPublic.pointers (p : SearchPublic) : AttemptPointers :=
  ⟨p.plan.C, p.plan.attempt.construct.hash.F⟩

theorem searchBefore_pointers {pLen qLen : Nat} {p : SearchPublic} {s : State}
    (h : SearchBefore pLen qLen p s) : AttemptRegisters p.pointers s := by
  obtain ⟨W, hs, _⟩ := h.1
  exact ⟨h.2.1.x0, hs.layout.sp⟩

end VG.Proof.Dsa.AArch64.Generation
