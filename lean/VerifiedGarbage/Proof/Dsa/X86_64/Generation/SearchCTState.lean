module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchEntry
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PPrimalityCTState
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchControl
import VerifiedGarbage.Proof.Framework.Omega
public import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Data.Int.ModEq

/-! # The p-search counter and entropy cursor determine each public attempt -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

structure SearchPublic where
  plan : SearchPlan
  ws : List Region
  wr : List Region
  header : PrimeHeaderLayout (plan.attempt.construct.hash.W 5) wr
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
    (by simp [attemptWords, VG.Proof.RsaOaep.X86_64.upd])
    (by simp [attemptWords, VG.Proof.RsaOaep.X86_64.upd]) p.carry

def SearchPublic.attempt (p : SearchPublic) : PPrimalityPublic where
  plan := p.attemptPlan
  used := p.used
  ws := p.ws
  wr := p.wr
  header := by
    simpa [SearchPublic.attemptPlan, PPrimalityPlan.reframe, PConstructPlan.reframe, HashPlan.reframe,
      attemptWords, VG.Proof.RsaOaep.X86_64.upd] using p.header

def SearchBefore (n pLen qLen : Nat) (p : SearchPublic) (s : State) : Prop :=
  (∃ W, SearchMemory p.plan W s ∧ W 16 = BitVec.ofNat 64 p.used) ∧
    SearchControl p.plan.C p.counter (p.plan.attempt.construct.hash.count + 1) s ∧
    FrV n p.plan.attempt.construct.hash.F p.ws s ∧ s.wr = p.wr ∧
    p.used ≤ p.plan.attempt.rand.length ∧ p.plan.attempt.construct.len = pLen ∧
    p.plan.attempt.construct.hash.len = qLen

def SearchPublic.pointers (p : SearchPublic) : ArgumentPointers :=
  ⟨p.plan.C, p.plan.attempt.construct.hash.F⟩

theorem searchBefore_pointers {n pLen qLen : Nat} {p : SearchPublic} {s : State}
    (h : SearchBefore n pLen qLen p s) : ArgumentRegisters p.pointers s := by
  obtain ⟨W, hs, _⟩ := h.1
  exact ⟨h.2.1.rdi, hs.layout.rsp⟩

end VG.Proof.Dsa.X86_64.Generation
