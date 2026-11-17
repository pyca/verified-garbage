module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchEntry
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchControl
import VerifiedGarbage.Proof.Framework.Omega
public import Mathlib.Algebra.Group.Nat.Defs
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PPrimalityPlan
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.HeaderCT
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PConstructCTState

/-! ### `Dsa.X86_64.Generation.PPrimalityCTState`, which this module and modules that import it used -/

section

/-! # Public p-search data and the live frame words used by primality -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

def PPrimalityWords (p : PPrimalityPlan) (W : Nat → BitVec 64) : Prop :=
  (∀ i < 6, W i = p.construct.hash.W i) ∧ W 13 = p.rp ∧ W 15 = BitVec.ofNat 64 p.rand.length

def PPrimalityPlan.withWords (p : PPrimalityPlan) (W : Nat → BitVec 64)
    (hw : PPrimalityWords p W) : PPrimalityPlan :=
  { p with
    construct := p.construct.withWords W hw.1
    tapePtr := hw.2.1
    tapeLength := hw.2.2
    bufferSeparate := by simpa only [PConstructPlan.withWords, HashPlan.withWords, hw.1 5 (by decide)] using p.bufferSeparate
    bufferOutside := by simpa only [PConstructPlan.withWords, HashPlan.withWords, hw.1 5 (by decide)] using p.bufferOutside
    tapeBuffer := by simpa only [PConstructPlan.withWords, HashPlan.withWords, hw.1 5 (by decide)] using p.tapeBuffer
    framePrime := by simpa only [PConstructPlan.withWords, HashPlan.withWords, hw.1 5 (by decide)] using p.framePrime
    hashPrime := by simpa only [PConstructPlan.withWords, HashPlan.withWords, hw.1 5 (by decide)] using p.hashPrime
    pPrime := by simpa only [PConstructPlan.withWords, HashPlan.withWords, hw.1 5 (by decide)] using p.pPrime
    exponentPrime := by simpa only [PConstructPlan.withWords, HashPlan.withWords, hw.1 5 (by decide)] using p.exponentPrime
    arenaBound := by simpa only [PConstructPlan.withWords, HashPlan.withWords, hw.1 5 (by decide)] using p.arenaBound
    tapeArena := by simpa only [PConstructPlan.withWords, HashPlan.withWords, hw.1 5 (by decide)] using p.tapeArena
    arenaFrame := by simpa only [PConstructPlan.withWords, HashPlan.withWords, hw.1 5 (by decide)] using p.arenaFrame
    arenaStack := by simpa only [PConstructPlan.withWords, HashPlan.withWords, hw.1 5 (by decide)] using p.arenaStack
    tapeConstruct := by
      simpa only [PConstructPlan.withWords, HashPlan.withWords, PConstructPlan.changed, HashPlan.changed,
        hw.1 5 (by decide)] using p.tapeConstruct }

structure PPrimalityPublic where
  plan : PPrimalityPlan
  used : Nat
  ws : List Region
  wr : List Region
  header : PrimeHeaderLayout (plan.construct.hash.W 5) wr

def PPrimalityPublic.construct (p : PPrimalityPublic) : PConstructPublic := ⟨p.plan.construct, p.ws⟩

def PPrimalityBefore (n : Nat) (H : Spec.Mgf1.Hash) (pLen qLen : Nat)
    (p : PPrimalityPublic) (s : State) : Prop :=
  (∃ W, ∃ hw : PPrimalityWords p.plan W,
    PConstructState (p.plan.construct.withWords W hw.1) H s ∧
      FrV n p.plan.construct.hash.F p.ws s ∧ W 16 = BitVec.ofNat 64 p.used) ∧
    s.wr = p.wr ∧ p.used ≤ p.plan.rand.length ∧
    Src s p.plan.construct.B p.plan.construct.Z p.plan.rp p.plan.rand ∧
    (Scr s (p.plan.construct.hash.W 5) domainCheck ∧
      Covers [⟨p.plan.rp, p.plan.rand.length⟩] (s.rd ++ s.wr)) ∧
    p.plan.construct.len = pLen ∧ p.plan.construct.hash.len = qLen

theorem pPrimality_construct {n pLen qLen : Nat} {H : Spec.Mgf1.Hash} {p : PPrimalityPublic} {s : State}
    (h : PPrimalityBefore n H pLen qLen p s) : PConstructBefore n H pLen qLen p.construct s := by
  obtain ⟨W, hw, hs, hf, _⟩ := h.1
  exact ⟨⟨W, hw.1, hs, hf⟩, h.2.2.2.2.2⟩

structure PPrimalityAfter (p : PPrimalityPublic) (s : State) : Prop where
  layout : Lay s p.plan.construct.hash.F p.plan.construct.hash.S
  frame : ∃ V W, Rep s.mem p.plan.construct.hash.F p.plan.construct.hash.S V W ∧
    PPrimalityWords p.plan W ∧ W 16 = BitVec.ofNat 64 p.used
  ws : VG.Proof.Rsa.X86_64.Ws s p.plan.construct.B p.plan.construct.Z (p.plan.construct.len / 8)
  pointer : word s.mem p.plan.construct.B 160 = off (p.plan.construct.hash.W 5) Impl.Dsa.Generation.Layout.p
  bytes : Spec.Rsa.bytesAt s.mem (off (p.plan.construct.hash.W 5) Impl.Dsa.Generation.Layout.p) p.plan.construct.len =
    Spec.Dsa.encodeBE p.plan.construct.len p.plan.construct.value
  odd : p.plan.construct.value % 2 = 1
  fits : p.plan.construct.value < 2 ^ (8 * p.plan.construct.len)
  source : Src s p.plan.construct.B p.plan.construct.Z
    (off (p.plan.construct.hash.W 5) Impl.Dsa.Generation.Layout.p)
    (Spec.Dsa.encodeBE p.plan.construct.len p.plan.construct.value)
  tape : Src s p.plan.construct.B p.plan.construct.Z p.plan.rp p.plan.rand
  arena : Scr s (p.plan.construct.hash.W 5) domainCheck
  tapeCover : Covers [⟨p.plan.rp, p.plan.rand.length⟩] (s.rd ++ s.wr)
  wr : s.wr = p.wr
  usedBound : p.used ≤ p.plan.rand.length

end VG.Proof.Dsa.X86_64.Generation

end

end

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
    have := p.plan.attempt.construct.hash.count_le; omega_using [this])
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
