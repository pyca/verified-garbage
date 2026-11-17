module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SearchEntry
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.AttemptBlocksCT
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SearchControl
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PPrimalityPlan
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PConstructCTState

/-! ### `Dsa.AArch64.Generation.PPrimalityCTState`, which this module and modules that import it used -/

section

/-! # Public p-search data and the live frame words used by primality -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

def PPrimalityWords (p : PPrimalityPlan) (W : Nat → BitVec 64) : Prop :=
  (∀ i < 6, W i = p.construct.hash.W i) ∧ W 14 = p.rp ∧ W 15 = BitVec.ofNat 64 p.rand.length

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
    hashStack := by simpa only [PConstructPlan.withWords, HashPlan.withWords, hw.1 5 (by decide)] using p.hashStack
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

def PPrimalityPublic.construct (p : PPrimalityPublic) : PConstructPublic := ⟨p.plan.construct⟩

def PPrimalityBefore (H : Spec.Mgf1.Hash) (pLen qLen : Nat)
    (p : PPrimalityPublic) (s : State) : Prop :=
  (∃ W, ∃ hw : PPrimalityWords p.plan W,
    PConstructState (p.plan.construct.withWords W hw.1) H s ∧
      W 16 = BitVec.ofNat 64 p.used) ∧
    p.used ≤ p.plan.rand.length ∧
    Src s p.plan.construct.B p.plan.construct.Z p.plan.rp p.plan.rand ∧
    (Scr s (p.plan.construct.hash.W 5) domainCheck ∧
      Covers [⟨p.plan.rp, p.plan.rand.length⟩] (s.rd ++ s.wr)) ∧
    p.plan.construct.len = pLen ∧ p.plan.construct.hash.len = qLen

theorem pPrimality_construct {pLen qLen : Nat} {H : Spec.Mgf1.Hash} {p : PPrimalityPublic} {s : State}
    (h : PPrimalityBefore H pLen qLen p s) : PConstructBefore H pLen qLen p.construct s := by
  obtain ⟨W, hw, hs, _⟩ := h.1
  exact ⟨⟨W, hw.1, hs⟩, h.2.2.2.2⟩

structure PPrimalityAfter (p : PPrimalityPublic) (s : State) : Prop where
  layout : Lay s p.plan.construct.hash.F p.plan.construct.hash.S
  frame : ∃ V W, Rep s.mem p.plan.construct.hash.F p.plan.construct.hash.S V W ∧
    PPrimalityWords p.plan W ∧ W 16 = BitVec.ofNat 64 p.used
  ws : VG.Proof.Rsa.AArch64.Ws s p.plan.construct.B p.plan.construct.Z (p.plan.construct.len / 8)
  pointer : VG.Proof.Bignum.word s.mem p.plan.construct.B 160 = VG.Proof.Bignum.off (p.plan.construct.hash.W 5) Impl.Dsa.Generation.Layout.p
  bytes : Spec.Rsa.bytesAt s.mem (VG.Proof.Bignum.off (p.plan.construct.hash.W 5) Impl.Dsa.Generation.Layout.p) p.plan.construct.len =
    Spec.Dsa.encodeBE p.plan.construct.len p.plan.construct.value
  odd : p.plan.construct.value % 2 = 1
  fits : p.plan.construct.value < 2 ^ (8 * p.plan.construct.len)
  source : Src s p.plan.construct.B p.plan.construct.Z
    (VG.Proof.Bignum.off (p.plan.construct.hash.W 5) Impl.Dsa.Generation.Layout.p)
    (Spec.Dsa.encodeBE p.plan.construct.len p.plan.construct.value)
  tape : Src s p.plan.construct.B p.plan.construct.Z p.plan.rp p.plan.rand
  arena : Scr s (p.plan.construct.hash.W 5) domainCheck
  tapeCover : Covers [⟨p.plan.rp, p.plan.rand.length⟩] (s.rd ++ s.wr)
  usedBound : p.used ≤ p.plan.rand.length

end VG.Proof.Dsa.AArch64.Generation

end

end

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
