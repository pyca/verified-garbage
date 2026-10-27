module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PPrimalityPlan
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.HeaderCT
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PConstructCTState
import VerifiedGarbage.Proof.Framework.Omega

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
    (∀ i < p.plan.construct.len, InRegions s.wr (off (off (p.plan.construct.hash.W 5) witness) i) 1) ∧
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
  writable : ∀ i < p.plan.construct.len, InRegions s.wr (off (off (p.plan.construct.hash.W 5) witness) i) 1
  wr : s.wr = p.wr
  usedBound : p.used ≤ p.plan.rand.length

end VG.Proof.Dsa.X86_64.Generation
