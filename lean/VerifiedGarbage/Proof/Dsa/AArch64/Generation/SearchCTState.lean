module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SearchEntry
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SearchControl
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PPrimalityPlan
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PConstructCTState
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.PAttempt
public import VerifiedGarbage.Proof.RsaOaep.AArch64.Basic
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.AttemptStatus
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.RsaOaep.AArch64.Hash
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
meta import VerifiedGarbage.Impl.Dsa.AArch64.Generation.PAttempt
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.Basic
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.AttemptStatus
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import Aesop.BuiltinRules
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.Hash

/-! ### `Dsa.AArch64.Generation.AttemptBlocksCT`, which this module and modules that import it used -/

section

/-! # Public addressing on p-attempt entry and return to the search controller -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.Dsa.AArch64.Generation

structure AttemptReturnPublic where
  F : Addr
  S : Addr
  arena : Addr

def AttemptReturnBefore (p : AttemptReturnPublic) (s : State) : Prop :=
  Lay s p.F p.S ∧ ∃ V W, Rep s.mem p.F p.S V W ∧ W 5 = p.arena

def AttemptReturnReady (p : AttemptReturnPublic) (s : State) : Prop :=
  s.gpr .x0 = VG.Proof.Bignum.off p.arena Impl.Dsa.Generation.Layout.control ∧ s.sp = p.F

theorem controlBase_ready {p : AttemptReturnPublic} {s : State} (h : AttemptReturnBefore p s) :
    WP isa (.block controlBase) s (AttemptReturnReady p) := by
  obtain ⟨V, W, R, hw⟩ := h.2
  exact WP.mono (controlBase_ok h.1 R (by rw [hw])) fun _ ⟨hb, _, hk⟩ =>
    ⟨hb, hk.sp.trans h.1.sp⟩

theorem controlBase_ct : RelCT isa (Two AttemptReturnBefore) (.block controlBase) (Two AttemptReturnReady) := by
  exact two_post (two_taint [] (by intro _ _ _ _ _ _ h; cases h) (by taint_decide))
    (fun _ _ h => controlBase_ready h)

theorem searchReturn_ct : RelCT isa (Two AttemptReturnBefore) (.block searchReturn) (fun _ _ => True) := by
  apply RelCT.block_append (M := isa) (l₁ := controlBase)
    (l₂ := [.ldrSp .x3 152, VG.Impl.Bignum.AArch64.sth .x3 2])
  refine RelCT.seq controlBase_ct (two_taint [.x0] ?_ (by taint_decide))
  intro p s t hs ht r hr
  obtain rfl := List.mem_singleton.mp hr
  exact hs.1.trans ht.1.symm

structure AttemptPointers where
  B : Addr
  F : Addr

def AttemptRegisters (p : AttemptPointers) (s : State) : Prop := s.gpr .x0 = p.B ∧ s.sp = p.F

theorem pAttemptArgs_ct : RelCT isa (Two AttemptRegisters) (.block pAttemptArgs) (fun _ _ => True) :=
  two_taint [.x0] (fun _ _ _ hs ht r hr => by
    obtain rfl := List.mem_singleton.mp hr
    exact hs.1.trans ht.1.symm) (by taint_decide)

end VG.Proof.Dsa.AArch64.Generation

end

end

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
