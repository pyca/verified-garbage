module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchBody
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchControlCT
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchCTState
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Data.Int.ModEq

/-! # A completed p attempt returns a public status and next witness cursor -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MillerRabin.X86_64
open VG.Proof.Pbkdf2.Md.X86_64 VG.Proof.RsaOaep.X86_64

def SearchPublic.result (p : SearchPublic) : Option (Bool × List Byte) :=
  p.plan.stepResult p.counter p.used

def SearchPublic.status (p : SearchPublic) : Nat :=
  match p.result with
  | none => 0
  | some (b, _) => if b then 1 else 3

def SearchPublic.nextUsed (p : SearchPublic) : Nat :=
  match p.result with
  | none => p.used
  | some (_, rest) => p.plan.attempt.rand.length - rest.length

def SearchPublic.control (p : SearchPublic) : SearchControlPublic where
  B := p.plan.C
  counter := p.counter
  stride := p.plan.attempt.construct.hash.count + 1
  status := p.status
  statusBound := by unfold SearchPublic.status; split; decide; split <;> decide

structure SearchBodyAfter (n : Nat) (p : SearchPublic) (s : State) : Prop where
  memory : ∃ W, SearchMemory p.plan W s ∧
    (p.status = 3 → W 16 = BitVec.ofNat 64 p.nextUsed ∧ p.nextUsed ≤ p.plan.attempt.rand.length)
  control : SearchControlBefore p.control s
  frame : FrV n p.plan.attempt.construct.hash.F p.ws s
  wr : s.wr = p.wr

theorem searchBody_ready (G1 G256 : Impl.Pbkdf2.Md.X86_64.Stream)
    (M : Mont) (K : Kernel) {n pLen qLen : Nat} {H : Spec.Mgf1.Hash}
    (hG : Calls.StreamOK (if qLen = 20 then G1 else G256))
    (hmatch : ∀ x, H.hash x = hG.SH.H.hash x)
    (hsize : ∀ x, (H.hash x).length = (if qLen = 20 then G1 else G256).D)
    (hhash : ∀ bs, H.hash bs = Spec.Dsa.seedHash (8 * qLen) bs)
    (hseedsize : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * qLen) bs).length = 8 * qLen)
    (hd : (if qLen = 20 then G1 else G256).D = qLen) {p : SearchPublic} {s : State}
    (h : SearchBefore n pLen qLen p s) :
    WP isa (Impl.Dsa.X86_64.Generation.pAttempt G1 G256 M.mm K.run pLen qLen) s (SearchBodyAfter n p) := by
  obtain ⟨⟨W, hs, hu⟩, ctrl, frame, wr, ub, hp, hq⟩ := h
  subst qLen
  have step := searchBody_ok hG hmatch hsize M K hd hhash hseedsize hs ctrl p.bound hu ub
  rw [hp] at step
  refine WP.mono step fun t ⟨ct, W', used, status, memory, bound, wordUsed, _, wordStatus,
    _, _, exhausted, result, _, _, wrt⟩ => ?_
  have statusEq : status = BitVec.ofNat 64 p.status := by
    cases hr : p.result with
    | none => exact (exhausted hr).trans (by simp [SearchPublic.status, hr])
    | some pair =>
      obtain ⟨b, rest⟩ := pair
      exact (result b rest hr).1.trans (by simp [SearchPublic.status, hr])
  refine ⟨⟨W', memory, ?_⟩, ⟨ct, wordStatus.trans statusEq⟩,
    frame.congr (memory.layout.rsp.trans hs.layout.rsp.symm) wrt, wrt.trans wr⟩
  intro retry
  cases hr : p.result with
  | none => simp [SearchPublic.status, hr] at retry
  | some pair =>
    obtain ⟨b, rest⟩ := pair
    have usedEq : used = p.nextUsed := by simpa only [SearchPublic.nextUsed, hr] using (result b rest hr).2
    exact ⟨usedEq ▸ wordUsed, usedEq ▸ bound⟩

end VG.Proof.Dsa.X86_64.Generation
