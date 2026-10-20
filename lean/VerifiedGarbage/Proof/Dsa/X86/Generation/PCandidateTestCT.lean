module
public meta import VerifiedGarbage.Proof.Framework.X86.RelCT
public meta import VerifiedGarbage.Proof.Dsa.X86.Generation.PCandidateGuardCT
public import VerifiedGarbage.Proof.Dsa.X86.Generation.SearchPrimeCT
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.X86.Generation.DrawMemory
public import VerifiedGarbage.Impl.Dsa.X86.Generation.PAttempt
import Mathlib.Tactic.Attr.Core
import VerifiedGarbage.Proof.Dsa.Generation.PDomain
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeometrySeparate
import VerifiedGarbage.Proof.Dsa.X86.Generation.PCandidateGuard
import VerifiedGarbage.Proof.Dsa.X86.Generation.PCandidateGuardCT

/-! # Reject short candidates or apply the public-input primality test -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation VG.Impl.Dsa.Generation.Layout

def PCandidateAt (P : SearchContextPlan) (value used : Nat) (s : State) : Prop :=
  ∃ W, SearchContext P W s ∧ W 16 = BitVec.ofNat 32 used ∧
    Spec.Rsa.bytesAt s.mem (off P.geometry.base p) P.geometry.pLen = Spec.Dsa.encodeBE P.geometry.pLen value

def PCandidateGuarded (P : SearchContextPlan) (value used : Nat) (s : State) : Prop :=
  SearchPrimeAt P P.geometry.pLen value used p s ∧
    s.cf = some (decide (value < 2 ^ (8 * P.geometry.pLen - 1)))

theorem pCandidateGuard_ct (P : SearchContextPlan) (value used : Nat)
    (bound : value < 256 ^ P.geometry.pLen) : RelCT isa (Two fun (_ : Unit) => PCandidateAt P value used)
    (.block (candidatePointer p ++ ([.mov .esi (.mem (frameSlot 22))] : List Instr) ++ candidateWidth))
    (Two fun (_ : Unit) => PCandidateGuarded P value used) := by
  refine two_post (two_map (fun (_ : Unit) => (⟨P.geometry.frameBase, P.saved⟩ : PublicFrame)) ?_ pGuardBlock_ct) ?_
  · rintro _ s ⟨W, R, _, _⟩
    refine ⟨R.arena.frame, ?_⟩
    intro i hi
    obtain rfl := List.mem_singleton.mp hi
    exact (R.representation 5 (by decide)).trans (R.fixed 5 (by decide) (by decide))
  · rintro _ s ⟨W, R, usedValue, bytes⟩
    refine WP.mono (pCandidateGuard_ok R bound bytes) fun t ⟨Rt, cf, O, _⟩ => ?_
    refine ⟨⟨_, Rt, rfl, usedValue, ?_⟩, cf⟩
    have pw := P.geometry.width
    have room : p + P.geometry.pLen ≤ usedBytes P.geometry.pLen := by unfold p usedBytes domainCheck; omega
    rw [drawFrame_bytes O (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact (P.geometry.frame_part room).symm)
      (by omega), bytes, VG.Proof.Dsa.decodeBE_encodeBE bound]

theorem pCandidateTest_ct (P : SearchContextPlan) (value used : Nat)
    (bound : value < 256 ^ P.geometry.pLen) (odd : value % 2 = 1) (usedBound : used ≤ P.witnesses.bytes.length) :
    RelCT isa (Two fun (_ : Unit) => PCandidateAt P value used) (pCandidateTest P.geometry.pLen) (fun _ _ => True) := by
  unfold pCandidateTest
  refine RelCT.seq (pCandidateGuard_ct P value used bound) ?_
  apply two_ite (fun _ _ _ hs ht => by simp only [eval, hs.2, ht.2])
  · refine two_taint [.esp] ?_ (by taint_decide)
    intro u s t hs ht r hr
    obtain rfl := List.mem_singleton.mp hr
    obtain ⟨Ws, Rs, _, _, _⟩ := hs.1.1
    obtain ⟨Wt, Rt, _, _, _⟩ := ht.1.1
    exact BitVec.eq_of_toNat_eq (Rs.arena.frame.esp_toNat.trans Rt.arena.frame.esp_toNat.symm)
  · intro s t ts tt s' t' ⟨u, hs, ht⟩ es et
    have notSmall : ¬ value < 2 ^ (8 * P.geometry.pLen - 1) := by
      have h : decide (value < 2 ^ (8 * P.geometry.pLen - 1)) = false := Option.some.inj (hs.1.2.symm.trans hs.2)
      exact of_decide_eq_false h
    have pw := P.geometry.width
    have upper : value < 2 ^ (8 * P.geometry.pLen) := by rw [Nat.pow_mul]; exact bound
    let D : VG.Proof.Dsa.Generation.PDomain P.geometry.pLen value := ⟨pw, odd, by omega, upper⟩
    have words : P.geometry.pLen % 4 = 0 := by rcases pw with h | h | h <;> rw [h] <;> decide
    exact searchPrime_ct P P.geometry.pLen value used p (by omega) (by omega) words D.bits odd
      (by unfold p usedBytes domainCheck; omega) (by unfold p arithmetic; omega) usedBound
      s t ts tt s' t' ⟨u, hs.1.1, ht.1.1⟩ es et
end VG.Proof.Dsa.X86.Generation
