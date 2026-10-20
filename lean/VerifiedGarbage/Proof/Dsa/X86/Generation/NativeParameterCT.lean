module
public import Aesop.BuiltinRules
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Basic
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Spec.Weierstrass.Point
import VerifiedGarbage.Proof.Dsa.X86.Generation.SearchSlots
public import VerifiedGarbage.Impl.Dsa.X86.Generation.ParameterSearch
public import VerifiedGarbage.Impl.Dsa.X86.Generation.Validate
public import VerifiedGarbage.Proof.Dsa.X86.Generation.ParameterCTState
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.CheckCall
public import VerifiedGarbage.Proof.Dsa.X86.RandomTwo
public import VerifiedGarbage.Proof.Pbkdf2.Stream.X86.Hash
import VerifiedGarbage.Proof.Dsa.X86.Generation.ParameterLoopCT
import VerifiedGarbage.Proof.Dsa.X86.Generation.TapeBlocksCT
import VerifiedGarbage.Proof.Dsa.X86.Generation.TapeControl

/-! # Parameter generation starts at the beginning of the public seed tape -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Proof.Pbkdf2.Stream.X86 VG.Impl.Dsa.X86.Generation

def ParameterStartAt (plen qlen : Nat) (p : ParameterPublic) (s : State) : Prop :=
  (∃ W, SearchContext p.plan W s ∧ W 16 = BitVec.ofNat 32 p.used) ∧
    p.plan.geometry.pLen = plen ∧ p.plan.geometry.qLen = qlen

def parameterStart (p : ParameterPublic) : ParameterPublic := ⟨p.plan, 0, p.used, Nat.zero_le _, p.bound⟩

theorem parameterReset_ct (plen qlen : Nat) : RelCT isa (Two (ParameterStartAt plen qlen))
    (.block (tapeReset seedTape)) (Two fun p => ParameterBefore plen qlen (parameterStart p)) := by
  refine two_piece [.esp] ?_ (tapeReset_check _ (.inl rfl)) ?_
  · intro p s t hs ht r hr
    obtain rfl := List.mem_singleton.mp hr
    obtain ⟨Ws, Rs, _⟩ := hs.1
    obtain ⟨Wt, Rt, _⟩ := ht.1
    exact BitVec.eq_of_toNat_eq (Rs.arena.frame.esp_toNat.trans Rt.arena.frame.esp_toNat.symm)
  · rintro p s ⟨⟨W, R, used⟩, pl, ql⟩
    refine WP.mono (tapeReset_ok R.arena.frame R.representation seedTape (by decide)) fun t ⟨_, Wt, O, K⟩ => ?_
    exact ⟨⟨_, R.slot (by decide) (by decide) Wt O K (by decide), rfl, used⟩, pl, ql⟩

theorem nativeParameterSearch_ct {H : Hash} (K : HashOK H) (F : KeyRandom.CheckCall.CheckFn)
    (plen qlen : Nat) (digest : H.D = qlen) (final : H.F = qlen)
    (hash : ∀ bs, K.SH.H.hash bs = Spec.Dsa.seedHash (8 * qlen) bs)
    (hashSize : ∀ bs, (Spec.Dsa.seedHash (8 * qlen) bs).length = qlen) :
    RelCT isa (Two (ParameterStartAt plen qlen))
      (parameterSearch H plen qlen (finishDomain F.name F.code plen qlen)) (fun _ _ => True) :=
  RelCT.seq (parameterReset_ct plen qlen)
    (two_map parameterStart (fun _ _ h => h) (parameterLoop_ct K F plen qlen digest final hash hashSize))
end VG.Proof.Dsa.X86.Generation
