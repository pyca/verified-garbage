module
public meta import VerifiedGarbage.Proof.Framework.X86.RelCT
public meta import VerifiedGarbage.Proof.Dsa.X86.Generation.ParameterAnswerCT
public import Aesop.BuiltinRules
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Basic
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.Weierstrass.Point
public import VerifiedGarbage.Impl.Dsa.X86.Generation.ParameterSearch
public import VerifiedGarbage.Impl.Dsa.X86.Generation.Validate
public import VerifiedGarbage.Proof.Dsa.X86.Generation.ParameterCTState
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.CheckCall
public import VerifiedGarbage.Proof.Dsa.X86.RandomTwo
public import VerifiedGarbage.Proof.Pbkdf2.Stream.X86.Hash
import VerifiedGarbage.Proof.Dsa.X86.Generation.ParameterAnswerCT
import VerifiedGarbage.Proof.Dsa.X86.Generation.TapeBlocksCT

/-! # A seed tape iteration has a trace fixed by public cursor and candidate data -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

theorem parameter_check_ct (plen qlen : Nat) : RelCT isa (Two (ParameterBefore plen qlen))
    (.block (chunkCheck seedTape qlen)) (Two (ParameterChecked plen qlen)) := by
  refine two_piece [.esp] ?_ (chunkCheck_check _ qlen (.inl rfl)) (fun _ _ H => parameter_check H)
  intro p s t hs ht r hr
  obtain rfl := List.mem_singleton.mp hr
  obtain ⟨Ws, Rs, _, _⟩ := hs.1
  obtain ⟨Wt, Rt, _, _⟩ := ht.1
  exact BitVec.eq_of_toNat_eq (Rs.arena.frame.esp_toNat.trans Rt.arena.frame.esp_toNat.symm)

theorem parameter_take_ct (plen qlen : Nat) : RelCT isa (Two (ParameterAvailable plen qlen))
    (.block (tapeTake seedTape qlen)) (Two (ParameterTaken plen qlen)) := by
  refine two_piece [.esp] ?_ (tapeTake_check _ qlen (.inl rfl)) (fun _ _ H => parameter_take H)
  intro p s t hs ht r hr
  obtain rfl := List.mem_singleton.mp hr
  obtain ⟨Ws, Rs, _, _⟩ := hs.1.1
  obtain ⟨Wt, Rt, _, _⟩ := ht.1.1
  exact BitVec.eq_of_toNat_eq (Rs.arena.frame.esp_toNat.trans Rt.arena.frame.esp_toNat.symm)

open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Proof.Pbkdf2.Stream.X86

theorem parameterIteration_ct {H : Hash} (K : HashOK H) (F : KeyRandom.CheckCall.CheckFn)
    (plen qlen : Nat) (digest : H.D = qlen) (final : H.F = qlen)
    (hash : ∀ bs, K.SH.H.hash bs = Spec.Dsa.seedHash (8 * qlen) bs)
    (hashSize : ∀ bs, (Spec.Dsa.seedHash (8 * qlen) bs).length = qlen) : RelCT isa (Two (ParameterBefore plen qlen))
    (tapeIteration seedTape qlen (parameterBody H plen qlen (finishDomain F.name F.code plen qlen))) (fun _ _ => True) := by
  unfold tapeIteration
  refine RelCT.seq (parameter_check_ct plen qlen) ?_
  apply two_ite (fun _ _ _ hs ht => by simp only [eval, hs.2, ht.2])
  · refine two_taint [.esp] ?_ (by taint_decide)
    intro p s t hs ht r hr
    obtain rfl := List.mem_singleton.mp hr
    obtain ⟨Ws, Rs, _, _⟩ := hs.1.1.1
    obtain ⟨Wt, Rt, _, _⟩ := ht.1.1.1
    exact BitVec.eq_of_toNat_eq (Rs.arena.frame.esp_toNat.trans Rt.arena.frame.esp_toNat.symm)
  · refine RelCT.seq ((parameter_take_ct plen qlen).mono
      (fun _ _ => two_mono (fun _ _ h => parameter_available h.1 h.2)) (fun _ _ h => h))
      (RelCT.seq (parameter_answer_ct K F plen qlen digest final hash hashSize) ?_)
    refine two_taint [.esp] ?_ (by taint_decide)
    intro p s t hs ht r hr
    obtain rfl := List.mem_singleton.mp hr
    obtain ⟨_, Ws, _, Rs, _⟩ := hs.1
    obtain ⟨_, Wt, _, Rt, _⟩ := ht.1
    exact BitVec.eq_of_toNat_eq (Rs.arena.frame.esp_toNat.trans Rt.arena.frame.esp_toNat.symm)
end VG.Proof.Dsa.X86.Generation
