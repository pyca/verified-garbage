module
public import VerifiedGarbage.Proof.RsaOaep.X86_64.CtBase
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Output
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Context

import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextSuccess
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.OnSuccess
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
public import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
public import Mathlib.Tactic.ToAdditive
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.RsaKeyGen.Hdr
import VerifiedGarbage.Proof.RsaKeyGen.Slots
import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Lit
import VerifiedGarbage.TCB.Registration
meta import VerifiedGarbage.Proof.RsaOaep.X86_64.CtBase
meta import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Output
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Context
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextSuccess
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.OnSuccess
meta import Mathlib.Order.RelClasses
meta import Mathlib.Tactic.Finiteness.Attr
meta import Mathlib.Tactic.Push
meta import Mathlib.Tactic.Attr.Core
meta import Aesop.BuiltinRules
meta import Mathlib.Tactic.ToAdditive
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.RsaKeyGen.Hdr
meta import VerifiedGarbage.Proof.RsaKeyGen.Slots
meta import VerifiedGarbage.Proof.RsaKeyGen.Table
meta import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Lit
meta import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Lit
meta import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Lit
meta import VerifiedGarbage.TCB.Registration

/-! # Output copying and failure zeroing use public frame inputs -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Proof.MlKem.X86_64

structure OutputPublic where
  context : GenerationContext
  accepted : Bool
  ws : List Region

def OutputBefore (n : Nat) (p : OutputPublic) (s : State) : Prop :=
  (∃ W, GenerationMemory p.context W s ∧ (W 19 == 1) = p.accepted) ∧ FrV n p.context.geo.F p.ws s

def OutputPublic.words (p : OutputPublic) : Nat → BitVec 64 := p.context.saved

theorem output_frame {n : Nat} {p : OutputPublic} {s : State} (h : OutputBefore n p s) :
    FrV n p.context.geo.F p.ws s ∧
    ∀ k ∈ [5, 6, 7], word s.mem p.context.geo.F (8 * k) = p.words k := by
  obtain ⟨⟨W, hm, _⟩, hf⟩ := h
  obtain ⟨V, R⟩ := hm.rep
  refine ⟨hf, fun k hk => ?_⟩
  have bound : k < 37 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hk; omega
  rw [R.fr k bound]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · simpa [OutputPublic.words, upd] using hm.slots 5 (by simp [generationSlots])
  · simpa [OutputPublic.words, upd] using hm.slots 6 (by simp [generationSlots])
  · simpa [OutputPublic.words, upd] using hm.slots 7 (by simp [generationSlots])

theorem output_pins (n : Nat) : Pins (OutputBefore n) [.rsp] := by
  intro p s t ⟨⟨Ws, hs, _⟩, _⟩ ⟨⟨Wt, ht, _⟩, _⟩ r hr
  obtain rfl := List.mem_singleton.mp hr
  exact hs.layout.rsp.trans ht.layout.rsp.symm

theorem output_check {n : Nat} {p : OutputPublic} {s : State} (h : OutputBefore n p s) :
    WP isa (.block Impl.Dsa.X86_64.Generation.successStatus) s
      (fun t => OutputBefore n p t ∧ isa.eval .e t = some p.accepted) := by
  obtain ⟨⟨W, hm, hs⟩, hf⟩ := h
  obtain ⟨V, R⟩ := hm.rep
  refine WP.mono (successStatus_ok hm.layout R) fun t ⟨hz, he, hk⟩ => ?_
  exact ⟨⟨⟨W, hm.congr he hk, hs⟩, hf.congr (hk.gpr (by decide)) hk.2.2⟩,
    by simp only [eval, hz, hs]⟩

theorem outputCopy_ct (n : Nat) (hn : n = 2 ∨ n = 3) :
    RelCT isa (Two (OutputBefore n)) Impl.Dsa.X86_64.Generation.outputCopy (fun _ _ => True) := by
  refine two_taintF [] [5, 6, 7] (fun p => p.context.geo.F) OutputPublic.ws OutputPublic.words
    (fun _ _ h => output_frame h) (by intro _ _ _ _ _ r hr; simp at hr) (by decide) ?_
  rcases hn with rfl | rfl
  all_goals exact ⟨_, by taint_decide⟩

theorem outputZero_ct (n : Nat) (hn : n = 2 ∨ n = 3) :
    RelCT isa (Two (OutputBefore n)) Impl.Dsa.X86_64.Generation.outputZero (fun _ _ => True) := by
  refine two_taintF [] [5, 6, 7] (fun p => p.context.geo.F) OutputPublic.ws OutputPublic.words
    (fun _ _ h => output_frame h) (by intro _ _ _ _ _ r hr; simp at hr) (by decide) ?_
  rcases hn with rfl | rfl
  all_goals exact ⟨_, by taint_decide⟩

theorem finishOutput_ct (n : Nat) (hn : n = 2 ∨ n = 3) :
    RelCT isa (Two (OutputBefore n)) Impl.Dsa.X86_64.Generation.finishOutput (fun _ _ => True) := by
  refine RelCT.seq (two_piece [.rsp] (output_pins n) (by taint_decide)
    (fun _ _ h => output_check h)) ?_
  refine two_ite (fun _ _ _ hs ht => hs.2.trans ht.2.symm) ?_ ?_
  · exact two_map (fun p : OutputPublic => p) (fun _ _ h => h.1.1) (outputCopy_ct n hn)
  · exact two_map (fun p : OutputPublic => p) (fun _ _ h => h.1.1) (outputZero_ct n hn)

end VG.Proof.Dsa.X86_64.Generation
