module
public meta import VerifiedGarbage.Proof.Framework.X86.RelCT
public meta import VerifiedGarbage.Proof.Dsa.X86.Generation.PSearchLoopCT
public import Aesop.BuiltinRules
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Basic
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.Weierstrass.Point
import VerifiedGarbage.Proof.Dsa.X86.Generation.PSearchStable
import VerifiedGarbage.Proof.Dsa.X86.Generation.BufferArgs
public import VerifiedGarbage.Proof.Dsa.X86.Generation.AttemptOffsetCT
import VerifiedGarbage.Proof.Dsa.X86.Generation.SearchControl

/-! # Initialize the public p-search controller while preserving the accepted q -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

def PSearchStartAt (P : PSearchPlan) (used : Nat) (s : State) : Prop :=
  ∃ W, PSearchMemory P W s ∧ W 16 = BitVec.ofNat 32 used

def PSearchInitAt (P : PSearchPlan) (used : Nat) (s : State) : Prop :=
  PSearchStartAt P used s ∧ s.gpr .edi = P.context.geometry.pointer VG.Impl.Dsa.Generation.Layout.control

theorem pSearchControl_ct (P : PSearchPlan) (used : Nat) : RelCT isa
    (Two fun (_ : Unit) => PSearchStartAt P used) (.block controlBase)
    (Two fun (_ : Unit) => PSearchInitAt P used) := by
  refine two_piece [.esp] ?_ (by taint_decide) ?_
  · rintro _ s t ⟨Ws, Rs, _⟩ ⟨Wt, Rt, _⟩ r hr
    obtain rfl := List.mem_singleton.mp hr
    exact BitVec.eq_of_toNat_eq (Rs.context.arena.frame.esp_toNat.trans Rt.context.arena.frame.esp_toNat.symm)
  · rintro _ s ⟨W, R, cursor⟩
    have parent : s.mem.readW (off P.context.geometry.frameBase 20) 32 = P.context.geometry.parent :=
      (R.context.representation 5 (by decide)).trans ((R.context.fixed 5 (by decide) (by decide)).trans P.context.parent)
    refine WP.mono (bufferPointer_ok R.context.arena.frame parent .edi _) fun t ⟨di, mem, K⟩ => ?_
    exact ⟨⟨W, ⟨R.context.congr mem K (by decide),
      R.seed.keep (by rw [mem]; exact Frame.refl [] s.mem) (by simp) K,
      R.source, by rw [mem]; exact R.qval, R.seedUsed⟩, cursor⟩, di⟩

theorem pSearchInit_ct (P : PSearchPlan) (used : Nat) : RelCT isa
    (Two fun (_ : Unit) => PSearchInitAt P used) (.block pSearchInit)
    (Two fun (_ : Unit) => PAttemptAt P 0 used) := by
  refine two_piece [.edi] ?_ (by taint_decide) ?_
  · intro _ s t hs ht r hr
    obtain rfl := List.mem_singleton.mp hr
    exact hs.2.trans ht.2.symm
  · rintro _ s ⟨⟨W, R, cursor⟩, di⟩
    have S := R.context.arena.controlScr di
    refine WP.mono (pSearchInit_ok S (by decide)) fun t ⟨count, offset, O, K⟩ => ?_
    have Rt := R.control (O.mono (by omega) (by omega)) (K.mono (by decide))
    exact ⟨⟨W, Rt, cursor⟩, ⟨S.of_keeps K (by decide), count, by simpa using offset⟩⟩
end VG.Proof.Dsa.X86.Generation
