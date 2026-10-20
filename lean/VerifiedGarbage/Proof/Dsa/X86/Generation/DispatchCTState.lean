module
public meta import VerifiedGarbage.Proof.Framework.X86.RelCT
public meta import VerifiedGarbage.Proof.Dsa.X86.Generation.Hashes
public meta import VerifiedGarbage.Proof.Dsa.X86.Generation.GenerateCT
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Basic
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.Weierstrass.Point
import VerifiedGarbage.Proof.Mont.X86.Instr
public import Aesop.BuiltinRules
public import VerifiedGarbage.Proof.Dsa.X86.Generation.SearchStorage
public import VerifiedGarbage.Proof.Dsa.X86.RandomTwo

/-! # Width dispatch preserves search storage and compares only a public length -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

def DispatchBefore (P : SearchContextPlan) (s : State) : Prop := ∃ W, SearchStorage P W s ∧ W 16 = 0

def DispatchChecked (len : Nat) (P : SearchContextPlan) (s : State) : Prop :=
  DispatchBefore P s ∧ s.gpr .eax = BitVec.ofNat 32 P.geometry.pLen ∧
    eval .e s = some ((BitVec.ofNat 32 P.geometry.pLen - BitVec.ofNat 32 len) == 0)

theorem dispatchBefore_congr {P : SearchContextPlan} {s t : State}
    (h : DispatchBefore P s) (mem : t.mem = s.mem) (K : Keeps [.eax] s t) : DispatchBefore P t := by
  obtain ⟨W, R, cursor⟩ := h
  exact ⟨W, R.keep (by rw [mem]; exact Frame.refl _ _) K (by decide), cursor⟩

theorem dispatch_check : RelCT isa (Two DispatchBefore)
    (.block [.mov .eax (.mem (frameSlot 17)), .alu .cmp .eax (.imm 128)]) (Two (DispatchChecked 128)) := by
  refine two_piece [.esp] ?_ (by taint_decide) ?_
  · rintro p s t ⟨Ws, Rs, _⟩ ⟨Wt, Rt, _⟩ r hr
    obtain rfl := List.mem_singleton.mp hr
    exact BitVec.eq_of_toNat_eq (Rs.arena.frame.esp_toNat.trans Rt.arena.frame.esp_toNat.symm)
  · intro P s H
    obtain ⟨W, R, cursor⟩ := H
    have len := (R.fixed 17 (by decide) (by decide)).trans P.pLength
    refine wp_movS (R.arena.frame.readWord R.representation (by decide : 17 < 37)) fun a sa _ =>
      wp_cmpi fun t ab _ zf => WP.block_nil ?_
    exact ⟨dispatchBefore_congr ⟨W, R, cursor⟩ (ab.mem.trans sa.mem) (sa.keeps.trans (ab.keeps _)),
      by rw [ab.gpr, sa.gpr, len], by change t.zf = _; rw [zf, sa.gpr, len]; rfl⟩

def DispatchLarge (P : SearchContextPlan) (s : State) : Prop :=
  DispatchBefore P s ∧ s.gpr .eax = BitVec.ofNat 32 P.geometry.pLen ∧ P.geometry.pLen ≠ 128

def DispatchLargeChecked (P : SearchContextPlan) (s : State) : Prop :=
  DispatchChecked 256 P s ∧ P.geometry.pLen ≠ 128

theorem dispatch_check256 : RelCT isa (Two DispatchLarge) (.block [.alu .cmp .eax (.imm 256)])
    (Two DispatchLargeChecked) := by
  refine two_piece [.eax] ?_ (by taint_decide) ?_
  · intro p s t hs ht r hr
    obtain rfl := List.mem_singleton.mp hr
    exact hs.2.1.trans ht.2.1.symm
  · rintro P s ⟨H, ax, large⟩
    refine wp_cmpi fun t st _ zf => WP.block_nil ?_
    exact ⟨⟨dispatchBefore_congr H st.mem (st.keeps _), by rw [st.gpr, ax],
      by change t.zf = _; rw [zf, ax]; rfl⟩, large⟩
end VG.Proof.Dsa.X86.Generation
