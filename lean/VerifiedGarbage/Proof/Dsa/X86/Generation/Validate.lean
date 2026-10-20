module
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Basic
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Spec.Weierstrass.Point
import VerifiedGarbage.Proof.Mont.X86.Instr
public import Aesop.BuiltinRules
public import VerifiedGarbage.Impl.Dsa.X86.Generation.Validate
public import VerifiedGarbage.Proof.Dsa.X86.Generation.SearchContext
public import VerifiedGarbage.Proof.Dsa.X86.Generation.ValidateCall
import Mathlib.Tactic.Attr.Core
import VerifiedGarbage.Proof.Dsa.X86.Generation.SearchSlots
import VerifiedGarbage.Proof.Dsa.X86.Generation.ValidateFrame

/-! # Map the domain checker's public result to the seed-search status -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

def validateStatusWrites (G : GenerationGeometry) : List Region :=
  validateWrites G ++ [⟨G.frameBase, VG.Impl.Dsa.X86.Generation.frameBytes⟩]

theorem validate_ok (F : KeyRandom.CheckCall.CheckFn) {P : SearchContextPlan} {W : Nat → BitVec 32} {s : State}
    (R : SearchContext P W s) :
    WP isa (validate F.name F.code P.geometry.pLen P.geometry.qLen) s fun t =>
      SearchContext P (frameUpdate W 19 (if validateResult P.geometry s.mem then 1 else 3)) t ∧
      Frame (validateStatusWrites P.geometry) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .esi, .edi, .ebp] s t := by
  have parent : s.mem.readW (off P.geometry.frameBase 20) 32 = P.geometry.parent :=
    (R.representation 5 (by decide)).trans ((R.fixed 5 (by decide) (by decide)).trans P.parent)
  unfold validate
  refine WP.seq (WP.mono (validateArgs_ok R.arena parent) fun a ⟨regs, mem, Ka⟩ => ?_)
  refine WP.seq (WP.mono (validateFrame_ok F (R.congr mem Ka (by decide)) regs) fun b ⟨Rb, ax, Ob, Kb⟩ => ?_)
  rw [mem] at ax Ob
  refine WP.seq (wp_cmpi fun c bc _ zf => WP.block_nil ?_)
  have Rc := Rb.congr bc.mem (bc.keeps []) (by decide)
  have Oc : Frame (validateStatusWrites P.geometry) s.mem c.mem := by
    rw [bc.mem]
    exact Ob.mono (by intro r hr; exact List.mem_append_left _ hr)
  have Kc : Keeps [.eax, .ebx, .ecx, .edx, .esi, .edi, .ebp] s c :=
    ((Ka.mono (by decide)).trans (Kb.mono (by decide))).trans (bc.keeps _)
  cases good : validateResult P.geometry s.mem with
  | false =>
    refine WP.ite true (by simp [eval, zf, ax, good]) (fun _ => ?_) (fun h => Bool.noConfusion h)
    refine WP.mono (searchStatus_ok Rc 3) fun t ⟨Rt, Ot, Kt⟩ => ?_
    exact ⟨Rt, Oc.trans (Ot.mono (by intro r hr; exact List.mem_append_right _ hr)), Kc.trans (Kt.mono (by decide))⟩
  | true =>
    refine WP.ite false (by simp [eval, zf, ax, good]) (fun h => Bool.noConfusion h) (fun _ => ?_)
    refine WP.mono (searchStatus_ok Rc 1) fun t ⟨Rt, Ot, Kt⟩ => ?_
    exact ⟨Rt, Oc.trans (Ot.mono (by intro r hr; exact List.mem_append_right _ hr)), Kc.trans (Kt.mono (by decide))⟩
end VG.Proof.Dsa.X86.Generation
