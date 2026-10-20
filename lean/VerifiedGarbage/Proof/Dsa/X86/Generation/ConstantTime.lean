module
public meta import VerifiedGarbage.Proof.Framework.X86.RelCT
public meta import VerifiedGarbage.Proof.Dsa.X86.Generation.EntryInnerCT
public import Aesop.BuiltinRules
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Basic
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.Weierstrass.Point
public import VerifiedGarbage.Impl.Dsa.X86.Generation.Entry
public import VerifiedGarbage.Proof.Dsa.X86.Generation.Hashes
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.CheckCall
import VerifiedGarbage.Proof.Dsa.X86.Generation.AllocationCT
import VerifiedGarbage.Proof.Dsa.X86.Generation.EntryInnerCT
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # The complete x86 parameter generator meets its declared public leakage contract -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

theorem saveRegisters_ct : RelCT isa (fun s t => s.gpr .esp = t.gpr .esp) (.block saveRegisters) (fun _ _ => True) := by
  apply (two_taint [.esp] (Φ := fun (sp : BitVec 32) s => s.gpr .esp = sp)
    (by intro sp s t hs ht r hr; obtain rfl := List.mem_singleton.mp hr; exact hs.trans ht.symm)
    (by taint_decide)).mono
  · intro s t h; exact ⟨s.gpr .esp, rfl, h.symm⟩
  · intro _ _ h; exact h

theorem restoreRegisters_ct : RelCT isa (fun s t => s.gpr .esp = t.gpr .esp) (.block restoreRegisters) (fun _ _ => True) := by
  apply (two_taint [.esp] (Φ := fun (sp : BitVec 32) s => s.gpr .esp = sp)
    (by intro sp s t hs ht r hr; obtain rfl := List.mem_singleton.mp hr; exact hs.trans ht.symm)
    (by taint_decide)).mono
  · intro s t h; exact ⟨s.gpr .esp, rfl, h.symm⟩
  · intro _ _ h; exact h

theorem generation_constantTime (H : GenerationHashes) (F : KeyRandom.CheckCall.CheckFn) :
    ConstantTime isa (Spec.Dsa.generateParametersContract abi 292).pre
      (Spec.Dsa.generateParametersContract abi 292).pub (code H.sha1 H.sha256 F.name F.code) := by
  intro s t tsa tsb u v hs ht hpub ea eb
  have A := parameterABI_of hs
  have B := parameterABI_of ht
  have pub := generation_public_related hpub
  unfold code at ea eb
  cases ea with
  | frame pa ba _ =>
    cases eb with
    | frame pb bb _ =>
      rw [allocated_push (by decide) (by have := A.stackLow; omega : 16 ≤ (s.gpr .esp).toNat), Option.some.injEq] at pa
      rw [allocated_push (by decide) (by have := B.stackLow; omega : 16 ≤ (t.gpr .esp).toNat), Option.some.injEq] at pb
      subst pa pb
      cases ba with | seq sa restA => cases restA with | seq ia ra =>
      cases bb with | seq sb restB => cases restB with | seq ib rb =>
      have saveTrace := (saveRegisters_ct _ _ _ _ _ _ (by change s.gpr .esp - 16#32 = t.gpr .esp - 16#32; rw [pub.sp]) sa sb).1
      obtain ⟨_, _, Oa, Ka⟩ := wp_result (saveRegisters_ok A.outerFrame) sa
      obtain ⟨_, _, Ob, Kb⟩ := wp_result (saveRegisters_ok B.outerFrame) sb
      have inner := entryInner_ct H F A B pub Oa Ka Ob Kb ia ib
      have restoreTrace := (restoreRegisters_ct _ _ _ _ _ _ inner.2 ra rb).1
      simp only [addrs, List.map_nil, List.nil_append, List.append_nil]
      rw [saveTrace, inner.1, restoreTrace]
end VG.Proof.Dsa.X86.Generation
