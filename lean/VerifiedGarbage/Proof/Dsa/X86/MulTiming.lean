module

public import VerifiedGarbage.Impl.Dsa.X86.Arith
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Dsa.X86.StackFrame
public import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Dsa.X86.EntryTiming
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Dsa.X86.CoreSetupTiming
import VerifiedGarbage.Proof.Dsa.X86.ArithmeticTiming
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Traces of the IA-32 DSA product and of its calls

Two runs from the same stack pointer and working space leak the same trace:
the saves read the argument and store through public pointers, and the
context's setup, the product and the restores are checked by taint, which
the values of the numbers do not reach. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Mul
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic
open VG.Impl.Dsa.X86.Arith VG.Proof.Mont.X86.Dynamic

theorem body_relCT (n : Nat) :
    RelCT isa (fun s t => s.gpr .esp = t.gpr .esp ∧ arg s 0 = arg t 0 ∧
      readSrc s (.mem (at_ .esp 4)) = some (arg s 0) ∧
      readSrc t (.mem (at_ .esp 4)) = some (arg t 0))
      (mulBody n) (fun _ _ => True) := by
  unfold mulBody
  have saveCT : RelCT isa (fun s t => s.gpr .esp = t.gpr .esp ∧ arg s 0 = arg t 0 ∧
      readSrc s (.mem (at_ .esp 4)) = some (arg s 0) ∧
      readSrc t (.mem (at_ .esp 4)) = some (arg t 0))
      (.block VG.Impl.Dsa.X86.Pow.save) (VG.X86.Taint.Agree (workspaceTaint false)) := by
    unfold VG.Impl.Dsa.X86.Pow.save
    rw [List.append_assoc]
    exact RelCT.block_append (RelCT.seq (scratchArgument_relCT 0)
      (checkedProgramChange (σ := workspaceTaint false) (hint := .block []) rfl rfl))
  refine RelCT.seq saveCT (RelCT.seq (contextSetup_relCT n) (RelCT.seq (ordinaryMul_relCT n) ?_))
  exact (checkedProgramChange (σ := { regs := .ofList [], flags := false }) (hint := .block []) (by rfl) rfl).mono
    (fun _ _ h => h) (fun _ _ _ => trivial)

theorem body_readArg {n : Nat} {s t : State} {tr : List Leak}
    (E : Exec isa (mulBody n) s tr t) :
    readSrc s (.mem (at_ .esp 4)) = some (arg s 0) := by
  change s.load32 (argAddr s 0) = some (arg s 0)
  unfold State.load32
  split
  · rfl
  · rename_i h
    cases E with
    | seq E _ =>
      cases E with
      | block H =>
        simp only [VG.Impl.Dsa.X86.Pow.save, VG.Impl.Dsa.X86.Pow.slots, List.map_cons, List.map_nil,
          List.cons_append, List.nil_append, execBlock, isa, exec, readSrc, State.load32] at H
        simp only [show s.ea (at_ .esp 4) = argAddr s 0 from rfl, h, ↓reduceIte, Option.map_none] at H
        cases H

theorem framed_relCT (n : Nat) :
    RelCT isa (fun s t => s.gpr .esp = t.gpr .esp ∧ s.gpr .edi = t.gpr .edi ∧ 12 ≤ (s.gpr .esp).toNat)
      (.frame (.push [.eax, .edi]) (.call (mulName n) (mulBody n)) (.pop .eax 2))
      (fun _ _ => True) := by
  refine RelCT.frame (R := fun _ _ => True) (fun _ _ H => H.1) ?_
  rintro _ _ tr ur sf tf ⟨s, t, ⟨SP, DI, fit⟩, rfl, rfl⟩ E F
  cases E with
  | call C E R =>
    cases F with
    | call D F S =>
      rw [call_callEntry, Option.some.injEq] at C D
      subst C D
      have sp : (pushed [Reg.eax, .edi] s).callEntry.gpr .esp =
          (pushed [Reg.eax, .edi] t).callEntry.gpr .esp := by
        rw [callEntry_esp', callEntry_esp', SP]
      have args : arg (pushed [Reg.eax, .edi] s).callEntry 0 =
          arg (pushed [Reg.eax, .edi] t).callEntry 0 := by
        rw [callEntry_arg (rs := [.eax, .edi]) (s := s) fit (by decide) (by decide),
          callEntry_arg (rs := [.eax, .edi]) (s := t) (by rw [← SP]; exact fit) (by decide) (by decide)]
        exact DI
      have traces := (body_relCT n) _ _ _ _ _ _ ⟨sp, args, body_readArg E, body_readArg F⟩ E F
      have r := (ret_gpr R .esp).1
      have q := (ret_gpr S .esp).1
      refine ⟨?_, trivial⟩
      simp only [r, q, State.callEntry_esp, pushed_esp, SP, traces.1]

theorem call_relCT (n : Nat) :
    RelCT isa (fun s t => s.gpr .esp = t.gpr .esp ∧ s.gpr .edi = t.gpr .edi ∧ 12 ≤ (s.gpr .esp).toNat)
      (mulCall n) (fun _ _ => True) := by
  unfold mulCall
  refine RelCT.seq ?_ (framed_relCT n)
  intro s t tr ur sf tf H E F
  have W (s : State) : WP isa (.block [.mov .eax (.imm (BitVec.ofNat 32 (contextBytes n / 8)))]) s
      (fun t => VG.Proof.Mont.X86.Keeps [.eax] s t ∧ t.mem = s.mem) :=
    wp_movS rfl fun _ U _ => WP.block_nil ⟨U.keeps, U.mem⟩
  have K := wp_result (W s) E
  have L := wp_result (W t) F
  refine ⟨?_, ?_⟩
  · cases E with
    | block E => cases F with
      | block F =>
        simp only [execBlock, isa, exec, readSrc, Option.map_some, addrs, srcAddrs, List.map_nil,
          List.nil_append, Option.some.injEq, Prod.mk.injEq] at E F
        exact E.2.symm.trans F.2
  · dsimp only
    rw [K.1.1 .esp (by decide), L.1.1 .esp (by decide), K.1.1 .edi (by decide), L.1.1 .edi (by decide)]
    exact ⟨H.1, H.2.1, H.2.2⟩

end VG.Proof.Dsa.X86.Mul
