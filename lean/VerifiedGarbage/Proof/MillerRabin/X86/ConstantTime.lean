module

public import VerifiedGarbage.Impl.MillerRabin.X86.Round
public import VerifiedGarbage.Proof.MillerRabin.X86.Baseline
public import VerifiedGarbage.Proof.MillerRabin.X86.Entry
public import VerifiedGarbage.Proof.MillerRabin.X86.TimingBlocks
public import VerifiedGarbage.Proof.MillerRabin.Contract
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.MillerRabin.X86.TimingEntry
import VerifiedGarbage.Proof.MillerRabin.X86.TimingCore
import VerifiedGarbage.Proof.MillerRabin.X86.TimingPointers
import VerifiedGarbage.Proof.MillerRabin.X86.MontInstance
import VerifiedGarbage.Proof.Mont.X86.Sse2.PreparedVerified
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.X86.RelCT

/-! # Callable i686 Miller–Rabin is constant time under the reviewed contract -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.MillerRabin.X86 VG.Proof.Dsa.X86

theorem publicInputs {s t : State}
    (H : (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96).pub s t) :
    s.gpr .esp = t.gpr .esp ∧ arg s 0 = arg t 0 ∧ arg s 1 = arg t 1 ∧
      Proof.Rsa.Mont.wOf s.mem (wsOf s) = Proof.Rsa.Mont.wOf t.mem (wsOf t) := by
  sig_pub [Proof.MillerRabin.Round.roundContract, Proof.MillerRabin.Round.roundSig, abi, argSlots, argVal, argBytes] at H
  sig_split H
  refine ⟨by with_reducible assumption, by with_reducible assumption, by with_reducible assumption, ?_⟩
  apply List.singleton_inj.mp
  with_reducible assumption

theorem baseLoad_trace : RelCT isa (VG.X86.Taint.Agree (roundTaint []))
    (.block [.mov .edi (.mem (at_ .esp 20))]) (VG.X86.Taint.Agree (roundTaint [])) :=
  checkedBlockInvariant rfl rfl

theorem restore_trace : RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi]))
    (.block VG.Impl.Mont.X86.Compact.restoreRegs) (VG.X86.Taint.Agree (roundTaint [])) :=
  checkedProgramChange (hint := .block []) (τ' := roundTaint []) rfl rfl

private theorem pair_of_context {g : Geometry} {s t : State}
    (S : Context g s) (T : Context g t) (sp : s.gpr .esp = t.gpr .esp) : Pair g [.edi] s t := by
  refine ⟨S, T, agree_regs ?_⟩
  intro r mem
  change r ∈ [.esp, .edi] at mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl
  · exact sp
  · exact ptr_agree S.base T.base

theorem constantTime : ConstantTime isa
    (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96).pre
    (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96).pub (code montName montCode) := by
  apply RelCT.constantTime
  unfold code
  refine VG.X86.RelCT.frame (rs := Compact.savedRegisters) (R := fun _ _ => True)
    (fun _ _ H => (publicInputs H.2.2).1) ?_
  rintro a b tr ur u z ⟨s, t, H, rfl, rfl⟩ E G
  have S := entry_of H.1
  have T := entry_of H.2.1
  obtain ⟨sp, a0, a1, width⟩ := publicInputs H.2.2
  have geo := geometry_eq a0 a1 width
  have enteredSp : (entered s).gpr .esp = (entered t).gpr .esp := by
    rw [entered, entered, Compact.entered, Compact.entered, pushed_esp, pushed_esp, sp]
  cases E with
  | seq bodyS restoreS =>
    cases G with
    | seq bodyT restoreT =>
      cases bodyS with
      | seq loadS coreS =>
        cases bodyT with
        | seq loadT coreT =>
          have baseAgree : VG.X86.Taint.Agree (roundTaint []) (entered s) (entered t) := agree_regs (by
            intro r mem
            change r ∈ [.esp] at mem
            obtain rfl := List.mem_singleton.mp mem
            exact enteredSp)
          have baseTrace := (baseLoad_trace _ _ _ _ _ _ baseAgree loadS loadT).1
          obtain ⟨startS, keepS⟩ := wp_result S.base loadS
          obtain ⟨startT, keepT⟩ := wp_result T.base loadT
          have startT' := startT
          rw [← geo, ← a1, ← enteredSp] at startT'
          have pair := pair_of_context startS.1.data.context startT'.1.data.context (by
            rw [keepS.1 .esp (by decide), keepT.1 .esp (by decide)]
            exact enteredSp)
          obtain ⟨coreTrace, after⟩ := core_trace VG.Proof.Mont.X86.Sse2.prepared_verified compact_noSp compact_stack S.valid
            (by change (arg s 1).toNat * 8 = 8 * (arg s 1).toNat; omega) _ _ _ _ _ _
            ⟨pair, ⟨entrySecret s, startS⟩, ⟨entrySecret t, startT'⟩⟩ coreS coreT
          have restoreTrace := (restore_trace _ _ _ _ _ _ after restoreS restoreT).1
          exact ⟨by rw [baseTrace, coreTrace, restoreTrace], trivial⟩

end VG.Proof.MillerRabin.X86
