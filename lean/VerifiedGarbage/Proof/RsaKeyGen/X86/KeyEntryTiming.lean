module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyEntry
public import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.KernelRfl

/-! # Copying the eighteen native key arguments has a public address trace -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyArgs
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Impl.RsaKeyGen.X86.CandidateArgs

def EntryPair (base : Addr) (size : Nat) (p : BitVec 32) (inputs : Nat → BitVec 32) (s t : State) : Prop :=
  Entry base size p inputs s ∧ Entry base size p inputs t

theorem pointer_ok {base : Addr} {size : Nat} {p : BitVec 32} {inputs : Nat → BitVec 32} {s : State}
    (S : Entry base size p inputs s) :
    WP isa (.block [.mov .edi (.mem (arg 16))]) s fun t => t.gpr .edi = inputs 16 ∧ Keeps [.edi] s t := by
  refine wp_movS (S.read 16 (by decide)) fun t T _ => WP.block_nil ⟨T.gpr, T.keeps⟩

theorem pointer_trace {base : Addr} {size : Nat} {p : BitVec 32} {inputs : Nat → BitVec 32} :
    RelCT isa (EntryPair base size p inputs) (.block [.mov .edi (.mem (arg 16))])
      (VG.X86.Taint.Agree (τr [.esp, .edi])) := by
  intro s t tr ur u v ⟨S, T⟩ A C
  have raw : RelCT isa (VG.X86.Taint.Agree (τr [.esp])) (.block [.mov .edi (.mem (arg 16))])
      (VG.X86.Taint.Agree (τr [.esp])) := checkedBlockInvariant rfl rfl
  have start : VG.X86.Taint.Agree (τr [.esp]) s t := agree_regs (by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact S.sp.trans T.sp.symm)
  obtain ⟨leftValue, leftKeeps⟩ := wp_result (pointer_ok S) A
  obtain ⟨rightValue, rightKeeps⟩ := wp_result (pointer_ok T) C
  refine ⟨(raw _ _ _ _ _ _ start A C).1, agree_regs ?_⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [leftKeeps.1 .esp (by decide), rightKeeps.1 .esp (by decide)]
    exact S.sp.trans T.sp.symm
  · exact leftValue.trans rightValue.symm

theorem enter_trace {base : Addr} {size : Nat} {p : BitVec 32} {inputs : Nat → BitVec 32} :
    RelCT isa (EntryPair base size p inputs) VG.Impl.RsaKeyGen.X86.Key.enter (fun _ _ => True) := by
  have copied : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi])) (copies 18) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (τr [.esp, .edi]) (fun _ _ H => H)
      (hc := VG.Taint.hintOf taint (τr [.esp, .edi]) (copies 18))
    kernel_rfl
  exact RelCT.seq pointer_trace copied

end VG.Proof.RsaKeyGen.X86.KeyArgs
