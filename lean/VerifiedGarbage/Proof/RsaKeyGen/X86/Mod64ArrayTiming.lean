module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Mod64Array
public import VerifiedGarbage.Proof.RsaKeyGen.X86.Mod64ArrayContext
public import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.RsaKeyGen.X86.Mod64ArrayInit
import VerifiedGarbage.Proof.RsaKeyGen.X86.Mod64ArrayLoopTiming
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.KernelRfl

/-! # Complete candidate reduction preserves timing privacy for all candidate values -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Mod64
open VG VG.X86 VG.Proof.Dsa.X86 VG.Impl.RsaKeyGen.X86.Mod64

theorem ArrayContext.agree {g : ArrayGeometry} {candidate exponent other otherExponent : Nat} {s t : State}
    (S : ArrayContext g candidate exponent s) (T : ArrayContext g other otherExponent t) :
    VG.X86.Taint.Agree (τr [.esp, .edi]) s t := by
  apply agree_regs
  intro r mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl
  · exact S.stack.sp.trans T.stack.sp.symm
  · exact S.workspace.trans T.workspace.symm

theorem init_trace {g : ArrayGeometry} (v : g.Valid) {candidate exponent other otherExponent : Nat}
    (positive : 0 < exponent) (otherPositive : 0 < otherExponent) :
    RelCT isa (fun s t => ArrayContext g candidate exponent s ∧ ArrayContext g other otherExponent t)
      (.block (init g.n g.src))
      (fun s t => ArrayState g candidate exponent 0 s ∧ ArrayState g other otherExponent 0 t) := by
  intro s t tr ur u z ⟨S, T⟩ E G
  have raw : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi])) (.block (init g.n g.src))
      (VG.X86.Taint.Agree (τr [.esp, .edi])) :=
    erased_relCT (.block (init g.n g.src)) (.block (init 0 0)) (.block []) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by decide +kernel)
  have trace := (raw _ _ _ _ _ _ (S.agree T) E G).1
  exact ⟨trace, (wp_result (init_ok v S positive) E).1, (wp_result (init_ok v T otherPositive) G).1⟩

theorem array_trace {g : ArrayGeometry} (v : g.Valid) {candidate exponent other otherExponent : Nat}
    (positive : 0 < exponent) (otherPositive : 0 < otherExponent) :
    RelCT isa (fun s t => ArrayContext g candidate exponent s ∧ ArrayContext g other otherExponent t)
      (array g.n g.src g.exponent) (VG.X86.Taint.Agree (τr [.esp, .edi])) :=
  RelCT.seq (init_trace v positive otherPositive) (loop_trace v)

end VG.Proof.RsaKeyGen.X86.Mod64
