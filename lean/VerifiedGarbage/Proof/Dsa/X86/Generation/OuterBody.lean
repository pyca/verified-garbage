module
public import Aesop.BuiltinRules
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Basic
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Spec.Weierstrass.Point
public import VerifiedGarbage.Proof.Dsa.X86.Generation.EntryResult
public import VerifiedGarbage.Proof.Dsa.X86.Generation.Hashes
public import VerifiedGarbage.Proof.Dsa.X86.Generation.OuterSetup
import VerifiedGarbage.Proof.Dsa.X86.Generation.EntryNarrow
import VerifiedGarbage.Proof.Dsa.X86.Generation.FrameAllocation
import VerifiedGarbage.Proof.Dsa.X86.Generation.OuterRestore
import VerifiedGarbage.Proof.Dsa.X86.Generation.RestoreFrame

/-! # Save registers, run the framed generator, and restore the caller's registers -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Impl.Dsa.X86.Generation

def outerWrites (s : State) : List Region := ⟨outerBase s, 16⟩ :: entryWrites s

structure OuterFinished (s t : State) : Prop where
  eax : t.gpr .eax = (if (parameterBytes s).isSome then 1 else 0)
  out : Spec.Rsa.bytesAt t.mem (argumentPointer s 0) (arg s 1).toNat =
    (parameterBytes s).getD (List.replicate (arg s 1).toNat 0)
  ebx : t.gpr .ebx = s.gpr .ebx
  ebp : t.gpr .ebp = s.gpr .ebp
  esi : t.gpr .esi = s.gpr .esi
  edi : t.gpr .edi = s.gpr .edi
  esp : t.gpr .esp = (allocated 16 s).gpr .esp
  frame : Frame (outerWrites s) s.mem t.mem
  rd : t.rd = s.rd
  wr : t.wr = (allocated 16 s).wr

theorem outerBody_ok (H : GenerationHashes) (F : KeyRandom.CheckCall.CheckFn) {s : State} (A : ParameterABI s) :
    WP isa (.seq (.block saveRegisters)
      (.seq (.frame (.alloc 148) (entryBody H.sha1 H.sha256 F.name F.code) (.free 148))
        (.block restoreRegisters))) (allocated 16 s) (OuterFinished s) := by
  refine WP.seq (WP.mono (saveRegisters_ok A.outerFrame) fun a ⟨Fa, Sa, Oa, Ka⟩ => ?_)
  have size : 148 ≤ (a.gpr .esp).toNat := by
    rw [Ka.1 _ (by decide), allocated_esp, sub_toNat (by have := A.stackLow; omega)]
    have := A.stackLow
    omega
  have run := entryBody_narrow_ok H F (afterSave_start A Oa Ka)
  refine WP.seq (alloc_restored (by decide) size (WP.mono run fun b Rb => ?_))
  refine ⟨Rb.2.2.2.2.2, ?_⟩
  have saved := searchFreed_saved A (saved_allocated Sa) Rb
  refine WP.mono (restoreRegisters_ok (searchFreed_frame Fa Rb) saved) fun t ⟨bx, bp, si, di, mem, Kt⟩ => ?_
  refine ⟨?_, ?_, bx, bp, si, di, ?_, ?_, ?_, ?_⟩
  · rw [Kt.1 _ (by decide), freed_gpr _ _ (by decide)]
    exact Rb.1
  · rw [mem]
    exact Rb.2.1
  · exact (Kt.1 _ (by decide)).trans ((searchFreed_esp Rb).trans (Ka.1 _ (by decide)))
  · rw [mem]
    change Frame (outerWrites s) s.mem b.mem
    exact (Oa.mono (fun _ hr => by obtain rfl := List.mem_singleton.mp hr; exact List.mem_cons_self)).trans
      (Rb.2.2.1.mono (fun _ hr => List.mem_cons_of_mem _ hr))
  · exact Kt.2.1.trans (Rb.2.2.2.1.trans Ka.2.1)
  · exact Kt.2.2.trans ((searchFreed_wr Rb).trans Ka.2.2)
end VG.Proof.Dsa.X86.Generation
