module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveStack

/-! # Save the trial result and form the all-ones continuation mask -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Sieve
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.RsaKeyGen.X86.Sieve

theorem saveHit_ok {p : BitVec 32} {s : State} (C : StackContext p s) :
    WP isa (.block (saveHit stackSlots)) s fun t =>
      t.gpr .ecx = s.gpr .eax - 1 ∧
      t.mem = s.mem.writeW (off (p.setWidth 64) 16) (s.gpr .eax) ∧
      Outside (p.setWidth 64) 16 4 s.mem t.mem ∧ Keeps [.ecx] s t ∧ StackContext p t := by
  change WP isa (.block ([.store (slot 16) .eax] ++ [.mov .ecx (.reg .eax), .alu .sub .ecx (.imm 1)])) s _
  refine WP.block_append (WP.mono (C.store 16 (by decide) .eax) fun a ⟨M, O, K, Ca⟩ => ?_)
  refine wp_movS rfl fun b B _ => wp_subS rfl fun t T _ => WP.block_nil ?_
  have keep : Keeps [.ecx] s t := ((K.mono (by decide)).widen B.keeps).trans T.keeps
  refine ⟨?_, ?_, ?_, keep, C.keep keep (by decide)⟩
  · rw [T.gpr, B.gpr, K.1 .eax (by decide)]
  · rw [T.mem, B.mem, M]
  · rw [T.mem, B.mem]; exact O

end VG.Proof.RsaKeyGen.X86.Sieve
