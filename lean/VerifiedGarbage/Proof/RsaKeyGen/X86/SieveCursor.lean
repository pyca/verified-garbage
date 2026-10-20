module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveStack

/-! # Advance the static prime/inverse pointer by one pair -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Sieve
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.RsaKeyGen.X86.Sieve

theorem advanceCursor_ok {p : BitVec 32} {s : State} (C : StackContext p s) :
    WP isa (.block (advanceCursor stackSlots)) s fun t =>
      t.mem = s.mem.writeW (off (p.setWidth 64) 8) (s.mem.readW (off (p.setWidth 64) 8) 32 + 8) ∧
      Outside (p.setWidth 64) 8 4 s.mem t.mem ∧ Keeps [.edx] s t ∧ StackContext p t := by
  change WP isa (.block [.mov .edx (.mem (slot 8)), .alu .add .edx (.imm 8), .store (slot 8) .edx]) s _
  refine wp_movS (C.read 8 (by decide)) fun a A _ => wp_addS rfl fun b B _ => ?_
  have K : Keeps [.edx] s b := A.keeps.trans B.keeps
  refine WP.mono ((C.keep K (by decide)).store 8 (by decide) .edx) fun t ⟨M, O, Kt, Ct⟩ => ?_
  refine ⟨?_, ?_, K.widen Kt, Ct⟩
  · rw [M, B.mem, A.mem, B.gpr, A.gpr]
  · rw [B.mem, A.mem] at O; exact O

end VG.Proof.RsaKeyGen.X86.Sieve
