module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.ParentConstants

/-! The reusable parent constants while preparing a compact candidate. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86

structure PrimeContext (base : Addr) (n candidate : Nat) (s : State) : Prop where
  parent : ParentContext base n candidate s
  ordinary : wordsVal s.mem base (slot n 3) n = 1
  square : wordsVal s.mem base (slot n 4) n = 2 ^ (64 * n) * 2 ^ (64 * n) % candidate
  one : wordsVal s.mem base (slot n 6) n = 2 ^ (64 * n) % candidate
  minus : wordsVal s.mem base (slot n 7) n = candidate - 2 ^ (64 * n) % candidate

theorem PrimeContext.frame_keep {s t : State} {base : Addr} {n candidate : Nat}
    {rs : List Region} {regs : List Reg} (C : PrimeContext base n candidate s)
    (K : Keeps regs s t) (edi : .edi ∉ regs) (esp : .esp ∉ regs) (F : Frame rs s.mem t.mem)
    (apart : ∀ r ∈ rs, Region.Disjoint ⟨base, montgomeryBytes⟩ r) : PrimeContext base n candidate t := by
  refine ⟨C.parent.frame_keep K edi esp F apart, ?_, ?_, ?_, ?_⟩
  · exact (C.parent.frame_slot F apart (show 3 < 9 by decide)).trans C.ordinary
  · exact (C.parent.frame_slot F apart (show 4 < 9 by decide)).trans C.square
  · exact (C.parent.frame_slot F apart (show 6 < 9 by decide)).trans C.one
  · exact (C.parent.frame_slot F apart (show 7 < 9 by decide)).trans C.minus

end VG.Proof.Dsa.X86.Generation
