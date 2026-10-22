module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeContext
import VerifiedGarbage.Proof.Mont.X86.ContextLayout

/-! The candidate context and the exponent saved before compact header installation. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86

structure SavedContext (base : Addr) (n candidate : Nat) (s : State) : Prop extends
    PrimeContext base n candidate s where
  exponent : wordsVal s.mem base (slot n 8) n = Spec.MillerRabin.exponent candidate
  oneHot : word s.mem base (slot n 8 + 8 * n) =
    BitVec.twoPow 64 ((Spec.Rsa.splitTwos (candidate - 1)).1 % 64)

theorem SavedContext.frame_keep {s t : State} {base : Addr} {n candidate : Nat}
    {rs : List Region} {regs : List Reg} (C : SavedContext base n candidate s)
    (K : Keeps regs s t) (edi : .edi ∉ regs) (esp : .esp ∉ regs) (F : Frame rs s.mem t.mem)
    (apart : ∀ r ∈ rs, Region.Disjoint ⟨base, montgomeryBytes⟩ r) : SavedContext base n candidate t := by
  have bound := VG.Proof.Mont.X86.Dynamic.slot_bound (n := n) (i := 8) (by decide)
  have size := C.parent.size_le
  refine ⟨C.toPrimeContext.frame_keep K edi esp F apart,
    (C.parent.frame_slot F apart (show 8 < 9 by decide)).trans C.exponent, ?_⟩
  exact (C.parent.frame_word F apart (by unfold stride at bound; omega)).trans C.oneHot

end VG.Proof.Dsa.X86.Generation
