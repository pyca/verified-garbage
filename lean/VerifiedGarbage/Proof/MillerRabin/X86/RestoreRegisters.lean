module

public import VerifiedGarbage.Proof.MillerRabin.X86.BodyFrame
public import VerifiedGarbage.Proof.MillerRabin.X86.Finish

/-! # Saved registers survive the arithmetic and the workspace restoration -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.MillerRabin.X86
open VG.Spec.Rsa.Mont (arrAt)

theorem restore_saved {σ s t g : State} {base : Addr} {bytes w : Nat} {rs : List Reg}
    (saved : Spill.Saved σ.mem (off (byteAddr (σ.gpr .esp))) g.gpr savedRegisters)
    (h : Stage base bytes w σ s) (fit : arrAt w 28 ≤ bytes)
    (frame : Frame [⟨off base (scratch w), 32⟩, ⟨off base (arrAt w 4), 8 * w⟩] s.mem t.mem)
    (K : Keeps rs s t) (esp : .esp ∉ rs := by decide) :
    Spill.Saved t.mem (off (byteAddr (t.gpr .esp))) g.gpr savedRegisters := by
  rw [K.1 .esp esp, h.stack]
  apply saved.of_readW
  intro p hp
  have bound : p.2 + 4 ≤ 52 := by
    simp only [savedRegisters, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> decide
  have read := restore_stack_read h.context fit (d := p.2) (n := 4)
    (by change p.2 + 4 ≤ 1132; omega) frame
  have read32 := congrArg (BitVec.setWidth 32) read
  change t.mem.readW (off (byteAddr (s.gpr .esp)) p.2) 32 =
    s.mem.readW (off (byteAddr (s.gpr .esp)) p.2) 32 at read32
  rw [h.stack] at read32
  exact read32.trans (h.read_stack32 fit (by change p.2 + 4 ≤ 1132; omega)
    (.inl (by change p.2 + 4 ≤ 60; omega)))

end VG.Proof.MillerRabin.X86
