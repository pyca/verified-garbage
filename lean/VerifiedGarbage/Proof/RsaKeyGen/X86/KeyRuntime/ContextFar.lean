module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyArgContext
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86.Call

/-! # The cdecl arguments survive writes away from them, such as the key outputs -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyArgs
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.CandidateArgs

/-- `Context.keep` for writes to any regions apart from the arguments. -/
theorem Context.keepFar {base : Addr} {size : Nat} {p : BitVec 32} {inputs : Nat → BitVec 32} {s t : State}
    {rs : List Reg} (C : Context base size p inputs s) (K : Keeps rs s t) {writes : List Region}
    (F : Frame writes s.mem t.mem) (far : ∀ r ∈ writes, (argsRegion p).Disjoint r)
    (edi : .edi ∉ rs := by decide) (esp : .esp ∉ rs := by decide) :
    Context base size p inputs t := by
  have spT : t.gpr .esp = p := (K.1 .esp esp).trans C.sp
  refine ⟨C.scratch.of_keeps K edi esp, C.header, spT, C.fit, C.separate, ?_⟩
  intro i index
  have eaT : t.ea (arg i) = s.ea (arg i) := by
    change addr (t.gpr .esp) _ = addr (s.gpr .esp) _
    rw [K.1 .esp esp]
  have memory : t.mem.readW (s.ea (arg i)) 32 = s.mem.readW (s.ea (arg i)) 32 := by
    rw [C.address index]
    exact F.readW (r := argsRegion p)
      (Offset.contains_base _ (by change 4 * i + 4 ≤ 72; omega) (by omega : 4 * i < 2 ^ 64))
      far (by decide)
  have same : readSrc t (.mem (arg i)) = readSrc s (.mem (arg i)) := by
    show t.load32 (t.ea (arg i)) = s.load32 (s.ea (arg i))
    simp only [State.load32, eaT, K.2.1, K.2.2, memory]
  exact same.trans (C.read i index)

end VG.Proof.RsaKeyGen.X86.KeyArgs
