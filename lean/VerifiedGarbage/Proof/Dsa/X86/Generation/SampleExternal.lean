module
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Mont.X86.ContextFrame
import VerifiedGarbage.Proof.Dsa.X86.Generation.SampleMemory

/-! # Mutating the separate witness buffer preserves the prepared modulus -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic

theorem sampleExternal_context {s t : State} {base p : Addr} {size n m len : Nat} {rs : List Reg}
    (C : Context n m base size s) (K : Keeps rs s t) (di : .edi ∉ rs) (sp : .esp ∉ rs)
    (O : Frame [⟨p, len⟩] s.mem t.mem) (apart : Region.Disjoint ⟨base, size⟩ ⟨p, len⟩) :
    Context n m base size t := by
  have modBound : slot n 0 + 8 * n ≤ size := C.modulus.mo
  have unchanged : wordsVal t.mem base (slot n 0) n = wordsVal s.mem base (slot n 0) n :=
    sampleFrame_words O (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact apart.sub_left (Offset.sub_base _ modBound))
      (by have := C.scr.nowrap; omega)
  have size4 : 4 ≤ size := by have := C.size_le; unfold contextBytes slot at this; omega
  have read : t.mem.readW base 32 = s.mem.readW base 32 :=
    O.readW (r := ⟨base, size⟩)
      (by simpa only [off, BitVec.add_zero] using Offset.contains_base base (by omega : 0 + 4 ≤ size) (by decide : 0 < 2 ^ 64))
      (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact apart) (by decide)
  refine ⟨C.scr.of_keeps K di sp, C.size_le,
    ⟨C.modulus.n0, C.modulus.mo, C.modulus.tmp, C.modulus.sep, unchanged.trans C.modulus.val⟩, C.gt_one, ?_⟩
  simpa only [w32, off, BitVec.add_zero, read] using C.inverse
end VG.Proof.Dsa.X86.Generation
