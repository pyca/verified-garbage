module

public import VerifiedGarbage.Proof.Mont.X86.Compact.Frame

import VerifiedGarbage.Proof.Mont.X86.Compact.EntryMemory
public import VerifiedGarbage.Proof.Mont.X86.Compact.Metadata
import VerifiedGarbage.Proof.Mont.X86.Compact.Prepared
public import VerifiedGarbage.Proof.Mont.X86.Compact.Entry

/-! # Prepared metadata and numbers survive the callee's register save -/

@[expose] public section
namespace VG.Proof.Mont.X86.Compact
open VG VG.X86 VG.Proof.Mont VG.Proof.Rsa.Mont

theorem layout_pointer_low {m : Mem} {W : Addr} {wsLen j : Nat}
    (layout : Layout m W wsLen) (index : j < 8) :
    w32 m W (64 + 8 * j) = (W.toNat + arrAt (wOf m W) j) % 2 ^ 32 := by
  rw [show 64 + 8 * j = 8 * arrWord j by unfold arrWord; omega, header_low,
    layout.2.2.2 j index, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem Entry.metadata {s : State} (A : Entry s) :
    Metadata (entered s).mem (wsOf s) (arg s) (2 * wOf s.mem (wsOf s))
      (arrAt (wOf s.mem (wsOf s)) 2) (arrAt (wOf s.mem (wsOf s)) 0)
      (arrAt (wOf s.mem (wsOf s)) (arg s 3).toNat)
      (arrAt (wOf s.mem (wsOf s)) (arg s 4).toNat) := by
  have V := layout_metadata (A := arg s) A.layout A.left.1 A.right.1
  have fit := A.headerFit
  have left := A.left.1
  have right := A.right.1
  refine ⟨?_, V.aIndex, V.bIndex, ?_, ?_, ?_, ?_⟩
  · rw [A.pushed_w32 (by omega)]; exact V.width
  · rw [A.pushed_w32 (by omega)]; exact V.scratch
  · rw [A.pushed_w32 (by omega)]; exact V.modulus
  · rw [A.pushed_w32 (by omega)]; exact V.left
  · rw [A.pushed_w32 (by omega)]; exact V.right

theorem Entry.pushed_val32 {s : State} (A : Entry s) {d n : Nat}
    (fit : d + 4 * n ≤ lenOf s) :
    val32 (entered s).mem (wsOf s) d n = val32 s.mem (wsOf s) d n := by
  apply val32_congr
  intro i index
  exact A.pushed_w32 (by omega)

theorem Entry.output_ptr {s : State} (A : Entry s) :
    w32 (entered s).mem (wsOf s) (64 + 8 * (arg s 2).toNat) =
      ((wsOf s).toNat + arrAt (wOf s.mem (wsOf s)) (arg s 2).toNat) % 2 ^ 32 := by
  rw [A.pushed_w32 (by have := A.headerFit; have := A.output.1; omega)]
  exact layout_pointer_low A.layout A.output.1

end VG.Proof.Mont.X86.Compact
