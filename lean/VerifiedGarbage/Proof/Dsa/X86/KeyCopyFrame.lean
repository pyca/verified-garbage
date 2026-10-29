module

import VerifiedGarbage.Proof.Dsa.X86.Layout
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Dsa.X86.Pointer
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Dsa.X86.OutputFrame

/-! # Copying a key preserves the workspace and every disjoint source -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem external_pointer {s t : State} {base out : Addr} {size len : Nat}
    (hs : Scr s base size) (hz : Layout.saved ≤ size)
    (O : Outside out 0 len s.mem t.mem)
    (A : Region.Disjoint ⟨base, size⟩ ⟨out, len⟩)
    (K : Keeps [.eax, .ecx, .edx, .esi] s t) (p : Pointer) :
    pointerValue base t p = pointerValue base s p := by
  have F : OutputFrame base out 0 len s.mem t.mem :=
    fun a _ h => O a (.inr (by simpa only [Nat.zero_add] using h))
  have field (f : Field) :
      t.mem.readW (off base (Layout.field f)) 32 = s.mem.readW (off base (Layout.field f)) 32 := by
    have B := VG.Proof.Dsa.X86.Layout.field_bounds f
    exact F.scratch_word A (Nat.zero_le _) (by omega) (by have := hs.nowrap; omega)
  cases p with
  | input f => exact field f
  | «local» d => simp only [pointerValue, K.1 .edi (by decide)]
  | signatureS => simp only [pointerValue, field]

theorem external_bytes {m m' : Mem} {src out : Addr} {count len : Nat}
    (O : Outside out 0 len m m')
    (A : Region.Disjoint ⟨src, count⟩ ⟨out, len⟩)
    (hb : count < 2 ^ 64) :
    Spec.Rsa.bytesAt m' src count = Spec.Rsa.bytesAt m src count := by
  unfold Spec.Rsa.bytesAt
  apply List.map_congr_left
  intro i hi
  have H := List.mem_range.mp hi
  have D := A _ (Offset.contains_base src (by omega) (by omega : i < 2 ^ 64))
  apply O _ (.inr ?_)
  change ¬ (ofs out (src + BitVec.ofNat 64 i) + 1 ≤ len) at D
  omega

structure KeyPartReady (s : State) (base out : Addr) (total : Nat)
    (part : Pointer × Nat) : Prop where
  positive : 0 < part.2
  fits : (pointerValue base s part.1).toNat + part.2 ≤ 2 ^ 32
  read : ∀ i < part.2, InRegions (s.rd ++ s.wr)
    (off ((pointerValue base s part.1).setWidth 64) i) 1
  apart : Region.Disjoint ⟨(pointerValue base s part.1).setWidth 64, part.2⟩ ⟨out, total⟩

theorem KeyPartReady.keep {s t : State} {base out : Addr} {size total : Nat} {part : Pointer × Nat}
    (R : KeyPartReady s base out total part) (hs : Scr s base size) (hz : Layout.saved ≤ size)
    (O : Outside out 0 total s.mem t.mem) (A : Region.Disjoint ⟨base, size⟩ ⟨out, total⟩)
    (K : Keeps [.eax, .ecx, .edx, .esi] s t) :
    KeyPartReady t base out total part := by
  have P := external_pointer hs hz O A K part.1
  refine ⟨R.positive, ?_, ?_, ?_⟩
  · rw [P]; exact R.fits
  · rw [P, K.2.1, K.2.2]; exact R.read
  · rw [P]; exact R.apart

theorem KeyPartReady.bytes {s t : State} {base out : Addr} {size total : Nat} {part : Pointer × Nat}
    (R : KeyPartReady s base out total part) (hs : Scr s base size) (hz : Layout.saved ≤ size)
    (O : Outside out 0 total s.mem t.mem) (A : Region.Disjoint ⟨base, size⟩ ⟨out, total⟩)
    (K : Keeps [.eax, .ecx, .edx, .esi] s t) :
    Spec.Rsa.bytesAt t.mem ((pointerValue base t part.1).setWidth 64) part.2 =
      Spec.Rsa.bytesAt s.mem ((pointerValue base s part.1).setWidth 64) part.2 := by
  rw [external_pointer hs hz O A K part.1]
  exact external_bytes O R.apart (by have := R.fits; omega)

end VG.Proof.Dsa.X86
