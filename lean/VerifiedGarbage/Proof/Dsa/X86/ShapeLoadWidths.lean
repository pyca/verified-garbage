module

public import VerifiedGarbage.Proof.Dsa.X86.CoreLoad
public import VerifiedGarbage.Proof.Dsa.X86.ShapeCombine
public import VerifiedGarbage.Proof.Ecdsa.X86.Flags
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Weierstrass.PointContract
import VerifiedGarbage.Proof.Dsa.X86.Layout
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Spec.Dsa
public import VerifiedGarbage.Impl.Dsa.X86.Width
import VerifiedGarbage.Proof.Dsa.X86.WidthConstant
import VerifiedGarbage.Proof.Dsa.BitLengthBounds

/-! ### `Dsa.X86.ShapeFrame`, which only this module used -/

section

/-! # Frames for width-mask scratch and public header slots -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86

theorem widthFrame_modulus {s t : State} {base : Addr} {n output count : Nat}
    (O : Outs base [(slot n 8, 8 * n), (output, count)] s.mem t.mem)
    (ho : output + count ≤ 64) (hb : contextBytes n ≤ 2 ^ 64) :
    wordsVal t.mem base (slot n 0) n = wordsVal s.mem base (slot n 0) n := by
  have b := slot_bound (n := n) (i := 0) (by decide)
  have sep := slot_le (n := n) (i := 0) (j := 8) (by decide)
  have h0 := slot_header n 0
  simp only [stride] at b sep
  rw [wordsVal_eq_val32, wordsVal_eq_val32]
  apply O.val32
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> omega
  · omega_using [hb, b]

theorem widthFrame_header {s t : State} {base : Addr} {n output d : Nat}
    (O : Outs base [(slot n 8, 8 * n), (output, 4)] s.mem t.mem)
    (hd : d + 4 ≤ 64) (hsep : d + 4 ≤ output ∨ output + 4 ≤ d) :
    shapeWord t base d = shapeWord s base d := by
  have h8 := slot_header n 8
  apply BitVec.eq_of_toNat_eq
  have H : val32 t.mem base d 1 = val32 s.mem base d 1 := by
    apply O.val32
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> omega
    · omega_using [hd]
  simpa only [val32, Nat.mul_zero, Nat.add_zero] using H

theorem widthFrame_widen {s t : State} {base : Addr} {n output lo len : Nat}
    (O : Outs base [(slot n 8, 8 * n), (output, 4)] s.mem t.mem)
    (hl : lo ≤ output) (hh : output + 4 ≤ lo + len) :
    Outs base [(slot n 8, 8 * n), (lo, len)] s.mem t.mem := by
  intro x hx
  apply O x
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hx _ (by simp)
  · have H := hx (lo, len) (by simp)
    omega

end VG.Proof.Dsa.X86

end

end

/-! ### `Dsa.X86.Width`, which only this module used -/

section

/-! # Correctness of the exact-width mask -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.X86
open VG.Proof.Ecdsa.X86

theorem widthMask_ok {s : State} {base : Addr} {size n a tmp bits : Nat}
    (hs : Scr s base size) (hn : 0 < n) (ha : a + 8 * n ≤ size) (ht : tmp + 8 * n ≤ size)
    (hb : 0 < bits) (hbn : bits ≤ 64 * n) (hsep : a + 8 * n ≤ tmp ∨ tmp + 8 * n ≤ a) :
    WP isa (widthMask n a tmp bits) s fun t =>
      t.gpr .edx = mask32 (2 ^ (bits - 1) ≤ wordsVal s.mem base a n ∧ wordsVal s.mem base a n < 2 ^ bits) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t ∧ Outside base tmp (8 * n) s.mem t.mem := by
  unfold widthMask
  refine WP.seq (WP.mono (lessThanConstant_ok hs hn ha ht
    (Nat.pow_lt_pow_right (by decide) (by omega)) hsep) fun u ⟨Vu, Ku, Ou⟩ => ?_)
  refine WP.seq (wp_logicS (.inr rfl) rfl fun v uv => ?_)
  refine wp_movS rfl fun w uw _ => WP.block_nil ?_
  have Kw : Keeps [.eax, .ebx, .ecx, .edx, .ebp] s w := ((Ku.mono (by decide)).widen uv.keeps).widen uw.keeps
  have Ow : Outside base tmp (8 * n) s.mem w.mem := by rw [uw.mem, uv.mem]; exact Ou
  have Ew : w.gpr .ebx = mask32 (2 ^ (bits - 1) ≤ wordsVal s.mem base a n) := by
    rw [uw.gpr, uv.gpr, Vu]
    simp only [reduceCtorEq, ite_false, mask_not, Nat.not_lt]
  by_cases hsmall : bits < 64 * n
  · rw [ite_eq_left hsmall]
    refine WP.seq (WP.mono (lessThanConstant_ok (hs.of_keeps Kw (by decide)) hn ha ht
      (Nat.pow_lt_pow_right (by decide) hsmall) hsep) fun x ⟨Vx, Kx, Ox⟩ => ?_)
    refine wp_logicS (.inl rfl) rfl fun y uy => ?_
    refine wp_movS rfl fun t ut _ => WP.block_nil ⟨?_, ((Kw.widen Kx).widen uy.keeps).widen ut.keeps, ?_⟩
    · rw [ut.gpr, uy.gpr, Vx, Kx.1 _ (by decide), Ew,
        Ow.wordsVal hsep (by have := hs.nowrap; omega_using [ha, this])]
      simp only [ite_true, mask32_and, and_comm]
    · rw [ut.mem, uy.mem]
      exact Ow.trans Ox
  · rw [ite_eq_right hsmall]
    refine wp_movS rfl fun t ut _ => WP.block_nil ⟨?_, Kw.widen ut.keeps, ut.mem ▸ Ow⟩
    have eq : bits = 64 * n := by omega_using [hbn, hsmall]
    rw [ut.gpr, Ew, eq]
    simp only [wordsVal_lt s.mem base a n, and_true]

theorem widthMask_bitLength {s : State} {base : Addr} {size n a tmp bits : Nat}
    (hs : Scr s base size) (hn : 0 < n) (ha : a + 8 * n ≤ size) (ht : tmp + 8 * n ≤ size)
    (hb : 0 < bits) (hbn : bits ≤ 64 * n) (hsep : a + 8 * n ≤ tmp ∨ tmp + 8 * n ≤ a) :
    WP isa (widthMask n a tmp bits) s fun t =>
      t.gpr .edx = mask32 (Spec.Dsa.bitLength (wordsVal s.mem base a n) = bits) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t ∧ Outside base tmp (8 * n) s.mem t.mem := by
  simpa only [VG.Proof.Dsa.bitLength_iff_bounds hb] using widthMask_ok hs hn ha ht hb hbn hsep

theorem optionalWidth_ok {s : State} {base : Addr} {size n a tmp bits : Nat}
    (hs : Scr s base size) (hn : 0 < n) (ha : a + 8 * n ≤ size) (ht : tmp + 8 * n ≤ size)
    (hb : 0 < bits) (hsep : a + 8 * n ≤ tmp ∨ tmp + 8 * n ≤ a) :
    WP isa (optionalWidth n a tmp bits) s fun t =>
      t.gpr .edx = mask32 (Spec.Dsa.bitLength (wordsVal s.mem base a n) = bits) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t ∧ Outside base tmp (8 * n) s.mem t.mem := by
  unfold optionalWidth
  by_cases hbn : bits ≤ 64 * n
  · rw [ite_eq_left hbn]
    exact widthMask_bitLength hs hn ha ht hb hbn hsep
  · rw [ite_eq_right hbn]
    have hnot : Spec.Dsa.bitLength (wordsVal s.mem base a n) ≠ bits := by
      intro h
      have lower := ((VG.Proof.Dsa.bitLength_iff_bounds hb).mp h).1
      have upper := wordsVal_lt s.mem base a n
      have powers : 2 ^ (64 * n) ≤ 2 ^ (bits - 1) := Nat.pow_le_pow_right (by decide) (by omega_using [hbn])
      omega_using [lower, upper, powers]
    refine wp_movS rfl fun t ut _ => WP.block_nil ⟨?_, ut.keeps.mono (by decide), ?_⟩
    · rw [ut.gpr, mask32, ite_eq_right hnot]
    · rw [ut.mem]
      exact Outside.refl _ _ _ _

end VG.Proof.Dsa.X86

end

end

/-! # Actual-width masks directly from an encoded DSA modulus -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86/ShapeWidth.lean`, which only this module imported.
section

/-! # Saving actual-width checks in the public domain header -/

section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86 VG.Proof.Ecdsa.X86

theorem shapeWidth_ok {s : State} {base : Addr} {size n bits output : Nat}
    (hs : Scr s base size) (hn : 0 < n) (hz : contextBytes n ≤ size)
    (hb : 0 < bits) (ho : output + 4 ≤ size) :
    WP isa (Shape.saveWidth n bits output) s fun t =>
      shapeWord t base output = mask32 (Spec.Dsa.bitLength (wordsVal s.mem base (slot n 0) n) = bits) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t ∧
      Outs base [(slot n 8, 8 * n), (output, 4)] s.mem t.mem := by
  have b0 := slot_bound (n := n) (i := 0) (by decide)
  have b8 := slot_bound (n := n) (i := 8) (by decide)
  have sep := slot_le (n := n) (i := 0) (j := 8) (by decide)
  simp only [stride] at b0 b8 sep
  unfold Shape.saveWidth
  refine WP.seq (WP.mono (optionalWidth_ok hs hn (by omega) (by omega) hb (.inl (by omega)))
    fun u ⟨Vu, Ku, Ou⟩ => ?_)
  have hu := hs.of_keeps Ku (by decide)
  refine wp_storeS (hu.ea (by omega)) (hu.write ho) fun t mt => WP.block_nil ⟨?_, Ku.trans (mt.keeps _), ?_⟩
  · rw [shapeWord, mt.mem, Mem.readW_writeW_self32, Vu]
  · have Ot : Outside base output 4 u.mem t.mem := by
      rw [mt.mem]
      exact writeW32_outside _ _ _ (by have := hs.nowrap; omega)
    exact (Outs.of_outside Ou (by simp)).trans (Outs.of_outside Ot (by simp))

end VG.Proof.Dsa.X86
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86/ShapeThreeWidths.lean`, which only this module imported.
section

/-! # The three candidate widths of each DSA modulus -/

section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86 VG.Proof.Ecdsa.X86

theorem threeWidths_ok {s : State} {base : Addr} {size n a b c output : Nat}
    (hs : Scr s base size) (hn : 0 < n) (hz : contextBytes n ≤ size)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (ho : output + 12 ≤ 64) :
    WP isa (Shape.threeWidths n a b c output) s fun t =>
      shapeWord t base output = mask32 (Spec.Dsa.bitLength (wordsVal s.mem base (slot n 0) n) = a) ∧
      shapeWord t base (output + 4) = mask32 (Spec.Dsa.bitLength (wordsVal s.mem base (slot n 0) n) = b) ∧
      shapeWord t base (output + 8) = mask32 (Spec.Dsa.bitLength (wordsVal s.mem base (slot n 0) n) = c) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t ∧ Outs base [(slot n 8, 8 * n), (output, 12)] s.mem t.mem := by
  have bh := slot_header n 9
  change 64 ≤ contextBytes n at bh
  have fit : contextBytes n ≤ 2 ^ 64 := by have := hs.nowrap; omega
  unfold Shape.threeWidths
  refine WP.seq (WP.mono (shapeWidth_ok hs hn hz ha (by omega)) fun u ⟨Vu, Ku, Ou⟩ => ?_)
  refine WP.seq (WP.mono (shapeWidth_ok (hs.of_keeps Ku (by decide)) hn hz hb (by omega))
    fun v ⟨Vv, Kv, Ov⟩ => ?_)
  refine WP.mono (shapeWidth_ok ((hs.of_keeps Ku (by decide)).of_keeps Kv (by decide)) hn hz hc (by omega))
    fun t ⟨Vt, Kt, Ot⟩ => ?_
  refine ⟨?_, ?_, ?_, (Ku.trans Kv).trans Kt, ?_⟩
  · rw [widthFrame_header Ot (by omega) (by omega), widthFrame_header Ov (by omega) (by omega), Vu]
  · rw [widthFrame_header Ot (by omega) (by omega), Vv, widthFrame_modulus Ou (by omega) fit]
  · rw [Vt, widthFrame_modulus Ov (by omega) fit, widthFrame_modulus Ou (by omega) fit]
  · exact ((widthFrame_widen Ou (Nat.le_refl _) (by omega)).trans
      (widthFrame_widen Ov (by omega) (by omega))).trans (widthFrame_widen Ot (by omega) (by omega))

end VG.Proof.Dsa.X86
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86 VG.Proof.Ecdsa.X86

theorem loadWidths_ok {s : State} {base : Addr} {size len n m a b c output : Nat} {modulus : VG.Impl.Dsa.Layout.Field}
    (hs : Scr s base size) (hz : VG.Impl.Dsa.X86.Layout.saved ≤ size)
    (hn : n = (len + 7) / 8) (h4 : 4 ≤ len) (hmax : len ≤ 384) (hw4 : len % 4 = 0)
    (hr : ReadableComponent s base (.input modulus) len)
    (hd : Region.Disjoint ⟨(pointerValue base s (.input modulus)).setWidth 64, len⟩ ⟨off base (slot n 0), 8 * n⟩)
    (hm : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s (.input modulus)).setWidth 64) len) = m)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (ho : output + 12 ≤ 64) :
    WP isa (Shape.loadWidths len modulus a b c output) s fun t =>
      wordsVal t.mem base (slot n 0) n = m ∧
      shapeWord t base output = mask32 (Spec.Dsa.bitLength m = a) ∧
      shapeWord t base (output + 4) = mask32 (Spec.Dsa.bitLength m = b) ∧
      shapeWord t base (output + 8) = mask32 (Spec.Dsa.bitLength m = c) ∧
      Keeps shapeClob s t ∧
      Outs base [(slot n 0, 8 * n), (slot n 8, 8 * n), (output, 12)] s.mem t.mem := by
  have hn0 : 0 < n := by omega_using [hn, h4]
  have cb := VG.Proof.Dsa.X86.Layout.context_bound (show n ≤ 48 by omega_using [hn, hmax])
  have hsize : 8256 ≤ size := hz
  have b0 := slot_bound (n := n) (i := 0) (by decide)
  simp only [stride] at b0
  unfold Shape.loadWidths
  dsimp only
  rw [← hn]
  refine WP.seq (WP.mono (coreLoad_ok hs hz (by omega_using [cb, hsize, b0]) h4 (by omega_using [hn]) hw4 hr hd)
    fun u ⟨Vu, Ku, Ou⟩ => ?_)
  rw [hm] at Vu
  refine WP.mono (threeWidths_ok (hs.of_keeps Ku (by decide)) hn0 (by omega_using [cb, hsize]) ha hb hc ho)
    fun t ⟨Va, Vb, Vc, Kt, Ot⟩ => ?_
  refine ⟨?_, by rw [Va, Vu], by rw [Vb, Vu], by rw [Vc, Vu], (Ku.mono (by decide)).widen Kt, ?_⟩
  · rw [widthFrame_modulus Ot ho (by omega_using [cb]), Vu]
  · have O1 : Outs base [(slot n 0, 8 * n), (slot n 8, 8 * n), (output, 12)] s.mem u.mem :=
      Outs.of_outside Ou (by simp)
    exact O1.trans (Ot.mono (by intro r hr; exact List.mem_cons_of_mem _ hr))

end VG.Proof.Dsa.X86
