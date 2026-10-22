module

public import VerifiedGarbage.Proof.MillerRabin.X86.StageFrame
public import VerifiedGarbage.Proof.MillerRabin.X86.Select

/-! # Masked operand selection preserves the shared loop invariant -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Spec.Rsa.Mont (arrAt)

namespace Stage

theorem select {σ s : State} {base : Addr} {bytes w o a : Nat} {k : Bool}
    (h : Stage base bytes w σ s) (hw : 4 ≤ w) (hu : w ≤ 128)
    (hf : arrAt w 28 ≤ bytes) (ho : o < 28) (ha : a < 28) (hne : a ≠ o)
    (mutable : o = 5 ∨ o = 6 ∨ o = 8 ∨ (11 ≤ o ∧ o < 27))
    (initial : σ.mem.readW (off base 48) 32 = BitVec.ofNat 32 w)
    (mask : s.gpr .esi = cmask k) :
    WP isa (VG.Impl.MillerRabin.X86.select o a) s fun t =>
      val32 t.mem base (arrAt w o) (2 * w) =
        (if k then val32 s.mem base (arrAt w a) (2 * w) else val32 s.mem base (arrAt w o) (2 * w)) ∧
      Stage base bytes w σ t ∧ Outside base (arrAt w o) (8 * w) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ebp, .ecx, .edx, .esi] s t := by
  have fit := array_fits_bytes hf ho
  have nw := h.context.ws.nowrap
  refine WP.mono (select_ok h.context.ws hw hu hf ho ha hne (h.width hf initial) mask) ?_
  rintro t ⟨value, outside, keeps⟩
  exact ⟨value, h.after_array keeps (VG.Proof.Bignum.outside_frame outside (by omega)) mutable,
    outside, keeps⟩

end Stage
end VG.Proof.MillerRabin.X86
