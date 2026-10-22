module

public import VerifiedGarbage.Proof.MillerRabin.X86.StageFrame
public import VerifiedGarbage.Proof.MillerRabin.X86.Equal

/-! # Equality tests preserve the round invariant -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Spec.Rsa.Mont (arrAt)

namespace Stage

theorem equal {σ s : State} {base : Addr} {bytes w a b d : Nat}
    (h : Stage base bytes w σ s) (hw : 4 ≤ w) (hu : w ≤ 128)
    (hf : arrAt w 28 ≤ bytes) (ha : a < 28) (hb : b < 28)
    (hd : d ∈ [184, 188, 212, 232, 236, 240, 244])
    (initial : σ.mem.readW (off base 48) 32 = BitVec.ofNat 32 w) :
    WP isa (VG.Impl.MillerRabin.X86.equal d a b) s fun t =>
      w32 t.mem base d =
        (decide (val32 s.mem base (arrAt w a) (2 * w) = val32 s.mem base (arrAt w b) (2 * w))).toNat ∧
      Stage base bytes w σ t ∧ Outside base d 4 s.mem t.mem ∧
      Keeps [.eax, .ebx, .ebp, .ecx, .edx] s t := by
  have dsmall : d + 4 ≤ 256 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have fit : d + 4 ≤ bytes := by simp only [arrAt, Spec.Rsa.Mont.hdrBytes] at hf; omega
  refine WP.mono (equal_ok h.context.ws hw hu hf ha hb fit (h.width hf initial)) ?_
  rintro t ⟨value, outside, keeps⟩
  exact ⟨value, h.after_header keeps (VG.Proof.Bignum.outside_frame outside (by omega)) hd,
    outside, keeps⟩

end Stage
end VG.Proof.MillerRabin.X86
