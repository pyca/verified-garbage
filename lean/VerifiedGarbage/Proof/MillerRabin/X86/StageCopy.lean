module

public import VerifiedGarbage.Proof.MillerRabin.X86.StageFrame
public import VerifiedGarbage.Proof.MillerRabin.X86.Copy

/-! # Copying an operand while preserving the round invariant -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Spec.Rsa.Mont (arrAt numAt)

namespace Stage

theorem copy {σ s : State} {base : Addr} {bytes w o a : Nat}
    (h : Stage base bytes w σ s) (hw : 4 ≤ w) (hu : w ≤ 128)
    (hf : arrAt w 28 ≤ bytes) (ho : o < 28) (ha : a < 28) (hne : a ≠ o)
    (mutable : o = 5 ∨ o = 6 ∨ o = 8 ∨ (11 ≤ o ∧ o < 27))
    (initial : σ.mem.readW (off base 48) 32 = BitVec.ofNat 32 w) :
    WP isa (VG.Impl.MillerRabin.X86.copy o a) s fun t =>
      numAt t.mem base w o = numAt s.mem base w a ∧ Stage base bytes w σ t ∧
      Frame [⟨off base (arrAt w o), 8 * w⟩] s.mem t.mem ∧
      Keeps [.eax, .ebx, .esi, .edx, .ecx] s t := by
  refine WP.mono (copy_ok h.context.ws hw hu hf ho ha hne (h.width hf initial)) ?_
  rintro t ⟨value, frame, keeps⟩
  exact ⟨value, h.after_array keeps frame mutable, frame, keeps⟩

end Stage
end VG.Proof.MillerRabin.X86
