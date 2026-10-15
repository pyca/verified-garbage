module

public import VerifiedGarbage.Proof.Dsa.X86.ValidateRangeMask

/-! # Range validation on encoded DSA components -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86 VG.Proof.Ecdsa.X86

theorem validateRange_ok {s : State} {base : Addr} {size len n : Nat} {input : Pointer} {modulus : Field}
    (hs : Scr s base size) (hz : VG.Impl.Dsa.X86.Layout.saved ≤ size)
    (hn : n = (len + 7) / 8) (h4 : 4 ≤ len) (hmax : len ≤ 384)
    (Rm : OperandReady s base n (.input modulus) len) (Ri : OperandReady s base n input len)
    (aboveOne : Bool) :
    WP isa (.block (Validate.range len modulus input aboveOne)) s fun t =>
      flagW base (Layout.field .mask) t = flagW base (Layout.field .mask) s &&& mask32
        ((if aboveOne then 1 else 0) < Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s input).setWidth 64) len) ∧
          Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s input).setWidth 64) len) <
            Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s (.input modulus)).setWidth 64) len)) ∧
      Keeps [.esi, .eax, .ebx, .ecx, .edx] s t ∧
      Outs base [(0, contextBytes n), (Layout.field .mask, 4)] s.mem t.mem := by
  have hn48 : n ≤ 48 := by omega
  have cb := VG.Proof.Dsa.X86.Layout.context_bound hn48
  unfold Validate.range
  dsimp only
  rw [← hn, List.append_assoc]
  refine WP.block_append (WP.mono (rawInputs_ok hs hz hn48 (by decide) (by decide) (by decide)
    h4 (by omega) h4 (by omega) Rm Ri) fun u ⟨Mu, Iu, Ou, Ku⟩ => ?_)
  have Fu : flagW base (Layout.field .mask) u = flagW base (Layout.field .mask) s :=
    pointerValue_keep Ku (by decide) Ou (by omega) (.input .mask)
  refine WP.mono (rangeMask_ok (hs.of_keeps Ku (by decide)) hz (by omega) hn48 aboveOne)
    fun t ⟨Vt, Kt, Ot⟩ => ?_
  exact ⟨by rw [Vt, Fu, Iu, Mu], (Ku.mono (by decide)).widen Kt,
    (Outs.of_outside Ou (by simp)).trans Ot⟩

end VG.Proof.Dsa.X86
