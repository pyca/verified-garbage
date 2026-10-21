module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.ExponentFilter
public import VerifiedGarbage.Proof.RsaKeyGen.X86.Mod64FramedTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.Gcd64PreserveTiming

/-! # Both stages of the general public-exponent filter preserve timing privacy -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.ExponentFilter
open VG VG.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.RsaKeyGen.X86.ExponentFilter VG.Impl.Bignum.X86.PublicContext

theorem general_trace {g : Mod64.ArrayGeometry} (v : g.Valid) {w candidate exponent other otherExponent : Nat}
    (width : g.n = 2 * w) (source : g.src = slot w 5) (offset : g.exponent = 128)
    (positive : 0 < exponent) (otherPositive : 0 < otherExponent) :
    RelCT isa (fun s t => Mod64.FramedInput g candidate exponent s ∧ Mod64.FramedInput g other otherExponent t)
      (general w) (VG.X86.Taint.Agree (workspaceTaint false)) := by
  unfold general
  have scan := Mod64.framed_trace v (candidate := candidate) (other := other) positive otherPositive
  rw [width, source, offset] at scan
  exact RelCT.seq scan (Gcd64.preserving_trace (2 * w) (slot w 0) (slot w 5) 128)

end VG.Proof.RsaKeyGen.X86.ExponentFilter
