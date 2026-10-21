module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Mod64Array
public import VerifiedGarbage.Proof.RsaKeyGen.X86.Mod64ArrayContext
import VerifiedGarbage.Proof.RsaKeyGen.X86.Mod64ArrayInit
import VerifiedGarbage.Proof.RsaKeyGen.X86.Mod64ArrayLoop

/-! # Candidate-sized reduction by any positive 64-bit exponent on i686 -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Mod64
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.Mod64

theorem array_ok {g : ArrayGeometry} (v : g.Valid) {candidate exponent : Nat} {s : State}
    (C : ArrayContext g candidate exponent s) (positive : 0 < exponent) :
    WP isa (array g.n g.src g.exponent) s fun t =>
      ArrayContext g candidate exponent t ∧ pair (t.gpr .ecx) (t.gpr .ebx) = candidate % exponent ∧
      Outside (g.sp.setWidth 64) 0 20 s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  refine WP.seq (WP.mono (init_ok v C positive) fun u ⟨U, O, K⟩ => ?_)
  refine WP.mono (loop_ok v U) fun t ⟨T, Ot, Kt⟩ => ?_
  refine ⟨T.context, ?_, O.trans Ot, (K.mono (by decide)).trans Kt⟩
  simpa only [Nat.sub_self, Nat.mul_zero, Nat.pow_zero, Nat.div_one] using T.value

end VG.Proof.RsaKeyGen.X86.Mod64
