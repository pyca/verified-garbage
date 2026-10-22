module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.ExponentStart
public import VerifiedGarbage.Proof.Dsa.X86.Generation.ExponentHalf
public import VerifiedGarbage.Spec.MillerRabin

/-! The native exponent setup matches the shared Miller–Rabin workspace. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.KeyRt
open VG.Proof.Rsa.X86.Keys (Keep num slot)
open VG.Impl.Rsa.X86.KeyRt (Lay)
open VG.Proof.RsaKeyGen (mrA mrSig mrE sigOf_pos mrE_halves)

theorem exponent_setup {L : Lay} {s : State} {base : Addr} {bytes len count candidate : Nat}
    (h : RtWs L s base bytes len count) (arrays : 3 ≤ count)
    (current : num s.mem base (kw len) 2 = candidate) (factors : slot s.mem base 20 = mrA candidate)
    (odd : candidate % 2 = 1) :
    WP isa (Impl.Dsa.X86.Generation.exponentSetup L) s fun t =>
      RtWs L t base bytes len count ∧ Keep base (kw len) [0, 1] [32, 28] s.mem t.mem ∧
      num t.mem base (kw len) 0 = Spec.MillerRabin.exponent candidate ∧
      slot t.mem base 20 = mrA candidate ∧ num t.mem base (kw len) 2 = candidate ∧
      slot t.mem base 32 = mrSig candidate ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  have hs : 1 ≤ mrSig candidate ∧ mrSig candidate ≤ 4 := sigOf_pos (mrA candidate)
  unfold Impl.Dsa.X86.Generation.exponentSetup
  refine WP.seq (WP.mono (exponent_start h arrays current factors) ?_)
  rintro a ⟨ha, F, value, shift, K⟩
  refine WP.seq (WP.mono (exponent_half ha (by omega) value shift hs (by decide : 1 ≤ 1 ∧ 1 ≤ 3)) ?_)
  rintro b ⟨hb, F', value', shift', K'⟩
  refine WP.seq (WP.mono (exponent_half hb (by omega) value' shift' hs (by decide : 1 ≤ 2 ∧ 2 ≤ 3)) ?_)
  rintro c ⟨hc, F'', value'', shift'', K''⟩
  refine WP.mono (exponent_half hc (by omega) value'' shift'' hs (by decide : 1 ≤ 3 ∧ 3 ≤ 3)) ?_
  rintro t ⟨H, F''', result, sigma, K'''⟩
  have frame : Keep base (kw len) [0, 1] [32, 28] s.mem t.mem := F.join ((F'.trans F'').trans F''')
  have exponent : num t.mem base (kw len) 0 = Spec.MillerRabin.exponent candidate := by
    calc
      _ = _ := result
      _ = mrE candidate := mrE_halves odd
      _ = _ := rfl
  exact ⟨H, frame, exponent, (frame.slot (by decide) (by decide)).trans factors,
    (frame.num (j := 2) (by decide) (by decide) (h.ws.fit64 (by omega))).trans current,
    sigma, ((K.trans K').trans K'').trans K'''⟩

end VG.Proof.Dsa.X86.Generation
