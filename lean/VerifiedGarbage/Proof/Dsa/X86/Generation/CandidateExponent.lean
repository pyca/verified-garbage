module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.PreparedExponent
public import VerifiedGarbage.Proof.Dsa.X86.Generation.Halving
public import VerifiedGarbage.Proof.Dsa.X86.Generation.CandidateExponentStart

/-! A fresh odd candidate yields both exponent fields required by the shared round. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.KeyRt
open VG.Proof.Rsa.X86.Keys (Keep num slot)
open VG.Impl.Rsa.X86.KeyRt (Lay)
open VG.Proof.RsaKeyGen (mrA)

theorem prepare_candidate_exponent {L : Lay} {s : State} {base : Addr} {bytes len count candidate : Nat}
    (h : RtWs L s base bytes len count) (arrays : 3 ≤ count)
    (current : num s.mem base (kw len) 0 = candidate) (large : 3 ≤ candidate)
    (odd : candidate % 2 = 1) (bits : 32 * kw len ≤ 16384) :
    WP isa (Impl.Dsa.X86.Generation.prepareCandidateExponent L) s fun t =>
      RtWs L t base bytes len count ∧ Keep base (kw len) [0, 1, 2] [28, 20, 56, 32, 64, 68] s.mem t.mem ∧
      num t.mem base (kw len) 0 = Spec.MillerRabin.exponent candidate ∧
      num t.mem base (kw len) 2 = candidate ∧
      (word t.mem base 64).toNat = 2 ^ (mrA candidate % 64) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  unfold Impl.Dsa.X86.Generation.prepareCandidateExponent
  refine WP.seq (WP.mono (candidate_exponent_start h arrays current) ?_)
  rintro b ⟨hb, F, even, cb, K⟩
  have before : num b.mem base (kw len) 0 = candidate - 1 := by omega
  refine WP.seq (WP.mono (halving hb (by omega) before (by omega) bits) ?_)
  rintro c ⟨hc, F', K'⟩
  have cc := (F'.num (j := 2) (by decide) (by decide) (h.ws.fit64 (by omega))).trans cb
  refine WP.mono (prepare_exponent hc.workspace arrays cc hc.twos odd) ?_
  rintro t ⟨ht, F'', exponent, modulus, power, K''⟩
  exact ⟨ht, (F.join F' (js := [0, 1, 2]) (ds := [28, 20, 56, 32, 64, 68])).join F'',
    exponent, modulus, power, (K.trans K').trans K''⟩

end VG.Proof.Dsa.X86.Generation
