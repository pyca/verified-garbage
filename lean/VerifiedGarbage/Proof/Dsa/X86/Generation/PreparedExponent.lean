module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.Exponent
public import VerifiedGarbage.Proof.Dsa.X86.Generation.ExponentOneHot

/-! Retain the shared window exponent and its complete one-hot metadata. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.KeyRt
open VG.Proof.Rsa.X86.Keys (Keep num slot)
open VG.Impl.Rsa.X86.KeyRt (Lay)
open VG.Proof.RsaKeyGen (mrA)

theorem prepare_exponent {L : Lay} {s : State} {base : Addr} {bytes len count candidate : Nat}
    (h : RtWs L s base bytes len count) (arrays : 3 ≤ count)
    (current : num s.mem base (kw len) 2 = candidate) (factors : slot s.mem base 20 = mrA candidate)
    (odd : candidate % 2 = 1) :
    WP isa (Impl.Dsa.X86.Generation.prepareExponent L) s fun t =>
      RtWs L t base bytes len count ∧ Keep base (kw len) [0, 1] [32, 28, 64, 68] s.mem t.mem ∧
      num t.mem base (kw len) 0 = Spec.MillerRabin.exponent candidate ∧
      num t.mem base (kw len) 2 = candidate ∧
      (word t.mem base 64).toNat = 2 ^ (mrA candidate % 64) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  unfold Impl.Dsa.X86.Generation.prepareExponent
  refine WP.seq (WP.mono (exponent_setup h arrays current factors odd) ?_)
  rintro u ⟨hu, F, exponent, twos, modulus, _, K⟩
  refine WP.mono (exponent_one_hot hu) ?_
  rintro t ⟨ht, F', power, K'⟩
  rw [twos] at power
  exact ⟨ht, F.join F', (F'.num (j := 0) (by simp) (by decide) (h.ws.fit64 (by omega))).trans exponent,
    (F'.num (j := 2) (by simp) (by decide) (h.ws.fit64 (by omega))).trans modulus,
    power, K.trans (K'.mono (by decide))⟩

end VG.Proof.Dsa.X86.Generation
