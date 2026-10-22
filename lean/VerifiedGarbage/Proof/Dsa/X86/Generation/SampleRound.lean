module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.SampleRoundFrame
public import VerifiedGarbage.Proof.Dsa.X86.Generation.ControlKeeps
import VerifiedGarbage.Proof.Mont.X86.ContextLayout

/-! Sample, encode, and test a witness using the shared prepared-round variant. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation VG.Impl.Dsa.Generation
open VG.Impl.Mont.X86.Dynamic VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.MillerRabin.X86

def sampledWitness (candidate : Nat) (m : Mem) (base : Addr) (len : Nat) : Nat × Bool :=
  Spec.RsaKeyGen.witness (candidate - 1) (Spec.Rsa.os2ip (Spec.Rsa.bytesAt m (off base Layout.witness) len))

theorem sample_round (v : RoundImpl) {s : State} {base : Addr} {bytes n len candidate : Nat}
    (scr : Scr s base bytes) (capacity : 40960 ≤ bytes) (S : PrimeState base n candidate s)
    (room : RoundRoom (s.gpr .esp) base bytes)
    (positive : 0 < n) (upper : n ≤ 48) (lower : 4 ≤ len)
    (length : len ≤ 8 * n) (aligned : len % 4 = 0)
    (bits : Spec.RsaKeyGen.bitLength (candidate - 1) = 8 * len) :
    WP isa (sampleRound v.name v.code n len) s fun t =>
      PrimeState base n candidate t ∧
      t.gpr .eax = BitVec.ofNat 32 (Spec.MillerRabin.round candidate (sampledWitness candidate s.mem base len).1).toNat ∧
      w32 t.mem base witnessUniform = (if (sampledWitness candidate s.mem base len).2 then 1 else 0) ∧
      SampleRoundFrame base (s.gpr .esp) len s t ∧
      ControlKeeps base s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] s t := by
  have odd : candidate % 2 = 1 := by
    have odd := S.core.odd
    rw [S.width, S.candidate] at odd
    exact odd
  unfold sampleRound
  refine WP.seq (WP.mono (sample_witness scr capacity S.context positive upper lower length aligned bits)
    fun u ⟨Cu, raw, uniform, Fs, Ffine, Ks⟩ => ?_)
  have U := S.sample Cu Fs
  have Su := scr.of_keeps Ks (by decide)
  have Ru : RoundRoom (u.gpr .esp) base bytes := by rw [Ks.1 .esp (by decide)]; exact room
  refine WP.seq (WP.mono (encode_witness (x := (sampledWitness candidate s.mem base len).1)
    Su capacity Ru.callRoom Cu positive upper odd (by rw [← wordsVal_eq_val32]; exact raw))
    fun a ⟨Ca, encoded, bound, Fa, Ka⟩ => ?_)
  have A := U.encoded Ca Fa Ru.callRoom capacity upper
  have Kpre : Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] s a := Ks.trans (Ka.mono (by decide))
  have Sa := scr.of_keeps Kpre (by decide)
  have Ra : RoundRoom (a.gpr .esp) base bytes := by rw [Kpre.1 .esp (by decide)]; exact room
  have prepared := A.core.prepared (by rw [A.width, A.candidate]; exact bound)
  have uniformA : w32 a.mem base witnessUniform = (if (sampledWitness candidate s.mem base len).2 then 1 else 0) := by
    unfold w32 Mem.readW
    rw [witness_middle_read (d := witnessUniform) (size := 4) capacity Ru.callRoom upper Fa (by decide) (by decide)]
    exact uniform
  refine WP.mono (round_call v Sa capacity Ra A.layout prepared upper A.width A.candidate)
    fun t ⟨Kt, Ft, value, kept⟩ => ?_
  have flag : w32 t.mem base witnessUniform = w32 a.mem base witnessUniform := by
    unfold w32 Mem.readW
    rw [round_middle_read (d := witnessUniform) (size := 4) capacity Ra Ft (by decide)]
  have result := value (sampledWitness candidate s.mem base len).1 (by
    simpa only [Nat.mul_mod, Nat.mod_mod] using encoded)
  refine ⟨A.afterRound capacity Ra Ft Kt kept, ?_, flag.trans uniformA, ?_, ?_,
    Kpre.trans (Kt.mono (by decide))⟩
  · apply BitVec.eq_of_toNat_eq
    rw [result]
    cases Spec.MillerRabin.round candidate (sampledWitness candidate s.mem base len).1 <;> rfl
  · have Fsu : SampleRoundFrame base (s.gpr .esp) len s u := sampling_round_frame Ffine upper
    have Fua : SampleRoundFrame base (s.gpr .esp) len u a := by
      have F := encoding_round_frame (len := len) Fa upper Ru.low
      rw [Ks.1 .esp (by decide)] at F
      exact F
    have Fat : SampleRoundFrame base (s.gpr .esp) len a t := by
      have F := called_round_frame (len := len) Ft
      rw [Kpre.1 .esp (by decide)] at F
      exact F
    exact (Fsu.trans Fua).trans Fat
  · exact ((sampling_control Ffine upper (by omega)).trans (encoding_control capacity Ru.callRoom upper Fa)).trans
      (called_control capacity Ra Ft)

end VG.Proof.Dsa.X86.Generation
