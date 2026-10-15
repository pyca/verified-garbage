module

public import VerifiedGarbage.Proof.Dsa.X86.CoreInputs
public import VerifiedGarbage.Proof.Dsa.X86.CoreStore
public import VerifiedGarbage.Proof.Dsa.X86.CorePowerFrame

/-! # Complete modular exponentiation call, including byte I/O -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem corePower_ok {s : State} {base : Addr} {size len expLen n m output : Nat} {a b : Pointer} {modulus : Field}
    (hs : Scr s base size) (hz : VG.Impl.Dsa.X86.Layout.saved ≤ size)
    (hn : n = (len + 7) / 8) (h4 : 4 ≤ len) (hmax : len ≤ 384)
    (he4 : 4 ≤ expLen) (he : expLen ≤ len)
    (Rq : OperandReady s base n (.input modulus) len)
    (Ra : OperandReady s base n a len) (Rb : OperandReady s base n b expLen)
    (hm : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s (.input modulus)).setWidth 64) len) = m)
    (hm1 : 1 < m) (hodd : m % 2 = 1)
    (ho : output + len ≤ size) (hfar : contextBytes n ≤ output) :
    WP isa (Core.power len expLen modulus a b output) s fun t =>
      Spec.Rsa.bytesAt t.mem (off base output) len = Spec.Dsa.encodeBE len
        (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s a).setWidth 64) len) ^
          Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s b).setWidth 64) expLen) % m) ∧
      Outs base [(0, contextBytes n), (output, len)] s.mem t.mem ∧ Keeps powerClob s t := by
  have hn48 : n ≤ 48 := by omega
  have hl : len ≤ 8 * n := by omega
  have b6 := slot_bound (n := n) (i := 6) (by decide)
  simp only [stride] at b6
  unfold Core.power
  dsimp only
  rw [← hn]
  refine WP.seq (WP.mono (coreSetup_ok hs hz hn h4 hmax Rq.toReadableComponent (Rq.slot (by decide)) hm hm1 hodd)
    fun u ⟨Cu, Oneu, R2u, Ou, Ku⟩ => ?_)
  have Rau := Ra.keep Ku (by decide) Ou hn48
  have Rbu := Rb.keep Ku (by decide) Ou hn48
  refine WP.seq (WP.mono (coreInputs_ok Cu hz hn48 h4 hl he4 (by omega) Rau Rbu)
    fun v ⟨Cv, Av, Bv, Constv, Ov, Kv⟩ => ?_)
  have R2v : wordsVal v.mem base (slot n 4) n = 2 ^ (128 * n) % m := by
    rw [Constv 4 (.inr rfl), R2u]
  rw [Ra.bytes Ku (by decide) Ou hn48] at Av
  rw [Rb.bytes Ku (by decide) Ou hn48] at Bv
  have Onev : wordsVal v.mem base (slot n 3) n = 1 := by
    rw [Constv 3 (.inl rfl), Oneu]
  have ek : (expLen + 3) / 4 ≤ 2 * n := by omega
  have Ev : val32 v.mem base (slot n 8) ((expLen + 3) / 4) =
      Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s b).setWidth 64) expLen) := by
    rw [wordsVal_eq_val32] at Bv
    rw [val32_prefix_of_lt ek (by rw [Bv]; exact decoded_exponent_fits _ _ _), Bv]
  refine WP.seq (WP.mono (exponentiate_ok Cv (by omega) ek (by omega) Onev R2v)
    fun w ⟨Cw, Vw, Ow, Kw⟩ => ?_)
  have bw : slot n 6 + 8 * n ≤ size := Nat.le_trans (by omega) Cw.size_le
  refine WP.mono (coreStore_ok Cw.scr hz bw h4 hl ho (by omega)) fun t ⟨Vt, Kt, Ot⟩ => ?_
  refine ⟨by rw [Vt, Vw, Av, Ev], ?_, ?_⟩
  · have Opre := (Ou.trans Ov).trans (exponentRanges_whole Ow ek)
    exact (Outs.of_outside Opre (by simp)).trans (Outs.of_outside Ot (by simp))
  · exact (((Ku.trans (Kv.mono (by decide))).trans (Kw.mono (by decide))).trans (Kt.mono (by decide)))

end VG.Proof.Dsa.X86
