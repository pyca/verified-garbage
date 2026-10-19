module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorModulus
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorFootprint
import VerifiedGarbage.Proof.Framework.Omega

/-! # Initialize and evaluate one generator power from arbitrary scratch -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64

theorem generatorPowerFresh_ok (M : Mont) {s : State} {B hp : Addr}
    {len : Nat} {pb hb eb : List Byte}
    (hs : Scr s B activeBytes) (hdi : s.gpr .x0 = B)
    (hl : len = 128 ∨ len = 256 ∨ len = 384)
    (hpl : pb.length = len) (hhl : hb.length = len) (hel : eb.length = len)
    (hm : 1 < Spec.Dsa.decodeBE pb) (hodd : Spec.Dsa.decodeBE pb % 2 = 1)
    (hptr : word s.mem B 272 = hp)
    (sp : Src s B activeBytes (off B VG.Impl.Dsa.Generation.Layout.p) pb)
    (sh : Src s B activeBytes hp hb)
    (se : Src s B activeBytes (off B VG.Impl.Dsa.Generation.Layout.exponent) eb)
    (hout : ∀ i < len, InRegions s.wr (off (off B VG.Impl.Dsa.Generation.Layout.g) i) 1)
    (houtside : ∀ i < len, activeBytes ≤ ofs B (off (off B VG.Impl.Dsa.Generation.Layout.g) i)) :
    WP isa (Impl.Dsa.AArch64.Generation.generatorPowerFresh M.mm len) s fun t =>
      Spec.Rsa.bytesAt t.mem (off B VG.Impl.Dsa.Generation.Layout.g) len =
        Spec.Dsa.encodeBE len (Spec.Dsa.powMod (Spec.Dsa.decodeBE hb) (Spec.Dsa.decodeBE eb) (Spec.Dsa.decodeBE pb)) ∧
      Frame [⟨B, activeBytes⟩, ⟨off B VG.Impl.Dsa.Generation.Layout.g, len⟩] s.mem t.mem ∧
      Keep coreRegs s t := by
  unfold Impl.Dsa.AArch64.Generation.generatorPowerFresh
  refine WP.seq (WP.mono (generatorModulus_ok hs hdi hl hpl sp hodd)
    fun u ⟨mi, gu, child, _, ep, plen, gh, fu, ku⟩ => ?_)
  have bounds : ∀ r ∈ [(48, 80), (256, 80)] ++ initRanges pWorkspace (len / 8), r.1 + r.2 ≤ activeBytes := by
    intro r hr
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, initRanges] at hr
    rcases hr with (rfl | rfl) | (rfl | rfl)
    · decide
    · decide
    · decide
    · rcases hl with hh | hh | hh <;> rw [hh] <;> decide
  have shu := sh.congrK (InScr.of_frm fu bounds) ku
  have seu := se.congrK (InScr.of_frm fu bounds) ku
  have has : OperandBytes u B activeBytes ⟨.input .g, .pLen⟩ hb := by
    refine ⟨?_, ?_⟩
    · change word u.mem B 328 = _
      rw [hhl]; exact plen
    · change Src u B activeBytes (word u.mem B 272) hb
      rw [gh, hptr]; exact shu
  have hes : OperandBytes u B activeBytes ⟨.input .x, .pLen⟩ eb := by
    refine ⟨?_, ?_⟩
    · change word u.mem B 328 = _
      rw [hel]; exact plen
    · change Src u B activeBytes (word u.mem B 288) eb
      rw [ep]; exact seu
  refine WP.mono (generatorPower_ok M gu child hl hm hodd has hes hhl hel
    (fun i hi => by rw [ku.wr]; exact hout i hi) houtside)
    fun t ⟨_, _, result, ft, kt⟩ => ?_
  have ff : Frame [⟨B, activeBytes⟩, ⟨off B VG.Impl.Dsa.Generation.Layout.g, len⟩] s.mem u.mem := by
    intro a ha
    apply fu a
    intro r hr
    right
    have hn := ha ⟨B, activeBytes⟩ (by simp)
    change ¬ ofs B a < activeBytes at hn
    exact Nat.le_trans (bounds r hr) (by omega)
  exact ⟨result, ff.trans (generator_power_frame hl ft), (ku.trans kt).mono (by decide)⟩

end VG.Proof.Dsa.AArch64.Generation
