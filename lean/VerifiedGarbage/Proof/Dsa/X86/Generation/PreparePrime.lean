module

public import VerifiedGarbage.Impl.Dsa.X86.Generation.PreparePrime
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimePreparation
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeState
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Mont.OutsFrame
import VerifiedGarbage.Proof.Mont.X86.ContextLayout

/-! Initialize the reusable state consumed by the streamed witness loop. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation VG.Impl.Dsa.Generation VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic

theorem prepare_prime {s : State} {base : Addr} {bytes n candidate bits : Nat}
    (scr : Scr s base bytes) (capacity : 40960 ≤ bytes) (room : CallRoom (s.gpr .esp) base bytes)
    (stack : StkOk (s.gpr .esp - 16#32) base bytes) (lower : 4 ≤ n) (upper : n ≤ 48)
    (modulus : wordsVal s.mem base (slot n 0) n = candidate) (large : 3 ≤ candidate)
    (odd : candidate % 2 = 1) (bitsLow : 2 ≤ bits) (bitsHigh : bits ≤ 64 * n)
    (top : 2 ^ (bits - 1) ≤ candidate) :
    WP isa (preparePrime n bits) s fun t =>
      PrimeState base n candidate t ∧ PreparationFrame base (s.gpr .esp) s t ∧ Keeps powerClob s t := by
  unfold preparePrime
  refine WP.seq (WP.mono (prime_preparation scr capacity room stack lower upper modulus large odd bitsLow bitsHigh top)
    fun a ⟨Ca, La, Pa, Wa, candidateA, Fa, Ka⟩ => ?_)
  have Sa := scr.of_keeps Ka (by decide)
  refine WP.mono (witness_init Sa (by unfold montgomeryBytes; omega) Ca (by omega)) fun t ⟨Ct, Ft, Kt⟩ => ?_
  have beforeArithmetic : SampleFrame base a t := sample_outside Ft (by simp only [slot, stride, Layout.arithmetic]; omega)
  obtain ⟨Lt, Pt, Wt⟩ := sample_prepared beforeArithmetic La Pa
  have fit : Spec.Rsa.Mont.arrAt n 28 ≤ 12288 := by
    have fit : Spec.Rsa.Mont.arrAt (Spec.Rsa.Mont.wOf a.mem (off base Layout.arithmetic)) 28 ≤ 12288 := La.2.2.2.2.1
    rw [Wa] at fit; exact fit
  have value := (VG.Proof.MillerRabin.kept_number (sample_keeps beforeArithmetic n) fit (j := 0) (.inl rfl)).trans candidateA
  have Fparent : Frame [⟨base, montgomeryBytes⟩] a.mem t.mem := by
    apply (Ft.frameAt (by simp only [slot, stride]; omega)).sub
    intro r hr
    rw [List.mem_singleton.mp hr]
    exact ⟨_, List.mem_singleton_self _, Offset.sub_base base (by simp only [slot, stride, montgomeryBytes]; omega)⟩
  exact ⟨⟨Ct, Lt, VG.Proof.MillerRabin.prepared_core Pt, Wt.trans Wa, value⟩,
    Fa.trans (preparation_parent_frame Fparent), Ka.trans (Kt.mono (by decide))⟩

end VG.Proof.Dsa.X86.Generation
