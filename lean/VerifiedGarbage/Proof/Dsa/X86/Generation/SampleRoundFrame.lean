module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeState
import VerifiedGarbage.Proof.Framework.Offset

/-! A witness iteration retains saved parameter bytes outside its small working regions. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation VG.Impl.Dsa.Generation
open VG.Impl.Mont.X86.Dynamic VG.Proof.Mont VG.Proof.Mont.X86

def SampleRoundFrame (base : Addr) (sp : BitVec 32) (len : Nat) (s t : State) : Prop :=
  Frame [⟨base, montgomeryBytes⟩, ⟨off base Layout.arithmetic, 12288⟩,
    ⟨off base Layout.witness, len⟩, ⟨off base Layout.control, 512⟩, below sp 1184] s.mem t.mem

theorem sampling_round_frame {s t : State} {base : Addr} {sp : BitVec 32} {n len : Nat}
    (F : SamplingFrame base n len s t) (upper : n ≤ 48) : SampleRoundFrame base sp len s t := by
  apply F.sub
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨⟨base, montgomeryBytes⟩, by simp, Offset.sub_base base (by
      simp only [slot, stride, montgomeryBytes]; omega)⟩
  · exact ⟨⟨off base Layout.witness, len⟩, by simp, fun _ h => h⟩
  · exact ⟨⟨off base Layout.control, 512⟩, by simp,
      Offset.sub base (by decide : Layout.control ≤ witnessUniform) (by decide)⟩

theorem encoding_round_frame {s t : State} {base : Addr} {n len : Nat}
    (F : WitnessFrame base (s.gpr .esp) n s t) (upper : n ≤ 48)
    (low : 1184 ≤ (s.gpr .esp).toNat) : SampleRoundFrame base (s.gpr .esp) len s t := by
  apply F.sub
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨⟨base, montgomeryBytes⟩, by simp, Offset.sub_base base (by
      simp only [slot, stride, montgomeryBytes]; omega)⟩
  · exact ⟨⟨base, montgomeryBytes⟩, by simp, Offset.sub_base base (by
      simp only [montgomeryScratch, Spec.Rsa.MontMul.scratchBytes, montgomeryBytes]; omega)⟩
  · exact ⟨⟨off base Layout.arithmetic, 12288⟩, by simp, Offset.sub base (by omega)
      (by simp only [Spec.Rsa.Mont.arrAt, Spec.Rsa.Mont.hdrBytes]; omega)⟩
  · exact ⟨below (s.gpr .esp) 1184, by simp, below_sub (by decide) low⟩

theorem called_round_frame {s t : State} {base : Addr} {len : Nat}
    (F : Frame [⟨off base Layout.arithmetic, 12288⟩, below (s.gpr .esp) 1184] s.mem t.mem) :
    SampleRoundFrame base (s.gpr .esp) len s t := F.mono (by simp)

end VG.Proof.Dsa.X86.Generation
