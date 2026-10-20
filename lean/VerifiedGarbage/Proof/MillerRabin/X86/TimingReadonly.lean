module

public import VerifiedGarbage.Proof.MillerRabin.X86.TimingBase
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # Retain the prepared geometry across read-only timing blocks -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Proof.Dsa.X86

theorem readonly_relCT {g : Geometry} {code : Prog isa} {before after : List Reg}
    (raw : RelCT isa (VG.X86.Taint.Agree (roundTaint before)) code (VG.X86.Taint.Agree (roundTaint after)))
    (correct : ∀ s, Context g s → WP isa code s fun t => t.mem = s.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t) :
    RelCT isa (Pair g before) code (Pair g after) := by
  intro s t tr ur u z H E G
  obtain ⟨trace, A⟩ := raw _ _ _ _ _ _ H.2.2 E G
  obtain ⟨Mu, Ku⟩ := wp_result (correct s H.1) E
  obtain ⟨Mz, Kz⟩ := wp_result (correct t H.2.1) G
  exact ⟨trace, H.1.keepMem Ku (by decide) Mu, H.2.1.keepMem Kz (by decide) Mz, A⟩

end VG.Proof.MillerRabin.X86
