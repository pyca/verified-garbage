module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.PrepareHeader
public import VerifiedGarbage.Proof.RsaKeyGen.X86.PrepareData
public import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedR2Timing
import VerifiedGarbage.Proof.RsaKeyGen.X86.PrepareHeader
import VerifiedGarbage.Proof.RsaKeyGen.X86.PrepareHeaderTiming
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # Fresh candidates acquire identical public prepared metadata -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Prepare
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86 VG.Proof.Dsa.X86

def Initial (g : Geometry) (capacity : Nat) (p : BitVec 32) (s : State) : Prop := ∃ c, Input g c capacity p s

def InitialPair (g : Geometry) (capacity : Nat) (p : BitVec 32) (s t : State) : Prop :=
  VG.X86.Taint.Agree (roundTaint [.edi]) s t ∧ Initial g capacity p s ∧ Initial g capacity p t

theorem header_pair {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32}
    (length : g.L = 8 * capacity) :
    RelCT isa (InitialPair g capacity p) (VG.Impl.RsaKeyGen.X86.PrepareHeader.code g.w)
      (PreparedR2.InputPair g capacity p) := by
  intro s t tr ur u z ⟨H, S, T⟩ E G
  obtain ⟨trace, agree⟩ := PrepareHeader.code_trace g.w _ _ _ _ _ _ H E G
  have post {a : State} (I : Initial g capacity p a) :
      WP isa (VG.Impl.RsaKeyGen.X86.PrepareHeader.code g.w) a (PreparedR2.Input g capacity p) := by
    obtain ⟨c, I⟩ := I
    exact WP.mono (PrepareHeader.code_ok v I.scratch I.caller length I.candidate I.odd)
      fun _ ⟨R, _, _⟩ => ⟨c, R, I.odd, I.top⟩
  obtain ⟨cu, Cu, ou, tu⟩ := wp_result (post S) E
  obtain ⟨cz, Cz, oz, tz⟩ := wp_result (post T) G
  exact ⟨trace, ⟨Cu.context, Cz.context, agree⟩, ⟨cu, Cu, ou, tu⟩, ⟨cz, Cz, oz, tz⟩⟩

end VG.Proof.RsaKeyGen.X86.Prepare
