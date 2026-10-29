module
public import VerifiedGarbage.Impl.MillerRabin.X86_64.Round
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Contract
public import VerifiedGarbage.Proof.RsaKeyGen.Slots
public import VerifiedGarbage.Proof.RsaKeyGen.Table

import VerifiedGarbage.Proof.MillerRabin.X86_64.StageFrame
import VerifiedGarbage.Proof.MillerRabin.X86_64.BoundaryCT
import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp

/-! # The whole inlined callable has only its declared public inputs -/

@[expose] public section

namespace VG.Proof.MillerRabin.X86_64

open VG VG.X86_64 VG.Impl.MillerRabin.X86_64 VG.Proof.Bignum.X86_64

private def RoundState (p : BodyPub) (s : State) : Prop :=
  roundPre s ∧ inputPub s = p

private theorem round_rel (M : Mont) :
    RelCT isa (Two RoundState) (round M.mm) fun _ _ => True := by
  unfold round
  refine RelCT.seq (two_post (Ψ := FramePre) ?_ ?_) (frames_ct M)
  · refine stage_ct.mono ?_ (fun _ _ h => h)
    rintro s t ⟨p, hs, ht⟩
    refine ⟨p.B, ?_, ?_⟩
    · exact congrArg BodyPub.B hs.2
    · exact congrArg BodyPub.B ht.2
  · intro p s h
    rw [← h.2]
    exact stage_frame_ok h.1

private theorem inputPub_eq {s t : State} (hp : roundPub s t) : inputPub s = inputPub t := by
  obtain ⟨hsp, hdi, hsi, hw⟩ := hp
  unfold inputPub
  congr 1
  · rw [hsi]
  · rw [hsp, hdi, hsi]
  · rw [hsp]

theorem round_ct (M : Mont) : ConstantTime isa roundPre roundPub (round M.mm) := by
  apply RelCT.constantTime
  refine (round_rel M).mono ?_ (fun _ _ h => h)
  rintro s t ⟨hs, ht, hp⟩
  exact ⟨inputPub s, ⟨hs, rfl⟩, ht, (inputPub_eq hp).symm⟩

end VG.Proof.MillerRabin.X86_64
