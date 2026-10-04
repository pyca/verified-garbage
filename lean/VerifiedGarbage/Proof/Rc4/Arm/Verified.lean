import VerifiedGarbage.Proof.Rc4.Arm.ConstantTime

/-! # RC4 on ARMv7: `Verified` -/

namespace VG.Proof.Rc4.Arm

open VG VG.Arm VG.Impl.Rc4.Arm VG.Spec.Rc4 VG.Proof.Rc4

theorem init_correct (s : State) (hs : initC.pre s) :
    ∃ t s', Exec isa VG.Impl.Rc4.Arm.init s t s' ∧ abiPreserved s s' ∧ initC.post s s' := by
  obtain ⟨t, s', he, hpost, hpres, hsp⟩ := init_ok s hs
  refine ⟨t, s', he, ⟨hpres, hsp⟩, ?_⟩
  unfold initC
  dsimp only
  revert hpost
  cases Spec.Rc4.init (bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat) with
  | ok c => intro hpost; exact ⟨by rw [ret_low, hpost.1]; rfl, hpost.2⟩
  | error e => cases e; intro hpost; rw [ret_low, hpost]; rfl

theorem apply_correct (s : State) (hs : applyC.pre s) :
    ∃ t s', Exec isa VG.Impl.Rc4.Arm.apply s t s' ∧ abiPreserved s s' ∧ applyC.post s s' := by
  obtain ⟨t, s', he, hpost, hpres, hsp⟩ := apply_ok s hs
  exact ⟨t, s', he, ⟨hpres, hsp⟩, hpost⟩

theorem init_verified : Verified target VG.Impl.Rc4.Arm.init (initScratchContract abi) := by
  refine Verified.of_correct init_correct init_ct ?_
  sig_implies [initScratchContract, initScratchSig, initPost, abi, argRegs, Arm.reduceClassify,
    Arm.Loc.val, initC, State.addr] [initSat] using initSat

theorem apply_verified : Verified target VG.Impl.Rc4.Arm.apply (applyScratchContract abi) := by
  refine Verified.of_correct apply_correct apply_ct ?_
  sig_implies [applyScratchContract, applyScratchSig, applyPost, applyLeak, abi, argRegs,
    Arm.reduceClassify, Arm.Loc.val, applyC, State.addr] [applySat] using applySat

end VG.Proof.Rc4.Arm
