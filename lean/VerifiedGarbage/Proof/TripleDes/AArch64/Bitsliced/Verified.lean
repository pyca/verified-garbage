import VerifiedGarbage.Proof.TripleDes.AArch64.Bitsliced.Loop
import VerifiedGarbage.Proof.TripleDes.AArch64.Bitsliced.ConstantTime
import VerifiedGarbage.Proof.TripleDes.AArch64.Ecb.Contract
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.TripleDes.Scratch

/-! # The AdvSIMD bitsliced ECB functions meet their contracts -/

namespace VG.Proof.TripleDes.AArch64.BitslicedNeon

open VG VG.AArch64 VG.Impl.TripleDes.AArch64.BitsliceNeon VG.Spec.TripleDes
open VG.Proof.TripleDes.Bitslice (blockOut wAt wAt_wAt blockAt_frame ecb_blocks)
open VG.Proof.TripleDes.AArch64.Ecb (contract)

def satState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x3 => 0x3000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x1000, 384⟩]
  wr := [⟨0x2000, 0⟩, ⟨0x3000, 1024⟩]

theorem publicRegs_four (s₁ s₂ : State) :
    VG.Proof.TripleDes.AArch64.PublicRegs [.x0, .x1, .x2, .x3] s₁ s₂ ↔
      s₁.sp = s₂.sp ∧ s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧
        s₁.gpr .x2 = s₂.gpr .x2 ∧ s₁.gpr .x3 = s₂.gpr .x3 := by
  simp [VG.Proof.TripleDes.AArch64.PublicRegs]

theorem ecb_contract (d : Direction) (s : State) (hs : (contract d).pre s) :
    WP isa (ecb d) s (fun s' => (contract d).post s s') := by
  obtain ⟨hrd, hwr, keyData, keyBuf, dataBuf, fit⟩ := hs
  exact WP.mono (ecb_correct d ⟨hrd, hwr, keyData, keyBuf, dataBuf, fit⟩) fun s' h =>
    ecb_blocks _ _ _ _ _ _ h

theorem encrypt_correct (s : State) (hs : (contract .encrypt).pre s) :
    ∃ t s', Exec isa encrypt s t s' ∧ abiPreserved s s' ∧ (contract .encrypt).post s s' := by
  obtain ⟨t, s', he, hp, hg⟩ := WP.gprs (c := encrypt) (ecb_contract .encrypt s hs) (rs := preserved)
    (by lit_decide) (by lit_decide)
  exact ⟨t, s', he, ⟨hg, VG.AArch64.Exec.sp he, VG.AArch64.Exec.preservedV he (by lit_decide)⟩, hp⟩

theorem decrypt_correct (s : State) (hs : (contract .decrypt).pre s) :
    ∃ t s', Exec isa decrypt s t s' ∧ abiPreserved s s' ∧ (contract .decrypt).post s s' := by
  obtain ⟨t, s', he, hp, hg⟩ := WP.gprs (c := decrypt) (ecb_contract .decrypt s hs) (rs := preserved)
    (by lit_decide) (by lit_decide)
  exact ⟨t, s', he, ⟨hg, VG.AArch64.Exec.sp he, VG.AArch64.Exec.preservedV he (by lit_decide)⟩, hp⟩

theorem encrypt_verified : Verified target encrypt (Proof.TripleDes.ecbEncryptScratchContract abi 0) := by
  refine Verified.of_correct encrypt_correct (encrypt_constantTime _) ?_
  sig_implies [Proof.TripleDes.ecbEncryptScratchContract, Proof.TripleDes.ecbScratchContract,
    Proof.TripleDes.ecbScratchSig, Spec.TripleDes.ecbPost, abi, argRegs, contract, publicRegs_four] [satState] using satState

theorem decrypt_verified : Verified target decrypt (Proof.TripleDes.ecbDecryptScratchContract abi 0) := by
  refine Verified.of_correct decrypt_correct (decrypt_constantTime _) ?_
  sig_implies [Proof.TripleDes.ecbDecryptScratchContract, Proof.TripleDes.ecbScratchContract,
    Proof.TripleDes.ecbScratchSig, Spec.TripleDes.ecbPost, abi, argRegs, contract, publicRegs_four] [satState] using satState

end VG.Proof.TripleDes.AArch64.BitslicedNeon
