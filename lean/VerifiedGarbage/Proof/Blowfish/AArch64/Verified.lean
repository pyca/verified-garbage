import VerifiedGarbage.Proof.Blowfish.AArch64.EcbMain
import VerifiedGarbage.Proof.Blowfish.AArch64.ConstantTime
import VerifiedGarbage.Proof.Blowfish.EcbScratch
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Framework.Contract

/-! # The ECB functions meet their contracts, with the working space as an argument -/

namespace VG.Proof.Blowfish.AArch64

open VG VG.AArch64 VG.Impl.Blowfish.AArch64 VG.Spec.Blowfish VG.Proof.Blowfish

def dir (up : Bool) : Direction := if up then .encrypt else .decrypt

/-- The ECB contract as the code sees it. -/
def ecbC (up : Bool) : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .x0, 4168⟩
    let data : Region := ⟨s.gpr .x1, 8 * (s.gpr .x2).toNat⟩
    let buf : Region := ⟨s.gpr .x3, 256⟩
    s.rd = [key] ∧ s.wr = [data, buf] ∧ key.Disjoint data ∧ key.Disjoint buf ∧
      data.Disjoint buf ∧
      (s.gpr .x1).toNat + 8 * (s.gpr .x2).toNat ≤ 2 ^ 64
  post s s' :=
    blocksAt s'.mem (s.gpr .x1) (s.gpr .x2).toNat =
      ecb (scheduleAt s.mem (s.gpr .x0)) (dir up) (blocksAt s.mem (s.gpr .x1) (s.gpr .x2).toNat)
  pub := PublicRegs [.x0, .x1, .x2, .x3]

theorem ecb_blocks (K : Schedule) (up : Bool) (m m' : Mem) (D : Addr) (n : Nat)
    (h : ∀ b < n, blockAt m' (wAt D b) = blockOut K up (blockAt m (wAt D b))) :
    blocksAt m' D n = ecb K (dir up) (blocksAt m D n) := by
  simp only [blocksAt, Spec.Blowfish.ecb, List.map_map]
  apply List.map_congr_left
  intro b hb
  rw [Function.comp_apply, h b (List.mem_range.mp hb)]
  cases up <;> rfl

def satState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x3000 | .x3 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 4168⟩]
  wr := [⟨0x3000, 0⟩, ⟨0x4000, 256⟩]

theorem publicRegs_four (s₁ s₂ : State) :
    PublicRegs [.x0, .x1, .x2, .x3] s₁ s₂ ↔
      s₁.sp = s₂.sp ∧ s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧
        s₁.gpr .x2 = s₂.gpr .x2 ∧ s₁.gpr .x3 = s₂.gpr .x3 := by
  simp [PublicRegs]

theorem ecb_ok (up : Bool) (s : State) (hs : (ecbC up).pre s) :
    ∃ t s', Exec isa (ecb up) s t s' ∧ abiPreserved s s' ∧ (ecbC up).post s s' := by
  obtain ⟨hrd, hwr, keyData, keyBuf, dataBuf, fit⟩ := hs
  obtain ⟨t, s', he, ⟨hb, hv⟩, hg⟩ := WP.gprs (c := ecb up) (ecb_correct up ⟨hrd, hwr, keyData, keyBuf,
    dataBuf, fit⟩) (rs := preserved) (by cases up <;> lit_decide) (by cases up <;> rfl)
  refine ⟨t, s', he, ⟨hg, VG.AArch64.Exec.sp he, fun r hr => by rw [hv r hr]⟩,
    ecb_blocks _ _ _ _ _ _ hb⟩

theorem encrypt_verified : Verified target encrypt (Proof.Blowfish.ecbEncryptScratchContract abi 0) := by
  refine Verified.of_correct (k := ecbC true) (ecb_ok true) (encrypt_constantTime _) ?_
  sig_implies [Proof.Blowfish.ecbEncryptScratchContract, Proof.Blowfish.ecbScratchContract,
    Proof.Blowfish.ecbScratchSig, Spec.Blowfish.ecbPost, abi, argRegs, ecbC, dir, publicRegs_four]
    [satState] using satState

theorem decrypt_verified : Verified target decrypt (Proof.Blowfish.ecbDecryptScratchContract abi 0) := by
  refine Verified.of_correct (k := ecbC false) (ecb_ok false) (decrypt_constantTime _) ?_
  sig_implies [Proof.Blowfish.ecbDecryptScratchContract, Proof.Blowfish.ecbScratchContract,
    Proof.Blowfish.ecbScratchSig, Spec.Blowfish.ecbPost, abi, argRegs, ecbC, dir, publicRegs_four]
    [satState] using satState

end VG.Proof.Blowfish.AArch64
