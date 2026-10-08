import VerifiedGarbage.Proof.Seed.AArch64.Ecb
import VerifiedGarbage.Proof.Seed.AArch64.ConstantTime
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Seed.Scratch

/-! # The ECB functions meet their contracts, with the scratch buffer as an argument -/

namespace VG.Proof.Seed.AArch64

open VG VG.AArch64

def contract (d : Spec.Seed.Direction) : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .x0, 128⟩
    let data : Region := ⟨s.gpr .x1, 16 * (s.gpr .x2).toNat⟩
    let buf : Region := ⟨s.gpr .x3, 976⟩
    s.rd = [key] ∧ s.wr = [data, buf] ∧ key.Disjoint data ∧ key.Disjoint buf ∧
      data.Disjoint buf ∧ (s.gpr .x1).toNat + 16 * (s.gpr .x2).toNat ≤ 2 ^ 64
  post s s' :=
    Spec.Seed.blocksAt s'.mem (s.gpr .x1) (s.gpr .x2).toNat =
      Spec.Seed.ecb (Spec.Seed.scheduleAt s.mem (s.gpr .x0)) d
        (Spec.Seed.blocksAt s.mem (s.gpr .x1) (s.gpr .x2).toNat)
  pub := PublicRegs [.x0, .x1, .x2, .x3]

theorem ecbPre_of {s : State} {d : Spec.Seed.Direction} (hs : (contract d).pre s) : EcbPre s := by
  obtain ⟨rd, wr, kd, kb, db, fit⟩ := hs
  exact { scratch := by rw [wr]; exact List.mem_cons_of_mem _ List.mem_cons_self
          dataIn := by rw [wr]; exact List.mem_cons_self
          keyIn := by rw [rd]; exact List.mem_cons_self
          keyData := kd
          keyBuf := kb
          dataBuf := db
          fit := by omega }

def satState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x3 => 0x3000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x2000, 0⟩, ⟨0x3000, 976⟩]

/-- The callee-saved registers, from those the code saves and `x30`, which it never writes. -/
theorem abi_of {c : Prog isa} {s s' : State} {t : List Leak} (he : Exec isa c s t s')
    (hs : ∀ p ∈ Impl.Seed.AArch64.savedRegs, s'.gpr p.1 = s.gpr p.1) (h30 : s'.gpr .x30 = s.gpr .x30)
    (hv : c.allInstrs keepsV = true) : abiPreserved s s' := by
  refine ⟨fun r hr => ?_, Exec.sp he, Exec.preservedV he hv⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hs (.x19, 112) (by decide)
  · exact hs (.x20, 113) (by decide)
  · exact hs (.x21, 114) (by decide)
  · exact hs (.x22, 115) (by decide)
  · exact hs (.x23, 116) (by decide)
  · exact hs (.x24, 117) (by decide)
  · exact hs (.x25, 118) (by decide)
  · exact hs (.x26, 119) (by decide)
  · exact hs (.x27, 120) (by decide)
  · exact hs (.x28, 121) (by decide)
  · exact h30

theorem ecb_wp (d : Spec.Seed.Direction) (s : State) (hs : (contract d).pre s) :
    WP isa (Impl.Seed.AArch64.ecb d) s fun s' =>
      (∀ p ∈ Impl.Seed.AArch64.savedRegs, s'.gpr p.1 = s.gpr p.1) ∧ (contract d).post s s' :=
  WP.mono (ecb_ok d (ecbPre_of hs)) fun _ hp => ⟨hp.saved, ecb_blocks _ _ _ _ _ _ hp.done⟩

theorem encrypt_correct (s : State) (hs : (contract .encrypt).pre s) :
    ∃ t s', Exec isa Impl.Seed.AArch64.encrypt s t s' ∧ abiPreserved s s' ∧
      (contract .encrypt).post s s' := by
  obtain ⟨t, s', he, ⟨hsv, hp⟩, h30⟩ := WP.gprs (c := Impl.Seed.AArch64.encrypt) (ecb_wp .encrypt s hs)
    (rs := [.x30]) (by lit_decide) (by lit_decide)
  exact ⟨t, s', he, abi_of he hsv (h30 _ (by simp)) (by lit_decide), hp⟩

theorem decrypt_correct (s : State) (hs : (contract .decrypt).pre s) :
    ∃ t s', Exec isa Impl.Seed.AArch64.decrypt s t s' ∧ abiPreserved s s' ∧
      (contract .decrypt).post s s' := by
  obtain ⟨t, s', he, ⟨hsv, hp⟩, h30⟩ := WP.gprs (c := Impl.Seed.AArch64.decrypt) (ecb_wp .decrypt s hs)
    (rs := [.x30]) (by lit_decide) (by lit_decide)
  exact ⟨t, s', he, abi_of he hsv (h30 _ (by simp)) (by lit_decide), hp⟩

theorem publicRegs_four (s₁ s₂ : State) : PublicRegs [.x0, .x1, .x2, .x3] s₁ s₂ ↔
    s₁.sp = s₂.sp ∧ s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧
      s₁.gpr .x2 = s₂.gpr .x2 ∧ s₁.gpr .x3 = s₂.gpr .x3 := by
  simp [PublicRegs]

theorem encrypt_verified : Verified target Impl.Seed.AArch64.encrypt
    (Proof.Seed.ecbScratchContract abi .encrypt 122) := by
  refine Verified.of_correct encrypt_correct (encrypt_constantTime _) ?_
  sig_implies [Proof.Seed.ecbScratchContract, Proof.Seed.ecbScratchSig, Spec.Seed.ecbPost, abi, argRegs,
    contract, publicRegs_four] [satState] using satState

theorem decrypt_verified : Verified target Impl.Seed.AArch64.decrypt
    (Proof.Seed.ecbScratchContract abi .decrypt 122) := by
  refine Verified.of_correct decrypt_correct (decrypt_constantTime _) ?_
  sig_implies [Proof.Seed.ecbScratchContract, Proof.Seed.ecbScratchSig, Spec.Seed.ecbPost, abi, argRegs,
    contract, publicRegs_four] [satState] using satState

end VG.Proof.Seed.AArch64
