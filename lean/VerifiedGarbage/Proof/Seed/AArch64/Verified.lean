module

public import VerifiedGarbage.Proof.Seed.AArch64.Ecb
public import VerifiedGarbage.Proof.Seed.AArch64.ConstantTime
public import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
public import VerifiedGarbage.Spec.Seed.Contract
public import VerifiedGarbage.Proof.Seed.Contract
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Seed.AArch64.Lit

/-! # The ECB functions meet their contracts, with the scratch buffer as an argument -/

@[expose] public section

namespace VG.Proof.Seed.AArch64

open VG VG.AArch64

/-- With `n` bytes of working space at `x3` (976 for ECB, 1088 for the blocks functions). -/
def contract (d : Spec.Seed.Direction) (n : Nat := 976) : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .x0, 128⟩
    let data : Region := ⟨s.gpr .x1, 16 * (s.gpr .x2).toNat⟩
    let buf : Region := ⟨s.gpr .x3, n⟩
    s.rd = [key] ∧ s.wr = [data, buf] ∧ key.Disjoint data ∧ key.Disjoint buf ∧
      data.Disjoint buf ∧ (s.gpr .x1).toNat + 16 * (s.gpr .x2).toNat ≤ 2 ^ 64
  post s s' :=
    Spec.Seed.blocksAt s'.mem (s.gpr .x1) (s.gpr .x2).toNat =
      Spec.Seed.ecb (Spec.Seed.scheduleAt s.mem (s.gpr .x0)) d
        (Spec.Seed.blocksAt s.mem (s.gpr .x1) (s.gpr .x2).toNat)
  pub := PublicRegs [.x0, .x1, .x2, .x3]

theorem ecbPre_of {s : State} {d : Spec.Seed.Direction} {n : Nat} (hn : 976 ≤ n)
    (hs : (contract d n).pre s) : EcbPre s := by
  obtain ⟨rd, wr, kd, kb, db, fit⟩ := hs
  have sub : Region.Sub ⟨s.gpr .x3, 8 * Impl.Seed.AArch64.scratchSlots⟩ ⟨s.gpr .x3, n⟩ := by
    have h := Offset.sub_base (s.gpr .x3) (d := 0) (n := 8 * Impl.Seed.AArch64.scratchSlots) (k := n)
      (by unfold Impl.Seed.AArch64.scratchSlots; omega)
    simpa using h
  exact { scratch := ⟨n, by unfold Impl.Seed.AArch64.scratchSlots; omega, by
            rw [wr]; exact List.mem_cons_of_mem _ List.mem_cons_self⟩
          dataIn := by rw [wr]; exact List.mem_cons_self
          keyIn := by rw [rd]; exact List.mem_cons_self
          keyData := kd
          keyBuf := kb.sub_right sub
          dataBuf := db.sub_right sub
          fit := by omega }

def satState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x3 => 0x3000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x2000, 0⟩, ⟨0x3000, 976⟩]

/-- `satState` with the 1088 bytes of `vg_seed_*_blocks`'s working space. -/
def satStateBlocks : State := { satState with wr := [⟨0x2000, 0⟩, ⟨0x3000, 1088⟩] }

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

theorem ecb_wp (d : Spec.Seed.Direction) {n : Nat} (hn : 976 ≤ n) (s : State) (hs : (contract d n).pre s) :
    WP isa (Impl.Seed.AArch64.ecb d) s fun s' =>
      (∀ p ∈ Impl.Seed.AArch64.savedRegs, s'.gpr p.1 = s.gpr p.1) ∧ (contract d n).post s s' :=
  WP.mono (ecb_ok d (ecbPre_of hn hs)) fun _ hp => ⟨hp.saved, ecb_blocks _ _ _ _ _ _ hp.done⟩

theorem encrypt_correct {n : Nat} (hn : 976 ≤ n) (s : State) (hs : (contract .encrypt n).pre s) :
    ∃ t s', Exec isa Impl.Seed.AArch64.encrypt s t s' ∧ abiPreserved s s' ∧
      (contract .encrypt n).post s s' := by
  obtain ⟨t, s', he, ⟨hsv, hp⟩, h30⟩ := WP.gprs (c := Impl.Seed.AArch64.encrypt) (ecb_wp .encrypt hn s hs)
    (rs := [.x30]) (by lit_decide) (by lit_decide)
  exact ⟨t, s', he, abi_of he hsv (h30 _ (by simp)) (by lit_decide), hp⟩

theorem decrypt_correct {n : Nat} (hn : 976 ≤ n) (s : State) (hs : (contract .decrypt n).pre s) :
    ∃ t s', Exec isa Impl.Seed.AArch64.decrypt s t s' ∧ abiPreserved s s' ∧
      (contract .decrypt n).post s s' := by
  obtain ⟨t, s', he, ⟨hsv, hp⟩, h30⟩ := WP.gprs (c := Impl.Seed.AArch64.decrypt) (ecb_wp .decrypt hn s hs)
    (rs := [.x30]) (by lit_decide) (by lit_decide)
  exact ⟨t, s', he, abi_of he hsv (h30 _ (by simp)) (by lit_decide), hp⟩

theorem publicRegs_four (s₁ s₂ : State) : PublicRegs [.x0, .x1, .x2, .x3] s₁ s₂ ↔
    s₁.sp = s₂.sp ∧ s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧
      s₁.gpr .x2 = s₂.gpr .x2 ∧ s₁.gpr .x3 = s₂.gpr .x3 := by
  simp [PublicRegs]

/-- ECB against `vg_seed_encrypt_blocks`'s contract: its working space is 136 words, of which
the code uses the first 122. -/
theorem encrypt_blocks_verified : Verified target Impl.Seed.AArch64.encrypt
    (Proof.Seed.blocksContract abi .encrypt) := by
  refine Verified.of_correct (encrypt_correct (n := 1088) (by decide)) (encrypt_constantTime _) ?_
  sig_implies [Proof.Seed.blocksContract, Proof.Seed.blocksSig, Spec.Seed.ecbPost, abi, argRegs,
    contract, publicRegs_four] [satStateBlocks] using satStateBlocks

theorem decrypt_blocks_verified : Verified target Impl.Seed.AArch64.decrypt
    (Proof.Seed.blocksContract abi .decrypt) := by
  refine Verified.of_correct (decrypt_correct (n := 1088) (by decide)) (decrypt_constantTime _) ?_
  sig_implies [Proof.Seed.blocksContract, Proof.Seed.blocksSig, Spec.Seed.ecbPost, abi, argRegs,
    contract, publicRegs_four] [satStateBlocks] using satStateBlocks

end VG.Proof.Seed.AArch64
