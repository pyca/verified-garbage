import VerifiedGarbage.Proof.Seed.AArch64.Key
import VerifiedGarbage.Proof.Seed.AArch64.Verified

/-! # Key expansion meets its contract, with the scratch buffer as an argument -/

namespace VG.Proof.Seed.AArch64

open VG VG.AArch64

def keyContract : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .x0, 16⟩
    let sched : Region := ⟨s.gpr .x1, 128⟩
    let buf : Region := ⟨s.gpr .x2, 976⟩
    s.rd = [key] ∧ s.wr = [sched, buf] ∧ key.Disjoint sched ∧ key.Disjoint buf ∧ sched.Disjoint buf
  post s s' :=
    Spec.Seed.scheduleAt s'.mem (s.gpr .x1) = Spec.Seed.expandKey (Spec.Seed.blockAt s.mem (s.gpr .x0))
  pub := PublicRegs [.x0, .x1, .x2]

def keySatState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 128⟩, ⟨0x3000, 976⟩]

theorem expandKey_wp (s : State) (hs : keyContract.pre s) :
    WP isa Impl.Seed.AArch64.expandKey s fun s' =>
      (∀ p ∈ Impl.Seed.AArch64.savedRegs, s'.gpr p.1 = s.gpr p.1) ∧ keyContract.post s s' := by
  obtain ⟨rd, wr, ks, kb, sb⟩ := hs
  refine WP.mono (expandKey_ok (s := s)
    { scratch := by rw [wr]; exact List.mem_cons_of_mem _ List.mem_cons_self
      schedIn := by rw [wr]; exact List.mem_cons_self
      keyIn := by rw [rd]; exact List.mem_cons_self
      keySched := ks
      keyBuf := kb
      schedBuf := sb }) fun _ hp => ⟨hp.saved, hp.sched⟩

theorem expandKey_correct (s : State) (hs : keyContract.pre s) :
    ∃ t s', Exec isa Impl.Seed.AArch64.expandKey s t s' ∧ abiPreserved s s' ∧ keyContract.post s s' := by
  obtain ⟨t, s', he, ⟨hsv, hp⟩, h30⟩ := WP.gprs (c := Impl.Seed.AArch64.expandKey) (expandKey_wp s hs)
    (rs := [.x30]) (by lit_decide) (by lit_decide)
  exact ⟨t, s', he, abi_of he hsv (h30 _ (by simp)) (by lit_decide), hp⟩

theorem publicRegs_three (s₁ s₂ : State) : PublicRegs [.x0, .x1, .x2] s₁ s₂ ↔
    s₁.sp = s₂.sp ∧ s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 := by
  simp [PublicRegs]

theorem expandKey_verified : Verified target Impl.Seed.AArch64.expandKey
    (Proof.Seed.expandKeyScratchContract abi 122) := by
  refine Verified.of_correct expandKey_correct (expandKey_constantTime _) ?_
  sig_implies [Proof.Seed.expandKeyScratchContract, Proof.Seed.expandKeyScratchSig, Proof.Seed.expandKeyPost,
    abi, argRegs, keyContract, publicRegs_three] [keySatState] using keySatState

end VG.Proof.Seed.AArch64
