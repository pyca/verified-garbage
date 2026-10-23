module
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Impl.Seed.PPC64LE.ExpandKey
public import VerifiedGarbage.Proof.Seed.Scratch
public import VerifiedGarbage.TCB.PPC64LE.Target

import VerifiedGarbage.Proof.Seed.PPC64LE.Key
import VerifiedGarbage.Proof.Seed.PPC64LE.Verified
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Seed.PPC64LE.Lit
import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.Semantics
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Impl.Seed.PPC64LE.ExpandKey
meta import VerifiedGarbage.Proof.Seed.Scratch
meta import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.Proof.Seed.PPC64LE.Key
meta import VerifiedGarbage.Proof.Seed.PPC64LE.Verified
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Seed.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.RegSet

/-! # Key expansion meets its contract, with the scratch buffer as an argument -/

@[expose] public section

namespace VG.Proof.Seed.PPC64LE

open VG VG.PPC64LE

def keyContract : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .r3, 16⟩
    let sched : Region := ⟨s.gpr .r4, 128⟩
    let buf : Region := ⟨s.gpr .r5, 8 * Impl.Seed.PPC64LE.scratchSlots⟩
    s.rd = [key] ∧ s.wr = [sched, buf] ∧ key.Disjoint sched ∧ key.Disjoint buf ∧ sched.Disjoint buf
  post s s' :=
    Spec.Seed.scheduleAt s'.mem (s.gpr .r4) = Spec.Seed.expandKey (Spec.Seed.blockAt s.mem (s.gpr .r3))
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5

def keySatState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 0x3000 | _ => 0
  sp := 0x4000
  lr := 0
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 128⟩, ⟨0x3000, 1040⟩]

theorem expandKey_wp (s : State) (hs : keyContract.pre s) :
    WP isa Impl.Seed.PPC64LE.expandKey s fun s' =>
      (∀ p ∈ Impl.Seed.PPC64LE.savedRegs, s'.gpr p.1 = s.gpr p.1) ∧ keyContract.post s s' := by
  obtain ⟨rd, wr, ks, kb, sb⟩ := hs
  refine WP.mono (expandKey_ok (s := s)
    { scratch := by rw [wr]; exact List.mem_cons_of_mem _ List.mem_cons_self
      schedIn := by rw [wr]; exact List.mem_cons_self
      keyIn := by rw [rd]; exact List.mem_cons_self
      keySched := ks
      keyBuf := kb
      schedBuf := sb }) fun _ hp => ⟨hp.saved, hp.sched⟩

theorem expandKey_correct (s : State) (hs : keyContract.pre s) :
    ∃ t s', Exec isa Impl.Seed.PPC64LE.expandKey s t s' ∧ abiPreserved s s' ∧ keyContract.post s s' := by
  have hn : Impl.Seed.PPC64LE.expandKey.noCalls = true := by lit_decide
  obtain ⟨t, s', he, hp, hk⟩ := WP.keep ecbWrites (expandKey_wp s hs) (by lit_decide) hn
  exact ⟨t, s', he, abi_of he hp.1 (hk.gpr (by decide)) (Exec.lr he hn (by lit_decide)), hp.2⟩

theorem expandKey_constantTime :
    ConstantTime isa keyContract.pre keyContract.pub Impl.Seed.PPC64LE.expandKey := by
  have hag : ∀ s₁ s₂, keyContract.pre s₁ → keyContract.pre s₂ → keyContract.pub s₁ s₂ →
      taint.Agree (Taint.ofRegs [.r3, .r4, .r5]) s₁ s₂ := by
    intro s₁ s₂ _ _ hp
    obtain ⟨hsp, h3, h4, h5⟩ := hp
    refine ⟨hsp, fun r hr => ?_⟩
    simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> with_reducible assumption
  exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5]) hag (by taint_decide)

theorem expandKey_verified : Verified target Impl.Seed.PPC64LE.expandKey
    (Proof.Seed.expandKeyScratchContract abi 130) := by
  refine Verified.of_correct expandKey_correct expandKey_constantTime ?_
  sig_implies [Proof.Seed.expandKeyScratchContract, Proof.Seed.expandKeyScratchSig, Proof.Seed.expandKeyPost,
    abi, argRegs, keyContract, Impl.Seed.PPC64LE.scratchSlots] [keySatState] using keySatState

end VG.Proof.Seed.PPC64LE
