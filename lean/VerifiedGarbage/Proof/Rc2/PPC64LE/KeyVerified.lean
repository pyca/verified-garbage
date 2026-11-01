module

import VerifiedGarbage.Proof.Rc2.PPC64LE.Key
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Spec.Rc2.Contract
public import VerifiedGarbage.Proof.Rc2.Contract
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Rc2.PPC64LE.Key
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Spec.Rc2.Contract
meta import VerifiedGarbage.Proof.Rc2.Contract
meta import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Impl.Rc2.PPC64LE.ExpandKey
public import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
public import VerifiedGarbage.Proof.Rc2.PPC64LE.Run
public import VerifiedGarbage.Proof.Rc2.PiLit

/-! # Verified RC2 key expansion on PPC64LE -/

@[expose] public section

namespace VG.Proof.Rc2.PPC64LE

open VG VG.PPC64LE VG.Impl.Rc2.PPC64LE

/-- The key expansion contract as the code sees it. -/
def keyC : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .r3, (s.gpr .r4).toNat⟩
    let sch : Region := ⟨s.gpr .r6, 128⟩
    let buf : Region := ⟨s.gpr .r7, 512⟩
    s.rd = [key] ∧ s.wr = [sch, buf] ∧ key.Disjoint sch ∧ key.Disjoint buf ∧ sch.Disjoint buf ∧
      Spec.Rc2.validKey (s.gpr .r4).toNat (s.gpr .r5).toNat
  post s s' := Spec.Rc2.scheduleAt s'.mem (s.gpr .r6) =
    Spec.Rc2.expandKey (Spec.Rc2.bytesAt s.mem (s.gpr .r3) (s.gpr .r4).toNat) (s.gpr .r5).toNat
  pub s₁ s₂ := s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.sp = s₂.sp

/-- The registers key expansion writes. -/
def keyWrites : List Reg := [.r0, .r8, .r9, .r10, .r11, .r12, .r14, .r15]

theorem expandKey_ok (s : State) (hs : keyC.pre s) :
    ∃ t s', Exec isa expandKey s t s' ∧ abiPreserved s s' ∧ keyC.post s s' := by
  obtain ⟨rd, wr, kS, kW, SW, valid⟩ := hs
  have hn : expandKey.noCalls = true := by decide +kernel
  obtain ⟨t, s', he, hp, hk⟩ := WP.keep keyWrites (expandKey_wp ⟨valid, rd, wr, kS, kW, SW⟩)
    (by decide +kernel) hn
  refine ⟨t, s', he, ⟨fun r hr => ?_, Exec.sp he, Exec.lr he hn (by rw [← Code.allInstrs_eq]; decide +kernel)⟩,
    hp.sched⟩
  by_cases h : r ∈ keySaved.map Prod.fst
  · exact hp.saved r h
  · refine hk.gpr fun hm => h ?_
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [keyWrites, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl <;> simp [keySaved] at hm ⊢

theorem key_agree : ∀ s₁ s₂, keyC.pre s₁ → keyC.pre s₂ → keyC.pub s₁ s₂ →
    taint.Agree (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7]) s₁ s₂ := by
  intro s₁ s₂ _ _ h
  refine ⟨h.2.2.2.2.2, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2.1
  · exact h.2.2.2.2.1

theorem expandKey_ct : ConstantTime isa keyC.pre keyC.pub expandKey :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7]) key_agree (by taint_decide)

def keySat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 16 | .r5 => 128 | .r6 => 0x2000 | .r7 => 0x4000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 128⟩, ⟨0x4000, 512⟩]

theorem key_verified : Verified target expandKey (Proof.Rc2.expandKeyContract abi) := by
  refine Verified.of_correct (k := keyC) expandKey_ok expandKey_ct ?_
  sig_implies [Proof.Rc2.expandKeyContract, Proof.Rc2.expandKeySig, Spec.Rc2.validKey, abi, argRegs, keyC]
    [keySat] using keySat

end VG.Proof.Rc2.PPC64LE
