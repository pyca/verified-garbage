module

import VerifiedGarbage.Proof.Rc2.RISCV64.Key
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Spec.Rc2.Contract
public import VerifiedGarbage.Proof.Rc2.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Rc2.RISCV64.Lit
meta import VerifiedGarbage.Proof.Rc2.RISCV64.Key
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Spec.Rc2.Contract
meta import VerifiedGarbage.Proof.Rc2.Contract
meta import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Rc2.RISCV64.Lit
public import VerifiedGarbage.Impl.Rc2.RISCV64.ExpandKey
public import VerifiedGarbage.Proof.Rc2.RISCV64.Run
public import VerifiedGarbage.Proof.Rc2.PiLit

/-! # Verified RC2 key expansion on RISC-V -/

@[expose] public section

namespace VG.Proof.Rc2.RISCV64

open VG VG.RISCV64 VG.Impl.Rc2.RISCV64

/-- The key expansion contract as the code sees it. -/
def keyC : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .a0, (s.gpr .a1).toNat⟩
    let sch : Region := ⟨s.gpr .a3, 128⟩
    let buf : Region := ⟨s.gpr .a4, 512⟩
    s.rd = [key] ∧ s.wr = [sch, buf] ∧ (s.gpr .a4).toNat % 8 = 0 ∧ key.Disjoint sch ∧ key.Disjoint buf ∧
      sch.Disjoint buf ∧ Spec.Rc2.validKey (s.gpr .a1).toNat (s.gpr .a2).toNat
  post s s' := Spec.Rc2.scheduleAt s'.mem (s.gpr .a3) =
    Spec.Rc2.expandKey (Spec.Rc2.bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat) (s.gpr .a2).toNat
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.sp = s₂.sp

/-- The registers key expansion writes: no preserved register, nor `ra`. -/
def keyWrites : List Reg := [.a5, .a6, .a7, .t0, .t1, .t2, .t3, .t4]

theorem expandKey_ok (hw : writesOnly keyWrites expandKey = true) (hn : callFree expandKey = true)
    (s : State) (hs : keyC.pre s) :
    ∃ t s', Exec isa expandKey s t s' ∧ abiPreserved s s' ∧ keyC.post s s' := by
  obtain ⟨rd, wr, al, kS, kW, SW, valid⟩ := hs
  obtain ⟨t, s', he, hp, hk⟩ := WP.keep keyWrites (expandKey_wp ⟨valid, rd, wr, al, kS, kW, SW⟩) hw hn
  exact ⟨t, s', he, abiPreserved_of_keep he hk (by decide) (by decide), hp⟩

theorem key_agree : ∀ s₁ s₂, keyC.pre s₁ → keyC.pre s₂ → keyC.pub s₁ s₂ →
    taint.Agree (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4]) s₁ s₂ := by
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
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4]) key_agree (by taint_decide)

def keySat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 16 | .a2 => 128 | .a3 => 0x2000 | .a4 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 128⟩, ⟨0x4000, 512⟩]

theorem key_verified : Verified RISCV64.target expandKey (Proof.Rc2.expandKeyContract RISCV64.abi) := by
  refine Verified.of_correct (k := keyC) (expandKey_ok (by lit_decide) (by lit_decide)) expandKey_ct ?_
  sig_implies [Proof.Rc2.expandKeyContract, Proof.Rc2.expandKeySig, Spec.Rc2.validKey, RISCV64.abi,
    RISCV64.argRegs, keyC]
    [keySat] using keySat

end VG.Proof.Rc2.RISCV64
