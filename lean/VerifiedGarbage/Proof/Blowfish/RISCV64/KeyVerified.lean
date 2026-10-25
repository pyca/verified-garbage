module

import VerifiedGarbage.Proof.Blowfish.RISCV64.KeyMain
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Spec.Blowfish.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Framework.RISCV64.Keep
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Blowfish.RISCV64.Lit
meta import VerifiedGarbage.Proof.Blowfish.RISCV64.KeyMain
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Spec.Blowfish.Contract
meta import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.Proof.Framework.RISCV64.Keep
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Blowfish.RISCV64.Lit
public import VerifiedGarbage.Impl.Blowfish.RISCV64
public import VerifiedGarbage.Proof.Blowfish.RISCV64.Run

/-!
# Blowfish key expansion on RISC-V meets its contract

The proof is written against `keyC`, which states the frame of 4176 bytes
below the stack pointer, and moved to `expandKeyContract` with
`stack := 4176`. The code writes only temporaries and argument registers.
-/

@[expose] public section

namespace VG.Proof.Blowfish.RISCV64

open VG VG.RISCV64 VG.Impl.Blowfish.RISCV64 VG.Spec.Blowfish VG.Proof.Blowfish

/-- The key expansion contract as the code sees it. -/
def keyC : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .a0, (s.gpr .a1).toNat⟩
    let sch : Region := ⟨s.gpr .a2, 4168⟩
    let stack : Region := ⟨s.sp - 4176, 4176⟩
    s.rd = [key] ∧ s.wr = [sch] ∧ key.Disjoint sch ∧ validKey (s.gpr .a1).toNat ∧
      s.sp.toNat % 16 = 0 ∧ 4176 ≤ s.sp.toNat ∧ stack.Disjoint key ∧ stack.Disjoint sch
  post s s' := scheduleAt s'.mem (s.gpr .a2) = expandKey (bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat)
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.sp = s₂.sp

/-- The registers key expansion writes: no preserved register, nor `ra`. -/
def keyRegs : List Reg := [.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7, .t0, .t1, .t2, .t3, .t4, .t5, .t6]

theorem expandKey_ok (hw : writesOnly keyRegs Impl.Blowfish.RISCV64.expandKey = true)
    (hn : callFree Impl.Blowfish.RISCV64.expandKey = true) (s : State) (hs : keyC.pre s) :
    ∃ t s', Exec isa Impl.Blowfish.RISCV64.expandKey s t s' ∧ abiPreserved s s' ∧ keyC.post s s' := by
  obtain ⟨rd, wr, kS, valid, al, sp, sk, ss⟩ := hs
  obtain ⟨t, s', he, hp, hk⟩ := WP.keep keyRegs (expandKey_wp ⟨valid, rd, wr, kS, al, sp, sk, ss⟩) hw hn
  exact ⟨t, s', he, abiPreserved_of_keep he hk (by decide) (by decide), hp.1⟩

theorem key_agree : ∀ s₁ s₂, keyC.pre s₁ → keyC.pre s₂ → keyC.pub s₁ s₂ →
    taint.Agree (Taint.ofRegs [.a0, .a1, .a2]) s₁ s₂ := by
  intro s₁ s₂ _ _ h
  refine ⟨h.2.2.2, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1

theorem expandKey_ct : ConstantTime isa keyC.pre keyC.pub Impl.Blowfish.RISCV64.expandKey :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2]) key_agree (by taint_decide)

def keySat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 16 | .a2 => 0x3000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x3000, 4168⟩]

theorem expandKey_verified :
    Verified RISCV64.target Impl.Blowfish.RISCV64.expandKey (Spec.Blowfish.expandKeyContract RISCV64.abi 4176) := by
  refine Verified.of_correct (k := keyC) (expandKey_ok (by lit_decide) (by lit_decide)) expandKey_ct ?_
  contract_implies [Spec.Blowfish.expandKeyContract, Spec.Blowfish.expandKeySig, Spec.Blowfish.expandKeyPre,
    Spec.Blowfish.expandKeyPost, Spec.Blowfish.validKey, RISCV64.abi, RISCV64.argRegs, keyC] [keySat]
    using keySat

end VG.Proof.Blowfish.RISCV64
