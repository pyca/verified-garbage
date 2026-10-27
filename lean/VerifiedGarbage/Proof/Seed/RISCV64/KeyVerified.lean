module

import VerifiedGarbage.Proof.Seed.RISCV64.Key
public import VerifiedGarbage.Proof.Seed.Scratch
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.TCB.Artifact
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Seed.RISCV64.Lit
meta import VerifiedGarbage.Proof.Seed.RISCV64.Key
meta import VerifiedGarbage.Proof.Seed.Scratch
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.TCB.Artifact
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Seed.RISCV64.Lit
public import VerifiedGarbage.Impl.Seed.RISCV64.ExpandKey
public import VerifiedGarbage.Proof.Framework.Bitslice.Atoms
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill
public import VerifiedGarbage.Proof.Framework.RISCV64.Straight
public import VerifiedGarbage.Proof.Seed.Sbox
public import VerifiedGarbage.TCB.Sig

/-!
# Key expansion meets its contract, with the scratch buffer as an argument

`expandKey_verified`: `expandKey` is correct (`expandKey_ok`) and constant
time, by the taint analysis with the pointers and the stack pointer public,
against `Proof.Seed.expandKeyScratchContract` with the working space's 129
words (`Frame.lean` runs it in a frame).
-/

@[expose] public section

namespace VG.Proof.Seed.RISCV64

open VG VG.RISCV64

/-- Key expansion with its working space at `a2`. -/
def keyContract : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .a0, 16⟩
    let sched : Region := ⟨s.gpr .a1, 128⟩
    let buf : Region := ⟨s.gpr .a2, 8 * Impl.Seed.RISCV64.scratchSlots⟩
    s.rd = [key] ∧ s.wr = [sched, buf] ∧ key.Disjoint sched ∧ key.Disjoint buf ∧ sched.Disjoint buf ∧
      (s.gpr .a2).toNat % 8 = 0
  post s s' :=
    Spec.Seed.scheduleAt s'.mem (s.gpr .a1) = Spec.Seed.expandKey (Spec.Seed.blockAt s.mem (s.gpr .a0))
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2

theorem expandKey_correct (s : State) (hs : keyContract.pre s) :
    ∃ t s', Exec isa Impl.Seed.RISCV64.expandKey s t s' ∧ abiPreserved s s' ∧ keyContract.post s s' := by
  obtain ⟨rd, wr, ks, kb, sb, al⟩ := hs
  obtain ⟨t, s', he, hp⟩ := expandKey_ok (s := s)
    { scrAl := al
      scratch := by rw [wr]; exact List.mem_cons_of_mem _ List.mem_cons_self
      schedIn := by rw [wr]; exact List.mem_cons_self
      keyIn := by rw [rd]; exact List.mem_cons_self
      keySched := ks
      keyBuf := kb
      schedBuf := sb }
  exact ⟨t, s', he, ⟨hp.saved, Exec.sp he, hp.ra⟩, hp.sched⟩

theorem expandKey_ct :
    ConstantTime isa keyContract.pre keyContract.pub Impl.Seed.RISCV64.expandKey := by
  have hag : ∀ s₁ s₂, keyContract.pre s₁ → keyContract.pre s₂ → keyContract.pub s₁ s₂ →
      taint.Agree (Taint.ofRegs [.a0, .a1, .a2]) s₁ s₂ := by
    rintro s₁ s₂ - - ⟨hsp, h0, h1, h2⟩
    refine ⟨hsp, fun r hr => ?_⟩
    simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [h0, h1, h2]
  exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2]) hag (by taint_decide)

def keySatState : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a2 => 0x3000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 128⟩, ⟨0x3000, 8 * 129⟩]

theorem expandKey_verified : Verified target Impl.Seed.RISCV64.expandKey
    (Proof.Seed.expandKeyScratchContract abi 129) := by
  refine Verified.of_correct expandKey_correct expandKey_ct ?_
  sig_implies [Proof.Seed.expandKeyScratchContract, Proof.Seed.expandKeyScratchSig, Proof.Seed.expandKeyPost,
    abi, argRegs, keyContract, Impl.Seed.RISCV64.scratchSlots] [keySatState] using keySatState

end VG.Proof.Seed.RISCV64
