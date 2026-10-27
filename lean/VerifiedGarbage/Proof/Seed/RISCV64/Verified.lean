module

public import VerifiedGarbage.Proof.Seed.RISCV64.Ecb
public import VerifiedGarbage.Proof.Seed.Scratch
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Spec.Seed.Contract
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Seed.RISCV64.Lit
meta import VerifiedGarbage.Proof.Seed.RISCV64.Ecb
meta import VerifiedGarbage.Proof.Seed.Scratch
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.Spec.Seed.Contract
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Seed.RISCV64.Lit
public import VerifiedGarbage.Spec.Seed
public import VerifiedGarbage.TCB.Artifact

/-!
# The ECB functions meet their contracts, with the scratch buffer as an argument

`ecb_verified`: `ecb d` is correct (`ecb_ok`) and constant time, by the
taint analysis with the pointers, `n` and the stack pointer public, against
`Proof.Seed.ecbScratchContract` with the working space's 129 words
(`Frame.lean` runs them in a frame).
-/

@[expose] public section

namespace VG.Proof.Seed.RISCV64

open VG VG.RISCV64

/-- ECB with its working space at `a3`. -/
def contract (d : Spec.Seed.Direction) : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .a0, 128⟩
    let data : Region := ⟨s.gpr .a1, 16 * (s.gpr .a2).toNat⟩
    let buf : Region := ⟨s.gpr .a3, 8 * Impl.Seed.RISCV64.scratchSlots⟩
    s.rd = [key] ∧ s.wr = [data, buf] ∧ key.Disjoint data ∧ key.Disjoint buf ∧
      data.Disjoint buf ∧ (s.gpr .a1).toNat + 16 * (s.gpr .a2).toNat ≤ 2 ^ 64 ∧
      (s.gpr .a3).toNat % 8 = 0
  post s s' :=
    Spec.Seed.blocksAt s'.mem (s.gpr .a1) (s.gpr .a2).toNat =
      Spec.Seed.ecb (Spec.Seed.scheduleAt s.mem (s.gpr .a0)) d
        (Spec.Seed.blocksAt s.mem (s.gpr .a1) (s.gpr .a2).toNat)
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧
    s₁.gpr .a2 = s₂.gpr .a2 ∧ s₁.gpr .a3 = s₂.gpr .a3

theorem ecbPre_of {s : State} {d : Spec.Seed.Direction} (hs : (contract d).pre s) : EcbPre s := by
  obtain ⟨rd, wr, kd, kb, db, fit, al⟩ := hs
  exact { scrAl := al
          scratch := ⟨_, Nat.le_refl _, by rw [wr]; exact List.mem_cons_of_mem _ List.mem_cons_self⟩
          dataIn := by rw [wr]; exact List.mem_cons_self
          keyIn := by rw [rd]; exact List.mem_cons_self
          keyData := kd
          keyBuf := kb
          dataBuf := db
          fit := by omega }

theorem ecb_correct (d : Spec.Seed.Direction) (s : State) (hs : (contract d).pre s) :
    ∃ t s', Exec isa (Impl.Seed.RISCV64.ecb d) s t s' ∧ abiPreserved s s' ∧ (contract d).post s s' := by
  obtain ⟨t, s', he, hp⟩ := ecb_ok d (ecbPre_of hs)
  exact ⟨t, s', he, ⟨hp.saved, Exec.sp he, hp.ra⟩, ecb_blocks _ _ _ _ _ _ hp.done⟩

theorem ecb_ct (d : Spec.Seed.Direction) :
    ConstantTime isa (contract d).pre (contract d).pub (Impl.Seed.RISCV64.ecb d) := by
  have hag : ∀ s₁ s₂, (contract d).pre s₁ → (contract d).pre s₂ → (contract d).pub s₁ s₂ →
      taint.Agree (Taint.ofRegs [.a0, .a1, .a2, .a3]) s₁ s₂ := by
    rintro s₁ s₂ - - ⟨hsp, h0, h1, h2, h3⟩
    refine ⟨hsp, fun r hr => ?_⟩
    simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    exacts [h0, h1, h2, h3]
  cases d
  · exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3]) hag (by taint_decide)
  · exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3]) hag (by taint_decide)

def satState : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a3 => 0x3000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x2000, 0⟩, ⟨0x3000, 8 * 129⟩]

theorem ecb_verified (d : Spec.Seed.Direction) : Verified target (Impl.Seed.RISCV64.ecb d)
    (Proof.Seed.ecbScratchContract abi d 129) := by
  refine Verified.of_correct (ecb_correct d) (ecb_ct d) ?_
  cases d <;>
  sig_implies [Proof.Seed.ecbScratchContract, Proof.Seed.ecbScratchSig, Spec.Seed.ecbPost, abi, argRegs,
    contract, Impl.Seed.RISCV64.scratchSlots] [satState] using satState

end VG.Proof.Seed.RISCV64
