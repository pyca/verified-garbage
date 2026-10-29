module

public import VerifiedGarbage.Proof.Rc2.RISCV64.Stream.Init
public import VerifiedGarbage.Proof.Rc2.RISCV64.Stream.Update
public import VerifiedGarbage.Proof.Rc2.Scratch
public import VerifiedGarbage.Impl.StackScratch.RISCV64
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Framework.RISCV64.StackScratch
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Rc2.RISCV64.Stream.Lit
meta import VerifiedGarbage.Proof.Rc2.RISCV64.Stream.Init
meta import VerifiedGarbage.Proof.Rc2.RISCV64.Stream.Update
meta import VerifiedGarbage.Proof.Rc2.Scratch
meta import VerifiedGarbage.Impl.StackScratch.RISCV64
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.Proof.Framework.RISCV64.StackScratch
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Rc2.RISCV64.Stream.Lit

/-!
# Verified streaming RC2-CBC on RISC-V

`init` and the updates meet the shared contracts with their working space as
an argument (`Proof.Rc2.cbcInitScratchContract`, `cbcUpdateScratchContract`),
and, in a frame that allocates the working space and zeroes it after the code
(`Verified.stackScratchWiped`), the contracts of `Spec/Rc2/Contract.lean`. The
code uses no other stack.
-/

@[expose] public section

namespace VG.Proof.Rc2.RISCV64.Stream

open VG VG.RISCV64 VG.Impl.Rc2.RISCV64.Stream

/-- `init`'s contract as the code sees it. -/
def initC : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .a0, (s.gpr .a1).toNat⟩
    let iv : Region := ⟨s.gpr .a3, (s.gpr .a4).toNat⟩
    let ctx : Region := ⟨s.gpr .a5, 144⟩
    let scr : Region := ⟨s.gpr .a6, 576⟩
    s.rd = [key, iv] ∧ s.wr = [ctx, scr] ∧ (s.gpr .a6).toNat % 8 = 0 ∧ key.Disjoint ctx ∧ key.Disjoint scr ∧
      iv.Disjoint ctx ∧ iv.Disjoint scr ∧ ctx.Disjoint scr
  post s s' := initPost s s'
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.gpr .a5 = s₂.gpr .a5 ∧ s₁.gpr .a6 = s₂.gpr .a6 ∧
    s₁.sp = s₂.sp

/-- The updates' contract as the code sees it. -/
def updateC (d : Spec.Rc2.Direction) : Contract isa where
  pre s :=
    let ctx : Region := ⟨s.gpr .a0, 144⟩
    let data : Region := ⟨s.gpr .a2, (s.gpr .a3).toNat⟩
    let out : Region := ⟨s.gpr .a4, (s.gpr .a5).toNat⟩
    let scr : Region := ⟨s.gpr .a6, 576⟩
    s.rd = [data] ∧ s.wr = [ctx, out, scr] ∧ ctx.Disjoint data ∧ ctx.Disjoint out ∧ ctx.Disjoint scr ∧
      data.Disjoint out ∧ data.Disjoint scr ∧ out.Disjoint scr ∧
      (s.gpr .a2).toNat + (s.gpr .a3).toNat ≤ 2 ^ 64 ∧ (s.gpr .a4).toNat + (s.gpr .a5).toNat ≤ 2 ^ 64 ∧
      (s.gpr .a6).toNat % 8 = 0 ∧ (s.gpr .a6).toNat + 576 ≤ 2 ^ 64 ∧
      (s.gpr .a1).toNat < 8 ∧ (s.gpr .a5).toNat = ((s.gpr .a1).toNat + (s.gpr .a3).toNat) / 8 * 8
  post s s' := updatePost d s s'
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.gpr .a5 = s₂.gpr .a5 ∧ s₁.gpr .a6 = s₂.gpr .a6 ∧
    s₁.sp = s₂.sp

theorem init_ok (s : State) (hs : initC.pre s) :
    ∃ t s', Exec isa init s t s' ∧ abiPreserved s s' ∧ initC.post s s' := by
  obtain ⟨rd, wr, al, kC, kW, vC, vW, CW⟩ := hs
  obtain ⟨t, s', he, ⟨hp, hl, hq⟩, _, _, hsp⟩ := WP.rdwr (init_wp s ⟨rd, wr, al, kC, kW, vC, vW, CW⟩)
  exact ⟨t, s', he, ⟨hp, hsp, hl⟩, hq⟩

theorem update_ok (d : Spec.Rc2.Direction) (s : State) (hs : (updateC d).pre s) :
    ∃ t s', Exec isa (update d) s t s' ∧ abiPreserved s s' ∧ (updateC d).post s s' := by
  obtain ⟨rd, wr, CD, CO, CW, DO, DW, OW, fD, fO, al, fW, hp, ho⟩ := hs
  obtain ⟨t, s', he, ⟨hpr, hl, hq⟩, _, _, hsp⟩ :=
    WP.rdwr (update_wp d s ⟨rd, wr, CD, CO, CW, DO, DW, OW, fD, fO, al, fW, hp, ho⟩)
  exact ⟨t, s', he, ⟨hpr, hsp, hl⟩, hq⟩

theorem agree {pub : State → State → Prop}
    (h : ∀ s₁ s₂, pub s₁ s₂ → s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
      s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.gpr .a5 = s₂.gpr .a5 ∧ s₁.gpr .a6 = s₂.gpr .a6 ∧
      s₁.sp = s₂.sp) {pre : State → Prop} :
    ∀ s₁ s₂, pre s₁ → pre s₂ → pub s₁ s₂ →
      taint.Agree (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4, .a5, .a6]) s₁ s₂ := by
  intro s₁ s₂ _ _ hp
  obtain ⟨p3, p4, p5, p6, p7, p8, p9, psp⟩ := h s₁ s₂ hp
  refine ⟨psp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem init_ct : ConstantTime isa initC.pre initC.pub init :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4, .a5, .a6])
    (agree fun _ _ h => h) (by taint_decide)

theorem encryptUpdate_ct : ConstantTime isa (updateC .encrypt).pre (updateC .encrypt).pub encryptUpdate :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4, .a5, .a6])
    (agree fun _ _ h => h) (by taint_decide)

theorem decryptUpdate_ct : ConstantTime isa (updateC .decrypt).pre (updateC .decrypt).pub decryptUpdate :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4, .a5, .a6])
    (agree fun _ _ h => h) (by taint_decide)

def initSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a3 => 0x2000 | .a5 => 0x3000 | .a6 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 0⟩, ⟨0x2000, 0⟩]
  wr := [⟨0x3000, 144⟩, ⟨0x4000, 576⟩]

def updateSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a2 => 0x2000 | .a4 => 0x3000 | .a6 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, 144⟩, ⟨0x3000, 0⟩, ⟨0x4000, 576⟩]

theorem init_verified : Verified RISCV64.target init (Proof.Rc2.cbcInitScratchContract RISCV64.abi) := by
  refine Verified.of_correct (k := initC) init_ok init_ct ?_
  sig_implies [Proof.Rc2.cbcInitScratchContract, Proof.Rc2.cbcInitScratchSig, Spec.Rc2.cbcInitPost, RISCV64.abi,
    RISCV64.argRegs,
    initC, initPost] [initSat] using initSat

theorem encryptUpdate_verified : Verified RISCV64.target encryptUpdate
    (Proof.Rc2.cbcEncryptUpdateScratchContract RISCV64.abi) := by
  refine Verified.of_correct (k := updateC .encrypt) (update_ok .encrypt) encryptUpdate_ct ?_
  sig_implies [Proof.Rc2.cbcEncryptUpdateScratchContract, Proof.Rc2.cbcUpdateScratchContract,
    Proof.Rc2.cbcUpdateScratchSig, Spec.Rc2.cbcUpdatePre, Spec.Rc2.cbcUpdatePost, RISCV64.abi, RISCV64.argRegs, updateC,
    updatePost]
    [updateSat] using updateSat

theorem decryptUpdate_verified : Verified RISCV64.target decryptUpdate
    (Proof.Rc2.cbcDecryptUpdateScratchContract RISCV64.abi) := by
  refine Verified.of_correct (k := updateC .decrypt) (update_ok .decrypt) decryptUpdate_ct ?_
  sig_implies [Proof.Rc2.cbcDecryptUpdateScratchContract, Proof.Rc2.cbcUpdateScratchContract,
    Proof.Rc2.cbcUpdateScratchSig, Spec.Rc2.cbcUpdatePre, Spec.Rc2.cbcUpdatePost, RISCV64.abi, RISCV64.argRegs, updateC,
    updatePost]
    [updateSat] using updateSat

end VG.Proof.Rc2.RISCV64.Stream
