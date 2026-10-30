module

public import VerifiedGarbage.Proof.Rc2.PPC64LE.Stream.Init
public import VerifiedGarbage.Proof.Rc2.PPC64LE.Stream.Update
public import VerifiedGarbage.Proof.Rc2.Scratch
public import VerifiedGarbage.Impl.StackScratch.PPC64LE
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchWipe
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Rc2.PPC64LE.Stream.Lit
meta import VerifiedGarbage.Proof.Rc2.PPC64LE.Stream.Init
meta import VerifiedGarbage.Proof.Rc2.PPC64LE.Stream.Update
meta import VerifiedGarbage.Proof.Rc2.Scratch
meta import VerifiedGarbage.Impl.StackScratch.PPC64LE
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch
meta import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Rc2.PPC64LE.Stream.Lit

/-!
# Verified streaming RC2-CBC on PPC64LE

`init` and the updates meet the shared contracts with their working space as
an argument (`Proof.Rc2.cbcInitScratchContract`, `cbcUpdateScratchContract`),
and, in a frame that allocates the working space and zeroes it after the code
(`Verified.stackScratchWiped`), the contracts of `Spec/Rc2/Contract.lean`. The
code uses no other stack.
-/

@[expose] public section

namespace VG.Proof.Rc2.PPC64LE.Stream

open VG VG.PPC64LE VG.Impl.Rc2.PPC64LE.Stream

/-- `init`'s contract as the code sees it. -/
noncomputable def initC : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .r3, (s.gpr .r4).toNat⟩
    let iv : Region := ⟨s.gpr .r6, (s.gpr .r7).toNat⟩
    let ctx : Region := ⟨s.gpr .r8, 144⟩
    let scr : Region := ⟨s.gpr .r9, 576⟩
    s.rd = [key, iv] ∧ s.wr = [ctx, scr] ∧ key.Disjoint ctx ∧ key.Disjoint scr ∧ iv.Disjoint ctx ∧
      iv.Disjoint scr ∧ ctx.Disjoint scr
  post s s' := initPost s s'
  pub s₁ s₂ := s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
    s₁.sp = s₂.sp

/-- The updates' contract as the code sees it. -/
noncomputable def updateC (d : Spec.Rc2.Direction) : Contract isa where
  pre s :=
    let ctx : Region := ⟨s.gpr .r3, 144⟩
    let data : Region := ⟨s.gpr .r5, (s.gpr .r6).toNat⟩
    let out : Region := ⟨s.gpr .r7, (s.gpr .r8).toNat⟩
    let scr : Region := ⟨s.gpr .r9, 576⟩
    s.rd = [data] ∧ s.wr = [ctx, out, scr] ∧ ctx.Disjoint data ∧ ctx.Disjoint out ∧ ctx.Disjoint scr ∧
      data.Disjoint out ∧ data.Disjoint scr ∧ out.Disjoint scr ∧
      (s.gpr .r5).toNat + (s.gpr .r6).toNat ≤ 2 ^ 64 ∧ (s.gpr .r7).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r4).toNat < 8 ∧ (s.gpr .r8).toNat = ((s.gpr .r4).toNat + (s.gpr .r6).toNat) / 8 * 8
  post s s' := updatePost d s s'
  pub s₁ s₂ := s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
    s₁.sp = s₂.sp

theorem init_ok (s : State) (hs : initC.pre s) :
    ∃ t s', Exec isa init s t s' ∧ abiPreserved s s' ∧ initC.post s s' := by
  obtain ⟨rd, wr, kC, kW, vC, vW, CW⟩ := hs
  obtain ⟨t, s', he, hp, hl, hq⟩ := init_wp s ⟨rd, wr, kC, kW, vC, vW, CW⟩
  exact ⟨t, s', he, ⟨hp, Exec.sp he, hl⟩, hq⟩

theorem update_ok (d : Spec.Rc2.Direction) (s : State) (hs : (updateC d).pre s) :
    ∃ t s', Exec isa (update d) s t s' ∧ abiPreserved s s' ∧ (updateC d).post s s' := by
  obtain ⟨rd, wr, CD, CO, CW, DO, DW, OW, fD, fO, hp, ho⟩ := hs
  obtain ⟨t, s', he, hpr, hl, hq⟩ := update_wp d s ⟨rd, wr, CD, CO, CW, DO, DW, OW, fD, fO, hp, ho⟩
  exact ⟨t, s', he, ⟨hpr, Exec.sp he, hl⟩, hq⟩

theorem agree {pub : State → State → Prop}
    (h : ∀ s₁ s₂, pub s₁ s₂ → s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
      s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
      s₁.sp = s₂.sp) {pre : State → Prop} :
    ∀ s₁ s₂, pre s₁ → pre s₂ → pub s₁ s₂ →
      taint.Agree (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7, .r8, .r9]) s₁ s₂ := by
  intro s₁ s₂ _ _ hp
  obtain ⟨p3, p4, p5, p6, p7, p8, p9, psp⟩ := h s₁ s₂ hp
  refine ⟨psp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem init_ct : ConstantTime isa initC.pre initC.pub init :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7, .r8, .r9])
    (agree fun _ _ h => h) (by taint_decide)

theorem encryptUpdate_ct : ConstantTime isa (updateC .encrypt).pre (updateC .encrypt).pub encryptUpdate :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7, .r8, .r9])
    (agree fun _ _ h => h) (by taint_decide)

theorem decryptUpdate_ct : ConstantTime isa (updateC .decrypt).pre (updateC .decrypt).pub decryptUpdate :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7, .r8, .r9])
    (agree fun _ _ h => h) (by taint_decide)

noncomputable def initSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r6 => 0x2000 | .r8 => 0x3000 | .r9 => 0x4000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 0⟩, ⟨0x2000, 0⟩]
  wr := [⟨0x3000, 144⟩, ⟨0x4000, 576⟩]

noncomputable def updateSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r5 => 0x2000 | .r7 => 0x3000 | .r9 => 0x4000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, 144⟩, ⟨0x3000, 0⟩, ⟨0x4000, 576⟩]

theorem init_verified : Verified target init (Proof.Rc2.cbcInitScratchContract abi) := by
  refine Verified.of_correct (k := initC) init_ok init_ct ?_
  sig_implies [Proof.Rc2.cbcInitScratchContract, Proof.Rc2.cbcInitScratchSig, Spec.Rc2.cbcInitPost, abi, argRegs,
    initC, initPost] [initSat] using initSat

theorem encryptUpdate_verified : Verified target encryptUpdate (Proof.Rc2.cbcEncryptUpdateScratchContract abi) := by
  refine Verified.of_correct (k := updateC .encrypt) (update_ok .encrypt) encryptUpdate_ct ?_
  sig_implies [Proof.Rc2.cbcEncryptUpdateScratchContract, Proof.Rc2.cbcUpdateScratchContract,
    Proof.Rc2.cbcUpdateScratchSig, Spec.Rc2.cbcUpdatePre, Spec.Rc2.cbcUpdatePost, abi, argRegs, updateC, updatePost]
    [updateSat] using updateSat

theorem decryptUpdate_verified : Verified target decryptUpdate (Proof.Rc2.cbcDecryptUpdateScratchContract abi) := by
  refine Verified.of_correct (k := updateC .decrypt) (update_ok .decrypt) decryptUpdate_ct ?_
  sig_implies [Proof.Rc2.cbcDecryptUpdateScratchContract, Proof.Rc2.cbcUpdateScratchContract,
    Proof.Rc2.cbcUpdateScratchSig, Spec.Rc2.cbcUpdatePre, Spec.Rc2.cbcUpdatePost, abi, argRegs, updateC, updatePost]
    [updateSat] using updateSat

end VG.Proof.Rc2.PPC64LE.Stream
