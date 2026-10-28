module
public import VerifiedGarbage.Impl.Seed.PPC64LE.Modes
public import VerifiedGarbage.Proof.Seed.Scratch
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.TCB.PPC64LE.Target

import VerifiedGarbage.Proof.Seed.PPC64LE.Verified
import VerifiedGarbage.Proof.Seed.ModeBytes
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchWipe
import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Seed.PPC64LE.Lit
meta import VerifiedGarbage.Impl.Seed.PPC64LE.Modes
meta import VerifiedGarbage.Proof.Seed.Scratch
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.Proof.Seed.PPC64LE.Verified
meta import VerifiedGarbage.Proof.Seed.ModeBytes
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Call
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Step
meta import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Seed.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Framework.RegSet
public import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# SEED ECB on PPC64LE: calls of the blocks functions

`vg_seed_ecb_encrypt` and `vg_seed_ecb_decrypt` allocate their working
space on the stack (1088 bytes, as `vg_seed_{en,de}crypt_blocks` need) and
call the blocks function of their direction with it (`ecbCall`), the link
register saved in a 48-byte frame. `ecbCall_verified` proves that code from
the blocks functions' code (`ecb_correct`), with the working space as an
argument and 48 bytes of stack; `ecbCall_framed` adds the frame of the
working space.
-/

@[expose] public section

namespace VG.Proof.Seed.PPC64LE

open VG VG.PPC64LE VG.Impl.Seed.PPC64LE

/-- The ECB contracts with `scratch: *mut [u64; 136]` and `stack = 48`, as
`sig_pre` evaluates them. -/
def ecbCallPPC64LE (d : Spec.Seed.Direction) : Contract isa where
  pre s :=
    let sched : Region := ⟨s.gpr .r3, 128⟩
    let data : Region := ⟨s.gpr .r4, (s.gpr .r5).toNat * 16⟩
    let scr : Region := ⟨s.gpr .r6, 1088⟩
    let stk : Region := ⟨s.sp - BitVec.ofNat 64 48, 48⟩
    48 ≤ s.sp.toNat ∧ s.rd = [sched] ∧ s.wr = [data, scr] ∧ sched.Disjoint data ∧ sched.Disjoint scr ∧
      data.Disjoint scr ∧ stk.Disjoint sched ∧ stk.Disjoint data ∧ stk.Disjoint scr ∧
      (s.gpr .r3).toNat + 128 ≤ 2 ^ 64 ∧ (s.gpr .r4).toNat + (s.gpr .r5).toNat * 16 ≤ 2 ^ 64 ∧
      (s.gpr .r6).toNat + 1088 ≤ 2 ^ 64
  post s s' :=
    Spec.Seed.blocksAt s'.mem (s.gpr .r4) (s.gpr .r5).toNat =
      Spec.Seed.ecb (Spec.Seed.scheduleAt s.mem (s.gpr .r3)) d
        (Spec.Seed.blocksAt s.mem (s.gpr .r4) (s.gpr .r5).toNat)
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
      s₁.gpr .r6 = s₂.gpr .r6

theorem fdepth_of_noFrames {c : Prog isa} (h : c.noFrames = true) : c.fdepth = 0 := by
  induction c <;> simp_all [Code.noFrames, Code.fdepth]

theorem pushFrames_of_noFrames {c : Prog isa} (h : c.noFrames = true) : pushFrames c = true := by
  induction c <;> simp_all [Code.noFrames, pushFrames]

/-- The frame's two stores are within its 48 bytes. -/
theorem frame_push (s : State) (v : BitVec 64) :
    Frame [⟨s.sp - BitVec.ofNat 64 48, 48⟩] s.mem
      ((s.mem.write (s.sp - 48) 8 s.sp).write (s.sp - 48 + 32) 8 v) := by
  have e : (48 : BitVec 64) = BitVec.ofNat 64 48 := rfl
  have e32 : (32 : BitVec 64) = BitVec.ofNat 64 32 := rfl
  refine ((Frame.refl _ _).write (List.mem_singleton_self _) _ ?_).write (List.mem_singleton_self _) _ ?_
  · rw [e]; exact contains_prefix (by decide)
  · rw [e, e32]; exact Offset.contains_base _ (by decide) (by decide)

/-- A call, in a frame saving the link register, of ECB's code in the
direction `d`. -/
theorem call_correct (d : Spec.Seed.Direction) (s₀ : State) (hs : (ecbCallPPC64LE d).pre s₀) :
    ∃ t s', Exec isa (ecbCall d) s₀ t s' ∧ abiPreserved s₀ s' ∧ (ecbCallPPC64LE d).post s₀ s' := by
  obtain ⟨hsp, hrd, hwr, dKD, dKS, dDS, sK, sD, sS, fitK, fitD, fitS⟩ := hs
  let s₁ := s₀.write .r0 s₀.lr
  have hw : WP isa (ecbCall d) s₀ fun s' => abiPreserved s₀ s' ∧ (ecbCallPPC64LE d).post s₀ s' := by
    refine WP.seq (WP.cons exec_mflr (WP.block_nil (WP.seq ?_)))
    have hn : (blockCall d).noFrames = true := by cases d <;> lit_decide
    refine WP.frameReg (r := .r0) (s₀ := s₁) hsp (fun R hR => ?_) ?_
      (by rw [fdepth_of_noFrames hn]; decide) (pushFrames_of_noFrames hn)
    · rw [show s₁.wr = s₀.wr from rfl, hwr] at hR
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
      have hsub : Region.Sub ⟨s₀.sp - 48 + 32, 16⟩ ⟨s₀.sp - BitVec.ofNat 64 48, 48⟩ := by
        rw [show (48 : BitVec 64) = BitVec.ofNat 64 48 from rfl,
          show (32 : BitVec 64) = BitVec.ofNat 64 32 from rfl]
        exact Offset.sub_base _ (by decide)
      rcases hR with rfl | rfl
      · exact sD.sub_left hsub
      · exact sS.sub_left hsub
    -- The call.
    let F := framed .r0 s₁
    have g : ∀ r, r ≠ .r0 → r ∉ linkRegs → F.callEntry.gpr r = s₀.gpr r := fun r h0 hl => by
      rw [State.callEntry_gpr _ hl]
      show (s₀.write .r0 s₀.lr).gpr r = s₀.gpr r
      exact RegUpd.gpr_write_of_ne _ _ h0
    have hc : ∀ (c : Prog isa) (name : String),
        (∀ s, (contract d 1088).pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (contract d 1088).post s s') →
        c.noFrames = true →
        WP isa (.call name c) F fun s₂ => WP isa (.block [.mtlr .r0])
          { s₂.write .r0 (s₁.gpr .r0) with sp := s₁.sp }
          fun s' => abiPreserved s₀ s' ∧ (ecbCallPPC64LE d).post s₀ s' := by
      intro c name hv hn'
      refine WP.call (k := contract d 1088) (s := F) hv (rd := s₀.rd) (wr := s₀.wr) ?_
        (fun _ _ h => h) (fun _ _ h => h) (fun s' rd' wr' sp' hf hp _ hpost => ?_) hn'
      · have r3 := g .r3 (by decide) (by decide)
        have r4 := g .r4 (by decide) (by decide)
        have r5 := g .r5 (by decide) (by decide)
        have r6 := g .r6 (by decide) (by decide)
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
          simp only [State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, r3, r4, r5, r6]
        · exact hrd
        · rw [hwr, Nat.mul_comm]
        · rw [Nat.mul_comm]; exact dKD
        · exact dKS
        · rw [Nat.mul_comm]; exact dDS
        · rw [Nat.mul_comm]; exact fitD
      · refine WP.cons exec_mtlr (WP.block_nil ⟨⟨fun r hr => ?_, rfl, ?_⟩, ?_⟩)
        · have h0 : r ≠ .r0 := by revert r hr; decide
          show (s'.write .r0 (s₁.gpr .r0)).gpr r = s₀.gpr r
          rw [RegUpd.gpr_write_of_ne _ _ h0, hp r hr]
          exact RegUpd.gpr_write_of_ne _ _ h0
        · show (s'.write .r0 (s₁.gpr .r0)).gpr .r0 = s₀.lr
          rw [RegUpd.gpr_write_self]; rfl
        · have hm : (s'.withRegions s₀.rd s₀.wr).mem = s'.mem := rfl
          have hm₀ : (F.callEntry.withRegions s₀.rd s₀.wr).mem = F.mem := rfl
          have r3 := g .r3 (by decide) (by decide)
          have r4 := g .r4 (by decide) (by decide)
          have r5 := g .r5 (by decide) (by decide)
          simp only [contract, State.withRegions_gpr, hm, hm₀, r3, r4, r5] at hpost
          show Spec.Seed.blocksAt s'.mem (s₀.gpr .r4) (s₀.gpr .r5).toNat = _
          have hfr := frame_push s₁ (s₁.gpr .r0)
          have hsch := Proof.Seed.scheduleAt_frame hfr (p := s₀.gpr .r3) fun r hr => by
            rw [List.mem_singleton] at hr; subst hr; exact sK.symm
          have hblk := Proof.Seed.blocksAt_frame hfr (p := s₀.gpr .r4) (n := (s₀.gpr .r5).toNat) (fun r hr => by
            rw [List.mem_singleton] at hr; subst hr; exact sD.symm) (by omega)
          rw [hpost, show F.mem = (s₁.mem.write (s₁.sp - 48) 8 s₁.sp).write (s₁.sp - 48 + 32) 8 (s₁.gpr .r0) from rfl,
            hsch, hblk]
          rfl
    cases d
    · exact hc _ _ (ecb_correct .encrypt (by decide)) (by lit_decide)
    · exact hc _ _ (ecb_correct .decrypt (by decide)) (by lit_decide)
  obtain ⟨t, s', he, h⟩ := hw
  exact ⟨t, s', he, h⟩

theorem ecbCallTaint_agree (d : Spec.Seed.Direction) (s₁ s₂ : State) (_ : (ecbCallPPC64LE d).pre s₁)
    (_ : (ecbCallPPC64LE d).pre s₂) (hp : (ecbCallPPC64LE d).pub s₁ s₂) :
    taint.Agree (Taint.ofRegs [.r3, .r4, .r5, .r6]) s₁ s₂ := by
  obtain ⟨hsp, h3, h4, h5, h6⟩ := hp
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem ecbCall_ct (d : Spec.Seed.Direction) :
    ConstantTime isa (ecbCallPPC64LE d).pre (ecbCallPPC64LE d).pub (ecbCall d) := by
  cases d
  · exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6]) (ecbCallTaint_agree .encrypt)
      (by taint_decide)
  · exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6]) (ecbCallTaint_agree .decrypt)
      (by taint_decide)

/-- A state satisfying the precondition with the working space as an
argument: the schedule at `0x1000`, one block at `0x3000`, the working space
at `0x4000`. -/
def ecbCallSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x3000 | .r5 => 1 | .r6 => 0x4000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x3000, 16⟩, ⟨0x4000, 1088⟩]

theorem ecbCall_verified (d : Spec.Seed.Direction) :
    Verified target (ecbCall d) (Proof.Seed.ecbScratchContract abi d 136 48) :=
  Verified.of_correct (call_correct d) (ecbCall_ct d) (by
    sig_implies [Proof.Seed.ecbScratchContract, Proof.Seed.ecbScratchSig, Spec.Seed.ecbPost, ecbCallPPC64LE,
      abi, argRegs] [ecbCallSat] using ecbCallSat)

end VG.Proof.Seed.PPC64LE
