module
public import VerifiedGarbage.Impl.Seed.AArch64.Modes
public import VerifiedGarbage.Proof.Seed.Contract
public import VerifiedGarbage.Proof.Seed.Scratch
public import VerifiedGarbage.Impl.StackScratch.AArch64
public import VerifiedGarbage.Proof.Framework.AArch64.Depth
public import VerifiedGarbage.Proof.Framework.AArch64.Taint
public import VerifiedGarbage.TCB.AArch64.Target

import VerifiedGarbage.Proof.Seed.AArch64.Verified
import VerifiedGarbage.Proof.Seed.ModeBytes
import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
import VerifiedGarbage.Proof.Framework.AArch64.StackScratch
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Impl.Seed.AArch64.Modes
meta import VerifiedGarbage.Proof.Seed.Scratch
meta import VerifiedGarbage.Impl.StackScratch.AArch64
meta import VerifiedGarbage.Proof.Framework.AArch64.Depth
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.TCB.AArch64.Target
meta import VerifiedGarbage.Proof.Seed.AArch64.Verified
meta import VerifiedGarbage.Proof.Seed.ModeBytes
meta import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.AArch64.StackScratch
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.Seed.AArch64.Lit
meta import VerifiedGarbage.Proof.Seed.AArch64.Lit

/-!
# SEED ECB on AArch64: calls of the blocks functions

`vg_seed_ecb_encrypt` and `vg_seed_ecb_decrypt` allocate their working
space on the stack (1088 bytes, as `vg_seed_{en,de}crypt_blocks` need) and
call the blocks function of their direction with it (`ecbCall`), in a frame
saving `x30`. `ecbCall_verified` proves that code from the blocks
functions' contracts, with the working space as an argument and 16 bytes
of stack; `ecbCall_framed` adds the frame of the working space.
-/

@[expose] public section

namespace VG.Proof.Seed.AArch64

open VG VG.AArch64 VG.Impl.Seed.AArch64

/-- The ECB contracts with `scratch: *mut [u64; 136]` and `stack = 16`, as
`sig_pre` evaluates them. -/
def ecbCallAArch64 (d : Spec.Seed.Direction) : Contract AArch64.isa where
  pre s :=
    let sched : Region := ⟨s.gpr .x0, 128⟩
    let data : Region := ⟨s.gpr .x1, (s.gpr .x2).toNat * 16⟩
    let scr : Region := ⟨s.gpr .x3, 1088⟩
    let stk : Region := ⟨s.sp - BitVec.ofNat 64 16, 16⟩
    16 ≤ s.sp.toNat ∧ s.rd = [sched] ∧ s.wr = [data, scr] ∧ sched.Disjoint data ∧ sched.Disjoint scr ∧
      data.Disjoint scr ∧ stk.Disjoint sched ∧ stk.Disjoint data ∧ stk.Disjoint scr ∧
      (s.gpr .x0).toNat + 128 ≤ 2 ^ 64 ∧ (s.gpr .x1).toNat + (s.gpr .x2).toNat * 16 ≤ 2 ^ 64 ∧
      (s.gpr .x3).toNat + 1088 ≤ 2 ^ 64
  post s s' :=
    Spec.Seed.blocksAt s'.mem (s.gpr .x1) (s.gpr .x2).toNat =
      Spec.Seed.ecb (Spec.Seed.scheduleAt s.mem (s.gpr .x0)) d
        (Spec.Seed.blocksAt s.mem (s.gpr .x1) (s.gpr .x2).toNat)
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
      s₁.gpr .x3 = s₂.gpr .x3

theorem fdepth_of_noFrames {c : Prog isa} (h : c.noFrames = true) : c.aarch64Depth = 0 := by
  induction c <;> simp_all [Code.noFrames, Code.aarch64Depth]

theorem frame_push (s₀ : State) :
    Frame [⟨s₀.sp - 16, 16⟩] s₀.mem (s₀.mem.write (s₀.sp - 16) 8 (s₀.gpr .x30)) :=
  (Frame.refl _ _).write (List.mem_singleton_self _) _ (by simp [Region.Contains])

/-- A call, in a frame saving `x30`, of code meeting the blocks contract of
`d`. -/
theorem call_correct {d : Spec.Seed.Direction} {name : String} {c : Prog isa}
    (hv : Verified AArch64.target c (Proof.Seed.blocksContract AArch64.abi d)) (hn : c.noFrames = true)
    (s₀ : State) (hs : (ecbCallAArch64 d).pre s₀) :
    ∃ t s', Exec isa (.frame (.push .x30) (.call name c) (.pop .x30)) s₀ t s' ∧ abiPreserved s₀ s' ∧
      (ecbCallAArch64 d).post s₀ s' := by
  obtain ⟨hsp, hrd, hwr, dKD, dKS, dDS, sK, sD, sS, fitK, fitD, fitS⟩ := hs
  refine (WP.frameReg (r := .x30) (s₀ := s₀) hsp (fun R hR => ?_) ?_
    (by rw [fdepth_of_noFrames (show (Code.call name c : Prog isa).noFrames = true from hn)]; decide)).elim
    fun t ⟨s', he, hq⟩ => ⟨t, s', he, hq⟩
  · rw [hwr] at hR
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl
    · exact sD
    · exact sS
  refine WP.callV (k := Proof.Seed.blocksContract AArch64.abi d) hv.1 (rd := s₀.rd) (wr := s₀.wr) ?_
    ?_ ?_ ?_ hn
  rotate_left
  · exact fun _ _ h => h
  · exact fun _ _ h => h
  rotate_left
  · sig_pre [Proof.Seed.blocksContract, Proof.Seed.blocksSig, AArch64.abi, AArch64.argRegs]
    exact ⟨hrd, hwr, dKD, dKS, dDS, fitK, fitD, fitS⟩
  · intro s' rd' wr' sp' hf hg _ hvv hpost
    sig_reduce [Proof.Seed.blocksContract, Proof.Seed.blocksSig, Spec.Seed.ecbPost, AArch64.abi, AArch64.argRegs] at hpost
    rw [BitVec.setWidth_eq] at hpost
    have hfr := frame_push s₀
    have hsch := Proof.Seed.scheduleAt_frame hfr (p := s₀.gpr .x0) fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact sK.symm
    have hblk := Proof.Seed.blocksAt_frame hfr (p := s₀.gpr .x1) (n := (s₀.gpr .x2).toNat) (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact sD.symm) (by omega)
    refine ⟨⟨fun r hr => ?_, rfl, fun r hr => hvv r hr⟩, ?_⟩
    · show (s'.write .x .x30 (s₀.gpr .x30)).gpr r = s₀.gpr r
      by_cases h : r = .x30
      · subst h; rw [RegUpd.gpr_write_self, BitVec.setWidth_eq]
      · rw [RegUpd.gpr_write_of_ne _ _ _ h, hg r hr h]
    · show Spec.Seed.blocksAt s'.mem (s₀.gpr .x1) (s₀.gpr .x2).toNat = _
      rw [hpost, hsch, hblk]

theorem ecbCall_correct (d : Spec.Seed.Direction) (s₀ : State) (hs : (ecbCallAArch64 d).pre s₀) :
    ∃ t s', Exec isa (ecbCall d) s₀ t s' ∧ abiPreserved s₀ s' ∧ (ecbCallAArch64 d).post s₀ s' := by
  cases d
  · exact call_correct encrypt_blocks_verified (by lit_decide) s₀ hs
  · exact call_correct decrypt_blocks_verified (by lit_decide) s₀ hs

theorem ecbCallTaint_agree (d : Spec.Seed.Direction) (s₁ s₂ : State) (_ : (ecbCallAArch64 d).pre s₁)
    (_ : (ecbCallAArch64 d).pre s₂) (hp : (ecbCallAArch64 d).pub s₁ s₂) :
    VG.AArch64.Taint.Agree (Taint.ofRegs [.x0, .x1, .x2, .x3]) s₁ s₂ := by
  obtain ⟨hsp, h1, h2, h3, h4⟩ := hp
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem ecbCall_ct (d : Spec.Seed.Direction) :
    ConstantTime isa (ecbCallAArch64 d).pre (ecbCallAArch64 d).pub (ecbCall d) := by
  cases d
  · exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3]) (ecbCallTaint_agree .encrypt)
      (by taint_decide)
  · exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3]) (ecbCallTaint_agree .decrypt)
      (by taint_decide)

/-- A state satisfying the precondition with the working space as an
argument: the schedule at `0x1000`, one block at `0x3000`, the working space
at `0x4000`. -/
def ecbCallSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x3000 | .x2 => 1 | .x3 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x3000, 16⟩, ⟨0x4000, 1088⟩]

theorem ecbCall_verified (d : Spec.Seed.Direction) :
    Verified AArch64.target (ecbCall d) (Proof.Seed.ecbScratchContract AArch64.abi d 136 16) :=
  Verified.of_correct (ecbCall_correct d) (ecbCall_ct d) (by
    sig_implies [Proof.Seed.ecbScratchContract, Proof.Seed.ecbScratchSig, Spec.Seed.ecbPost, ecbCallAArch64,
      AArch64.abi, AArch64.argRegs] [ecbCallSat] using ecbCallSat)

/-- `vg_seed_ecb_encrypt` and `vg_seed_ecb_decrypt`: the call in a frame
allocating the working space, 1104 bytes of stack in all. -/
theorem ecbCall_framed (d : Spec.Seed.Direction) :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 1088 .x3 136 (ecbCall d))
      (Spec.Seed.ecbContract AArch64.abi d 1104) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.Seed.ecbSig) (nm := "scratch") (e := .u64)
    (n := 136) (post := Spec.Seed.ecbPost d AArch64.abi.ptrBits) (wa := true) (stack := 16)
    (bytes := 1088) (ecbCall_verified d) (by decide) (by decide) (by decide) (Proof.Seed.ecbPostOut_local _ d)
    (AArch64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

end VG.Proof.Seed.AArch64
