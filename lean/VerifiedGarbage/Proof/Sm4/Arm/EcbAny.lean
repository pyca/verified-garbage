module

public import VerifiedGarbage.Proof.Sm4.Arm.Ecb
public import VerifiedGarbage.Proof.Sm4.Scratch
public import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Proof.Framework.Scratch
public import VerifiedGarbage.Proof.Sm4.Scratch
public import VerifiedGarbage.Impl.StackScratch.Arm
import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
import VerifiedGarbage.Proof.Framework.Arm.StackScratchWipe
import VerifiedGarbage.Proof.MdStream.Arm.Common
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Sm4.Arm.Lit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Sm4.Arm.LayersLit
meta import VerifiedGarbage.Proof.Sm4.Arm.Ecb
meta import VerifiedGarbage.Proof.Sm4.Scratch
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Scratch
meta import VerifiedGarbage.Impl.StackScratch.Arm
meta import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
meta import VerifiedGarbage.Proof.Framework.Arm.StackScratchWipe
meta import VerifiedGarbage.Proof.MdStream.Arm.Common
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Sm4.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Sm4.Arm.LayersLit
public import VerifiedGarbage.Proof.Sm4.Contract

/-!
# SM4 ECB on ARMv7 in either direction: `vg_sm4_ecb`

`ecbAny`, with its scratch buffer's address as a stack argument
(`ecbAnyArm`): the address to `r12`, then `ecbWith .r12 keysAny`
(`ecbWith_wp`, `keysAny_wp`).
-/

@[expose] public section

namespace VG.Proof.Sm4.Arm

open VG VG.Arm VG.Impl.Sm4.Arm
open VG.Proof.Sm4 (specDirArm)

/-- `vg_sm4_ecb` with its scratch buffer as a stack argument, as `sig_pre`
evaluates its contract. -/
def ecbAnyArm : Contract Arm.isa where
  pre s :=
    let sched : Region := ⟨State.addr (s.gpr .r0), 128⟩
    let data : Region := ⟨State.addr (s.gpr .r1), (s.gpr .r2).toNat * 16⟩
    let scr : Region := ⟨State.addr (stackArg s 0), 1456⟩
    let arg : Region := ⟨stackArgAddr s 0, 4⟩
    s.sp.toNat + 4 ≤ 2 ^ 32 ∧ s.rd = [sched, arg] ∧ s.wr = [data, scr] ∧ sched.Disjoint data ∧
      sched.Disjoint scr ∧ data.Disjoint scr ∧ data.Disjoint arg ∧ scr.Disjoint arg ∧
      (s.gpr .r0).toNat + 128 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + (s.gpr .r2).toNat * 16 ≤ 2 ^ 32 ∧
      (stackArg s 0).toNat + 1456 ≤ 2 ^ 32
  post s s' :=
    Spec.Sm4.blocksAt s'.mem (State.addr (s.gpr .r1)) (s.gpr .r2).toNat =
      Spec.Sm4.ecb (Spec.Sm4.scheduleAt s.mem (State.addr (s.gpr .r0))) (specDirArm (dirOf (s.gpr .r3)))
        (Spec.Sm4.blocksAt s.mem (State.addr (s.gpr .r1)) (s.gpr .r2).toNat)
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
      s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0

theorem ecbAny_wp {s₀ : State} (hp : ecbAnyArm.pre s₀) :
    WP isa ecbAny s₀ fun s' => (∀ i < 9, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧ ecbAnyArm.post s₀ s' := by
  obtain ⟨hspF, hrd, hwr, dKD, dKS, dDS, -, -, fitK, fitD, fitS⟩ := hp
  unfold ecbAny
  refine WP.seq (VG.Proof.MdStream.Arm.wp_ldrSp (a := stackArgAddr s₀ 0) (by decide) rfl
    ⟨_, List.mem_append_left _ (by rw [hrd]; simp), Region.contains_self _ _⟩ fun s₁ u₁ => WP.block_nil ?_)
  have h12 : s₁.gpr .r12 = stackArg s₀ 0 := u₁.gpr
  have g₁ : ∀ r, r ≠ .r12 → s₁.gpr r = s₀.gpr r := u₁.other
  have e0 : s₁.gpr .r0 = s₀.gpr .r0 := g₁ _ (by decide)
  have e1 : s₁.gpr .r1 = s₀.gpr .r1 := g₁ _ (by decide)
  have e2 : s₁.gpr .r2 = s₀.gpr .r2 := g₁ _ (by decide)
  have e3 : s₁.gpr .r3 = s₀.gpr .r3 := g₁ _ (by decide)
  have hslots : 4 * slots = 1456 := by rw [slots_eq]
  have hD : (⟨State.addr (s₁.gpr .r1), 16 * (s₁.gpr .r2).toNat⟩ : Region) =
      ⟨State.addr (s₀.gpr .r1), (s₀.gpr .r2).toNat * 16⟩ := by rw [e1, e2, Nat.mul_comm]
  have hS : (⟨State.addr (s₁.gpr .r12), 4 * slots⟩ : Region) = ⟨State.addr (stackArg s₀ 0), 1456⟩ := by
    rw [h12, hslots]
  refine WP.mono (ecbWith_wp .r12 keysAny (dirOf (s₀.gpr .r3)) (s₀ := s₁) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
    fun s' ⟨hg, hpost⟩ => ⟨fun i hi => ?_, ?_⟩
  · rw [u₁.rd, e0, hrd]; simp
  · refine ⟨by rw [hS, u₁.wr, hwr]; simp, by rw [h12, slots_eq]; omega⟩
  · rw [hD, u₁.wr, hwr]; simp
  · rw [hS, e0]; exact dKS
  · rw [hD, hS]; exact dDS
  · rw [e0]; exact fitK
  · rw [e1, e2]; omega
  · intro s₂ hs₂ r12₂ g₂
    exact keysAny_wp hs₂ r12₂ ((g₂ .r3 (by decide) (by decide)).trans e3)
  · rw [hg i hi]; exact g₁ _ (by revert i; decide)
  · show Spec.Sm4.blocksAt s'.mem (State.addr (s₀.gpr .r1)) (s₀.gpr .r2).toNat = _
    rw [← e1, ← e2, hpost, e0, u₁.mem]

/-- The initial taint: the registers of the arguments and the stack argument
are public; the stack argument is the base of the scratch buffer, the
second writable region. -/
def ecbAnyTaint : VG.Arm.Taint.T :=
  { regs := .ofList [.r0, .r1, .r2, .r3], flags := false, lens := [0, 4 * slots], argLen := 4,
    argBases := [(0, 1)] }

theorem ecbAnyTaint_wf {s : State} (h : ecbAnyArm.pre s) : VG.Arm.Taint.Wf ecbAnyTaint s := by
  obtain ⟨hspF, -, hwr, -, -, dDS, dDA, dSA, -, fitD, fitS⟩ := h
  have hslots : 4 * slots = 1456 := by rw [slots_eq]
  have harg : (⟨stackArgAddr s 0, 4⟩ : Region) = ⟨State.addr s.sp, 4⟩ := by
    simp [stackArgAddr]
  refine ⟨fun _ => ⟨by simp [hwr, ecbAnyTaint, hslots], ?_, ?_⟩, fun p hp => by simp [ecbAnyTaint] at hp,
    fun _ => ⟨hspF, fun r hr => ?_⟩, fun p hp => ?_⟩
  · simp only [hwr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
      List.Pairwise.nil]
    exact ⟨dDS, fun _ h => h.elim, trivial⟩
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [addr_toNat] <;> omega
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false] at hr
    show (⟨State.addr s.sp, 4⟩ : Region).Disjoint r
    rw [← harg]
    rcases hr with rfl | rfl
    · exact dDA.symm
    · exact dSA.symm
  · simp only [ecbAnyTaint, List.mem_singleton] at hp; subst hp
    refine ⟨by decide, ?_⟩
    simp [VG.Arm.Taint.region, hwr, stackArg, stackArgAddr]

theorem ecbAnyTaint_agree (s₁ s₂ : State) (h₁ : ecbAnyArm.pre s₁) (h₂ : ecbAnyArm.pre s₂)
    (hp : ecbAnyArm.pub s₁ s₂) : VG.Arm.Taint.Agree ecbAnyTaint s₁ s₂ := by
  obtain ⟨psp, p0, p1, p2, p3, pa⟩ := hp
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, ecbAnyTaint_wf h₁, ecbAnyTaint_wf h₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => psp, ?_⟩
  · simp only [ecbAnyTaint, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption
  · rw [h₁.2.2.1, h₂.2.2.1, p1, p2, pa]
  · exact fun k hk => argMem_of (j := 1) psp (by simpa using h₁.1)
      (fun i hi => by obtain rfl : i = 0 := by omega
                      exact pa) k hk

theorem ecbAny_ct : ConstantTime isa ecbAnyArm.pre ecbAnyArm.pub ecbAny :=
  VG.Taint.constantTime (A := VG.Arm.taint) ecbAnyTaint ecbAnyTaint_agree (by taint_decide)

theorem ecbAny_correct (s : State) (hs : ecbAnyArm.pre s) :
    ∃ t s', Exec isa ecbAny s t s' ∧ abiPreserved s s' ∧ ecbAnyArm.post s s' := by
  obtain ⟨t, s', he, h₁, h₂⟩ := ecbAny_wp hs
  refine ⟨t, s', he, ⟨fun r hr => ?_, VG.Arm.Exec.sp he⟩, h₂⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h₁ 0 (by omega)
  · exact h₁ 1 (by omega)
  · exact h₁ 2 (by omega)
  · exact h₁ 3 (by omega)
  · exact h₁ 4 (by omega)
  · exact h₁ 5 (by omega)
  · exact h₁ 6 (by omega)
  · exact h₁ 7 (by omega)
  · exact h₁ 8 (by omega)

/-- A state satisfying the precondition with the scratch buffer as an
argument: the schedule at `0x1000`, one block at `0x3000`, the buffer at 0
(the stack argument, which reads 0). -/
def ecbAnySat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x3000 | .r2 => 1 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 128⟩, ⟨0x8000, 4⟩]
  wr := [⟨0x3000, 16⟩, ⟨0, 1456⟩]

theorem ecbAny_verified :
    Verified Arm.target ecbAny (Sig.scratchContract Arm.abi Proof.Sm4.ecbDirSig "scratch" .u64 182
      (Proof.Sm4.ecbDirPre Arm.abi.ptrBits) (Proof.Sm4.ecbDirPost Arm.abi.ptrBits) true 0) :=
  Verified.of_correct ecbAny_correct ecbAny_ct
    { pre := by
        sig_implies_pre [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Proof.Sm4.ecbDirSig,
          Spec.Sm4.ecbSig, Proof.Sm4.ecbDirPre, Proof.Sm4.ecbDirPost, ecbAnyArm, Arm.abi, Arm.argRegs,
          Arm.reduceClassify, Arm.Loc.val, State.addr]
      post := by
        sig_implies_post [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Proof.Sm4.ecbDirSig,
          Spec.Sm4.ecbSig, Proof.Sm4.ecbDirPre, Proof.Sm4.ecbDirPost, ecbAnyArm, dirOf_eq, Arm.abi, Arm.argRegs,
          Arm.reduceClassify, Arm.Loc.val, State.addr]
      pub := by
        sig_implies_pub [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Proof.Sm4.ecbDirSig,
          Spec.Sm4.ecbSig, Proof.Sm4.ecbDirPre, Proof.Sm4.ecbDirPost, ecbAnyArm, Arm.abi, Arm.argRegs,
          Arm.reduceClassify, Arm.Loc.val, State.addr]
      sat := by
        refine ⟨ecbAnySat, ?_⟩
        sig_pre [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Proof.Sm4.ecbDirSig,
          Spec.Sm4.ecbSig, Proof.Sm4.ecbDirPre, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
          State.addr]
        have hst : stackArg ecbAnySat 0 = 0 := by
          simp [stackArg, stackArgAddr, ecbAnySat, Mem.readW, Mem.read]
        have hsa : stackArgAddr ecbAnySat 0 = 32768 := by decide
        sig_and_intros
        all_goals (try simp only [hst, hsa])
        all_goals first | rfl | decide | (refine Region.disjoint_of_sep ?_; decide) | exact Nat.zero_le 1 }

/-- A state satisfying `vg_sm4_ecb`'s precondition: the schedule at
`0x1000`, one block at `0x3000`, encryption. -/
def ecbDirFrameSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x3000 | .r2 => 1 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x3000, 16⟩]

theorem ecbDirFrameSat_pre : ∃ s, (Proof.Sm4.ecbDirContract Arm.abi 1472).pre s := by
  refine ⟨ecbDirFrameSat, ?_⟩
  sig_pre [Proof.Sm4.ecbDirContract, Proof.Sm4.ecbDirSig, Spec.Sm4.ecbSig, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val, State.addr]
  sig_and_intros
  all_goals first | rfl | decide | (refine Region.disjoint_of_sep ?_; decide)

/-- `vg_sm4_ecb`: ECB in the direction `decrypt` selects, with its working
space on the stack. -/
theorem ecbAny_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratchWiped 1472 0 364 ecbAny)
      (Proof.Sm4.ecbDirContract Arm.abi 1472) :=
  Arm.Verified.stackScratchWiped (sig := Proof.Sm4.ecbDirSig) (nm := "scratch") (e := .u64) (n := 182)
    (pre := Proof.Sm4.ecbDirPre Arm.abi.ptrBits) (post := Proof.Sm4.ecbDirPost Arm.abi.ptrBits) (wa := true)
    (stack := 0) (m := 0) (bytes := 1472) ecbAny_verified (by decide) (by decide) (by decide) (by decide)
    (by decide) (Proof.Sm4.ecbDirPre_local _) (Proof.Sm4.ecbDirPost_local _) (Proof.Sm4.ecbDirPostOut_local _)
    ecbDirFrameSat_pre

end VG.Proof.Sm4.Arm
