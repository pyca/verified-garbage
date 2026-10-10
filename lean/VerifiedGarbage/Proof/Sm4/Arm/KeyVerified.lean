import VerifiedGarbage.Proof.Sm4.Arm.KeyEk
import VerifiedGarbage.Proof.Sm4.Arm.Verified

/-!
# SM4 key expansion on ARMv7 meets its contracts

`expandKey_verified`: `expandKey` is correct (`expandKey_wp`) and constant
time, by the taint analysis: the pointers are public, and so is the
schedule's pointer the code keeps in a slot of the scratch buffer (stored
through `sb`, the buffer's base, after each extraction). `expandKey_framed`
runs it with its working space on the stack, zeroed on return, as
`ecb_framed` does.
-/

namespace VG.Proof.Sm4.Arm

open VG VG.Arm VG.Impl.Sm4.Arm
open VG.Proof.Sm4 (expandKeyArm)

/-- The initial taint: the pointers are public; `r1` and `r2` point at the
schedule and the scratch buffer, the writable regions. -/
def expandKeyTaint : VG.Arm.Taint.T :=
  { regs := .ofList [.r0, .r1, .r2], flags := false, lens := [128, 4 * slots], bases := [(.r1, 0), (.r2, 1)] }

theorem expandKeyTaint_wf {s : State} (h : expandKeyArm.pre s) : VG.Arm.Taint.Wf expandKeyTaint s := by
  obtain ⟨-, hwr, -, -, dSB, -, fitS, fitB⟩ := h
  refine ⟨fun _ => ⟨by simp [hwr, expandKeyTaint], ?_, ?_⟩, fun p hp => ?_, fun h => by simp [expandKeyTaint] at h,
    fun p hp => by simp [expandKeyTaint] at hp⟩
  · simp only [hwr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
      List.Pairwise.nil]
    exact ⟨dSB, fun _ h => h.elim, trivial⟩
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [addr_toNat] <;> omega
  · simp only [expandKeyTaint, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> simp [VG.Arm.Taint.region, hwr]

theorem expandKeyTaint_agree (s₁ s₂ : State) (h₁ : expandKeyArm.pre s₁) (h₂ : expandKeyArm.pre s₂)
    (hp : expandKeyArm.pub s₁ s₂) : VG.Arm.Taint.Agree expandKeyTaint s₁ s₂ := by
  obtain ⟨p0, p1, p2, -⟩ := hp
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, expandKeyTaint_wf h₁, expandKeyTaint_wf h₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun h => by simp [expandKeyTaint] at h, fun k hk => by simp [expandKeyTaint] at hk⟩
  · simp only [expandKeyTaint, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> with_reducible assumption
  · rw [h₁.2.1, h₂.2.1, p1, p2]

theorem expandKey_ct : ConstantTime isa expandKeyArm.pre expandKeyArm.pub expandKey :=
  VG.Taint.constantTime (A := VG.Arm.taint) expandKeyTaint expandKeyTaint_agree (by taint_decide)

theorem expandKey_correct (s : State) (hs : expandKeyArm.pre s) :
    ∃ t s', Exec isa expandKey s t s' ∧ abiPreserved s s' ∧ expandKeyArm.post s s' := by
  obtain ⟨t, s', he, h₁, h₂⟩ := expandKey_wp hs
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

/-- A state satisfying the precondition. -/
def expandKeySat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 128⟩, ⟨0x3000, 4 * 364⟩]

theorem expandKey_verified :
    Verified Arm.target expandKey (Proof.Sm4.expandKeyScratchContract Arm.abi 182) :=
  Verified.of_correct expandKey_correct expandKey_ct (by
    sig_implies [Proof.Sm4.expandKeyScratchContract, Proof.Sm4.expandKeyScratchSig, Proof.Sm4.expandKeyPost,
      expandKeyArm, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, State.addr, slots, nSlot, dSlot,
      savedSlot, tableEnd, tableSlot]
      [expandKeySat] using expandKeySat)

/-- A state satisfying the key schedule's precondition: the key at
`0x1000`, the schedule at `0x2000`. -/
def expandKeyFrameSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 128⟩]

theorem expandKeyFrameSat_pre : ∃ s, (Spec.Sm4.expandKeyContract Arm.abi 1456).pre s := by
  implies_sat [Spec.Sm4.expandKeyContract, Spec.Sm4.expandKeySig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val, Arm.State.addr] [expandKeyFrameSat] using expandKeyFrameSat

/-- Key expansion, with its working space on the stack. -/
theorem expandKey_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withRegScratchWiped 1456 .r2 364 expandKey)
      (Spec.Sm4.expandKeyContract Arm.abi 1456) :=
  Arm.Verified.regScratchWiped (sig := Spec.Sm4.expandKeySig) (nm := "scratch") (e := .u64)
    (n := 182) (post := Proof.Sm4.expandKeyPost Arm.abi.ptrBits) (wa := false) (stack := 0)
    expandKey_verified (by decide) (by decide) (by decide) (by decide)
    (Proof.Sm4.expandKeyPostOut_local _) expandKeyFrameSat_pre

end VG.Proof.Sm4.Arm
