import VerifiedGarbage.Proof.Sm4.Arm.Ecb
import VerifiedGarbage.Proof.Sm4.Scratch
import VerifiedGarbage.Proof.Framework.Arm.Inline
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Arm.RegScratchWipe
import VerifiedGarbage.Proof.Framework.Contract

/-!
# SM4 ECB on ARMv7 meets its contracts

`ecb_verified`: `ecb dir` is correct (`ecb_wp`) and constant time, by the
taint analysis: the pointers, `n` and what the code computes from them are
public, in registers or, during the rounds, in the scratch buffer's slots
(which the rounds store to only through `sb`, the buffer's base). `ecb_framed`
runs it with its working space on the stack, zeroed on return: 1456 bytes,
the 364 words of the scratch buffer.
-/

namespace VG.Proof.Sm4.Arm

open VG VG.Arm VG.Impl.Sm4.Arm
open VG.Proof.Sm4 (specDirArm ecbArm)

/-- The initial taint: the pointers and `n` are public; `r3` points at the
scratch buffer, the second writable region. -/
def ecbTaint : VG.Arm.Taint.T :=
  { regs := .ofList [.r0, .r1, .r2, .r3], flags := false, lens := [0, 4 * slots], bases := [(.r3, 1)] }

theorem ecbTaint_wf (dir : Dir) {s : State} (h : (ecbArm dir).pre s) : VG.Arm.Taint.Wf ecbTaint s := by
  obtain ⟨-, hwr, -, -, dDS, -, fitD, fitB⟩ := h
  refine ⟨fun _ => ⟨by simp [hwr, ecbTaint], ?_, ?_⟩, fun p hp => ?_, fun h => by simp [ecbTaint] at h,
    fun p hp => by simp [ecbTaint] at hp⟩
  · simp only [hwr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
      List.Pairwise.nil]
    exact ⟨dDS, fun _ h => h.elim, trivial⟩
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [addr_toNat] <;> omega
  · simp only [ecbTaint, List.mem_singleton] at hp; subst hp
    simp [VG.Arm.Taint.region, hwr]

theorem ecbTaint_agree (dir : Dir) (s₁ s₂ : State) (h₁ : (ecbArm dir).pre s₁) (h₂ : (ecbArm dir).pre s₂)
    (hp : (ecbArm dir).pub s₁ s₂) : VG.Arm.Taint.Agree ecbTaint s₁ s₂ := by
  obtain ⟨p0, p1, p2, p3, -⟩ := hp
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, ecbTaint_wf dir h₁, ecbTaint_wf dir h₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun h => by simp [ecbTaint] at h,
    fun k hk => by simp [ecbTaint] at hk⟩
  · simp only [ecbTaint, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption
  · rw [h₁.2.1, h₂.2.1, p1, p2, p3]

theorem ecb_ct (dir : Dir) : ConstantTime isa (ecbArm dir).pre (ecbArm dir).pub (ecb dir) := by
  cases dir
  · exact VG.Taint.constantTime (A := VG.Arm.taint) ecbTaint (ecbTaint_agree .encrypt) (by taint_decide)
  · exact VG.Taint.constantTime (A := VG.Arm.taint) ecbTaint (ecbTaint_agree .decrypt) (by taint_decide)

theorem ecb_correct (dir : Dir) (s : State) (hs : (ecbArm dir).pre s) :
    ∃ t s', Exec isa (ecb dir) s t s' ∧ abiPreserved s s' ∧ (ecbArm dir).post s s' := by
  obtain ⟨t, s', he, h₁, h₂⟩ := ecb_wp dir hs
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

/-- A state satisfying the precondition (one block). -/
def ecbSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x3000 | .r2 => 1 | .r3 => 0x4000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x3000, 16⟩, ⟨0x4000, 4 * 364⟩]

theorem ecb_verified (dir : Dir) :
    Verified Arm.target (ecb dir) (Proof.Sm4.ecbScratchContract Arm.abi (specDirArm dir) 182) :=
  Verified.of_correct (ecb_correct dir) (ecb_ct dir) (by
    cases dir <;>
    sig_implies [Proof.Sm4.ecbScratchContract, Proof.Sm4.ecbScratchSig, Spec.Sm4.ecbPost, ecbArm, specDirArm,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, State.addr, slots, nSlot, dSlot, savedSlot,
      tableEnd, tableSlot] [ecbSat] using ecbSat)

/-- A state satisfying the ECB functions' precondition: the schedule at
`0x1000`, one block at `0x3000`. -/
def ecbFrameSat : State where
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

theorem ecbFrameSat_pre (d : Spec.Sm4.Direction) :
    ∃ s, (Spec.Sm4.ecbContract Arm.abi d 1456).pre s := by
  implies_sat [Spec.Sm4.ecbContract, Spec.Sm4.ecbSig, Spec.Sm4.ecbPost, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] [ecbFrameSat] using ecbFrameSat

/-- ECB in the direction `dir`, with its working space on the stack. -/
theorem ecb_framed (dir : Dir) :
    Verified Arm.target (Impl.StackScratch.Arm.withRegScratchWiped 1456 .r3 364 (ecb dir))
      (Spec.Sm4.ecbContract Arm.abi (specDirArm dir) 1456) :=
  Arm.Verified.regScratchWiped (sig := Spec.Sm4.ecbSig) (nm := "scratch") (e := .u64)
    (n := 182) (post := Spec.Sm4.ecbPost (specDirArm dir) Arm.abi.ptrBits) (wa := true) (stack := 0)
    (ecb_verified dir) (by decide) (by decide) (by decide) (by decide) (Proof.Sm4.ecbPostOut_local _ _)
    (ecbFrameSat_pre _)

end VG.Proof.Sm4.Arm
