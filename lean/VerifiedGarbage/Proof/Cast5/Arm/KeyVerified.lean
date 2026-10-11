import VerifiedGarbage.Proof.Cast5.Arm.Key
import VerifiedGarbage.Proof.Cast5.Arm.Lit
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Cast5.Contract

/-!
# CAST5 key expansion on ARMv7: verified

Constant time by the taint analysis: `r0`–`r3` (the pointers and the key's
length) are public, `r3` the working space's base; the step and half counts
and the schedule's pointer are computed from them.
-/

namespace VG.Proof.Cast5.Arm

open VG VG.Arm VG.Impl.Cast5.Arm

/-- The initial taint: `r0`–`r3` public, `r3` the base of writable region 1. -/
def τKey : VG.Arm.Taint.T :=
  { regs := .ofList [.r0, .r1, .r2, .r3], flags := false, lens := [128, 256], bases := [(.r3, 1)] }

theorem τKey_wf {s : State} (h : keyArm.pre s) : VG.Arm.Taint.Wf τKey s := by
  obtain ⟨_, hwr, _, _, dKS, _, hKf, hcf, _⟩ := h
  refine ⟨fun _ => ⟨by simp [hwr, τKey], by simpa [hwr] using dKS, ?_⟩, fun p hp => ?_, fun h => absurd h (by decide),
    fun _ h => (List.not_mem_nil h).elim⟩
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [toNat_addr] <;> omega
  · simp only [τKey, List.mem_singleton] at hp; subst hp
    simp only [VG.Arm.Taint.region, hwr]
    rfl

theorem τKey_agree {s₁ s₂ : State} (h₁ : keyArm.pre s₁) (h₂ : keyArm.pre s₂) (hp : keyArm.pub s₁ s₂) :
    VG.Arm.Taint.Agree τKey s₁ s₂ := by
  obtain ⟨_, p0, p1, p2, p3⟩ := hp
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, τKey_wf h₁, τKey_wf h₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun h => absurd h (by decide),
    fun k hk => absurd hk (Nat.not_lt_zero k)⟩
  · simp only [τKey, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact p0
    · exact p1
    · exact p2
    · exact p3
  · rw [h₁.2.1, h₂.2.1, p2, p3]

theorem expandKey_constantTime : ConstantTime isa keyArm.pre keyArm.pub expandKey :=
  VG.Taint.constantTime (A := taint) τKey (fun _ _ h₁ h₂ hp => τKey_agree h₁ h₂ hp) (by taint_decide)

theorem keyArm_correct (s : State) (hs : keyArm.pre s) :
    ∃ t s', Exec isa expandKey s t s' ∧ abiPreserved s s' ∧ keyArm.post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := key_correct s hs
  exact ⟨t, s', he, ⟨ha, VG.Arm.Exec.sp he⟩, hp⟩

/-- A state satisfying the precondition: a key of five bytes. -/
def keySat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 5 | .r2 => 0x2000 | .r3 => 0x3000 | _ => 0
  sp := 0x4000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 5⟩]
  wr := [⟨0x2000, 128⟩, ⟨0x3000, 256⟩]

theorem expandKey_verified : Verified target expandKey (Spec.Cast5.expandKeyContract abi) := by
  refine Verified.of_correct keyArm_correct expandKey_constantTime ?_
  sig_implies [Spec.Cast5.expandKeyContract, Spec.Cast5.expandKeySig, Spec.Cast5.expandKeyPre,
    Spec.Cast5.expandKeyPost, abi, argRegs, Arm.reduceClassify, Arm.Loc.val, State.addr, keyArm,
    Spec.Cast5.validKey] [keySat] using keySat

end VG.Proof.Cast5.Arm
