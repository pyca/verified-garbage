import VerifiedGarbage.Proof.Cast5.Arm.Ecb
import VerifiedGarbage.Proof.Cast5.Arm.Lit
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Cast5.Contract

/-!
# CAST5 ECB on ARMv7: verified

Constant time by the taint analysis: `r0`–`r3` and the stack argument (the
working space's address) are public; the working space's slots then hold
public values (pointers, counts, the type of the next round).
-/

namespace VG.Proof.Cast5.Arm

open VG VG.Arm VG.Impl.Cast5.Arm

/-- The initial taint: `r0`–`r3`, the 4 bytes of stack argument (the base of
writable region 1, the working space) are public. -/
def τEcb : VG.Arm.Taint.T :=
  { regs := .ofList [.r0, .r1, .r2, .r3], flags := false, lens := [0, 256], argLen := 4, argBases := [(0, 1)] }

theorem τEcb_wf {up : Bool} {s : State} (h : (ecbArm up).pre s) : VG.Arm.Taint.Wf τEcb s := by
  obtain ⟨_, hwr, _, _, dDS, aD, aS, _, hdf, hcf, hsp, _⟩ := h
  refine ⟨fun _ => ⟨by simp [hwr, τEcb], by simpa [hwr] using dDS, ?_⟩, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨hsp, ?_⟩, ?_⟩
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [toNat_addr] <;> omega
  · have e : (⟨State.addr s.sp, 4⟩ : Region) = ⟨stackArgAddr s 0, 4⟩ := by simp [stackArgAddr]
    simp only [τEcb, e, hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact aD
    · exact aS
  · intro p hp; simp only [τEcb, List.mem_singleton] at hp; subst hp
    refine ⟨by decide, ?_⟩
    simp only [VG.Arm.Taint.region, hwr]
    rfl

theorem τEcb_agree {up : Bool} {s₁ s₂ : State} (h₁ : (ecbArm up).pre s₁) (h₂ : (ecbArm up).pre s₂)
    (hp : (ecbArm up).pub s₁ s₂) : VG.Arm.Taint.Agree τEcb s₁ s₂ := by
  obtain ⟨psp, p0, p1, p2, p3, a0⟩ := hp
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, τEcb_wf h₁, τEcb_wf h₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => psp, fun k hk => ?_⟩
  · simp only [τEcb, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact p0
    · exact p1
    · exact p2
    · exact p3
  · rw [h₁.2.1, h₂.2.1, p2, p3, a0]
  · have argByte_eq (s : State) : Taint.argByte s k = stackArgAddr s 0 + BitVec.ofNat 64 k := by
      simp [Taint.argByte, stackArgAddr]
    simp only [τEcb] at hk
    rw [argByte_eq, argByte_eq, Mem.readW_byte s₁.mem _ hk, Mem.readW_byte s₂.mem _ hk]
    exact congrArg _ a0

theorem ecbEncrypt_constantTime : ConstantTime isa (ecbArm true).pre (ecbArm true).pub ecbEncrypt :=
  VG.Taint.constantTime (A := taint) τEcb (fun _ _ h₁ h₂ hp => τEcb_agree h₁ h₂ hp) (by taint_decide)

theorem ecbDecrypt_constantTime : ConstantTime isa (ecbArm false).pre (ecbArm false).pub ecbDecrypt :=
  VG.Taint.constantTime (A := taint) τEcb (fun _ _ h₁ h₂ hp => τEcb_agree h₁ h₂ hp) (by taint_decide)

theorem ecbArm_correct (up : Bool) (s : State) (hs : (ecbArm up).pre s) :
    ∃ t s', Exec isa (ecb up) s t s' ∧ abiPreserved s s' ∧ (ecbArm up).post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := ecb_correct up s hs
  exact ⟨t, s', he, ⟨ha, VG.Arm.Exec.sp he⟩, hp⟩

/-- A state satisfying the precondition: no blocks. -/
def ecbSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 12 | .r2 => 0x2000 | _ => 0
  sp := 0x4000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x4001 then 0x30 else 0
  rd := [⟨0x1000, 128⟩, ⟨0x4000, 4⟩]
  wr := [⟨0x2000, 0⟩, ⟨0x3000, 256⟩]

theorem ecbEncrypt_verified :
    Verified target ecbEncrypt (Spec.Cast5.ecbEncryptContract abi) := by
  refine Verified.of_correct (ecbArm_correct true) ecbEncrypt_constantTime ?_
  sig_implies [Spec.Cast5.ecbEncryptContract, Spec.Cast5.ecbContract, Spec.Cast5.ecbSig, Spec.Cast5.ecbPre,
    Spec.Cast5.ecbPost, abi, argRegs, Arm.reduceClassify, Arm.Loc.val, State.addr, ecbArm]
    [ecbSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using ecbSat

theorem ecbDecrypt_verified :
    Verified target ecbDecrypt (Spec.Cast5.ecbDecryptContract abi) := by
  refine Verified.of_correct (ecbArm_correct false) ecbDecrypt_constantTime ?_
  sig_implies [Spec.Cast5.ecbDecryptContract, Spec.Cast5.ecbContract, Spec.Cast5.ecbSig, Spec.Cast5.ecbPre,
    Spec.Cast5.ecbPost, abi, argRegs, Arm.reduceClassify, Arm.Loc.val, State.addr, ecbArm]
    [ecbSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using ecbSat

end VG.Proof.Cast5.Arm
