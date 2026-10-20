module

public import VerifiedGarbage.Proof.Camellia.Arm.Ecb
public import VerifiedGarbage.Proof.Camellia.Scratch
public import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Arm.StackScratchWipe
public import VerifiedGarbage.Impl.StackScratch.Arm
public import VerifiedGarbage.Proof.Framework.Arm.NativeHintData
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Camellia.Arm.Lit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Camellia.Arm.Ecb
meta import VerifiedGarbage.Proof.Camellia.Scratch
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Arm.StackScratchWipe
meta import VerifiedGarbage.Impl.StackScratch.Arm
meta import VerifiedGarbage.Proof.Framework.Arm.NativeHintData
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Camellia.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# Camellia ECB on ARMv7 meets its contracts

`ecb_verified`: `ecb dir` is correct (`ecb_wp`) and constant time, by the
taint analysis: the pointers, `rounds`, `n` and what the code computes from
them are public, in registers or, during the rounds, in the scratch
buffer's slots (which the code stores to only through `sb`, the buffer's
base, loaded from the stack argument). `ecb_framed` runs it with its
working space on the stack, zeroed on return: 2816 bytes, of which the
scratch buffer is the 680 words after the copy of the arguments.
-/

@[expose] public section

namespace VG.Proof.Camellia.Arm

open VG VG.Arm VG.Impl.Camellia.Arm

/-- The initial taint: the registers' arguments and the stack argument are
public, and the stack argument is the base of the scratch buffer, the
second writable region. -/
def ecbTaint : VG.Arm.Taint.T :=
  { regs := .ofList [.r0, .r1, .r2, .r3], flags := false, lens := [0, 4 * slots], argLen := 4,
    argBases := [(0, 1)] }

theorem argMem_of {s₁ s₂ : State} {j : Nat} (hsp : s₁.sp = s₂.sp) (hf : s₁.sp.toNat + 4 * j ≤ 2 ^ 32)
    (h : ∀ i < j, stackArg s₁ i = stackArg s₂ i) :
    ∀ k < 4 * j, s₁.mem (VG.Arm.Taint.argByte s₁ k) = s₂.mem (VG.Arm.Taint.argByte s₂ k) := by
  intro k hk
  have e : ∀ s : State, s.sp.toNat + 4 * j ≤ 2 ^ 32 →
      VG.Arm.Taint.argByte s k = stackArgAddr s (k / 4) + BitVec.ofNat 64 (k % 4) := fun s hs => by
    simp only [VG.Arm.Taint.argByte, stackArgAddr]
    rw [VG.Arm.addr_add (by omega), BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2; omega
  rw [e s₁ hf, e s₂ (hsp ▸ hf), Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega)),
    Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega))]
  exact congrArg _ (h _ (by omega))

theorem ecbTaint_wf (dir : Dir) {s : State} (h : (ecbArm dir).pre s) : VG.Arm.Taint.Wf ecbTaint s := by
  obtain ⟨-, hwr, -, -, dDS, aD, aS, fitSp, -, fitD, fitB, -⟩ := h
  have e' : (⟨State.addr s.sp, 4⟩ : Region) = ⟨stackArgAddr s 0, 4⟩ := by simp [stackArgAddr]
  refine ⟨fun _ => ⟨by simp [hwr, ecbTaint], ?_, ?_⟩, fun p hp => by simp [ecbTaint] at hp,
    fun _ => ⟨fitSp, fun r hr => ?_⟩, fun p hp => ?_⟩
  · simp only [hwr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
      List.Pairwise.nil]
    exact ⟨dDS, fun _ h => h.elim, trivial⟩
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [addr_toNat] <;> omega
  · show (⟨State.addr s.sp, 4⟩ : Region).Disjoint r
    rw [e']
    simp only [hwr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact aD
    · exact aS
  · simp only [ecbTaint, List.mem_singleton] at hp; subst hp
    refine ⟨by decide, ?_⟩
    simp only [VG.Arm.Taint.region, hwr]
    rfl

theorem ecbTaint_agree (dir : Dir) (s₁ s₂ : State) (h₁ : (ecbArm dir).pre s₁) (h₂ : (ecbArm dir).pre s₂)
    (hp : (ecbArm dir).pub s₁ s₂) : VG.Arm.Taint.Agree ecbTaint s₁ s₂ := by
  obtain ⟨p0, p1, p2, p3, psp, pa⟩ := hp
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, ecbTaint_wf dir h₁, ecbTaint_wf dir h₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => psp,
    argMem_of (j := 1) psp h₁.2.2.2.2.2.2.2.1 fun i hi => by obtain rfl : i = 0 := (by omega); exact pa⟩
  · simp only [ecbTaint, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption
  · rw [h₁.2.1, h₂.2.1, p2, p3, pa]

theorem ecb_ct (dir : Dir) : ConstantTime isa (ecbArm dir).pre (ecbArm dir).pub (ecb dir) := by
  cases dir
  · exact VG.Taint.constantTime (A := VG.Arm.taint) ecbTaint (ecbTaint_agree .encrypt) (by native_taint_decide)
  · exact VG.Taint.constantTime (A := VG.Arm.taint) ecbTaint (ecbTaint_agree .decrypt) (by native_taint_decide)

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

/-- A state satisfying the precondition (one block, 18 rounds): the
schedule at `0x1000`, the block at `0x3000`, the scratch buffer at
`0x4000`, its address at the stack pointer, `0x8000`. -/
def ecbSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 18 | .r2 => 0x3000 | .r3 => 1 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := bif Nat.beq a.toNat 0x8001 then 0x40 else 0
  rd := [⟨0x1000, 272⟩, ⟨0x8000, 4⟩]
  wr := [⟨0x3000, 16⟩, ⟨0x4000, 4 * 680⟩]

theorem ecb_verified (dir : Dir) :
    Verified Arm.target (ecb dir) (Proof.Camellia.ecbScratchContract Arm.abi (specDir dir) 340) :=
  Verified.of_correct (ecb_correct dir) (ecb_ct dir) (by
    cases dir <;>
    sig_implies [Proof.Camellia.ecbScratchContract, Proof.Camellia.ecbScratchSig, Spec.Camellia.ecbSig,
      Spec.Camellia.ecbPre, Spec.Camellia.ecbPost, ecbArm, specDir, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val, Arm.State.addr, slots, tailSlot, savedSlot, endSlot, grpSlot, keySlot]
      [ecbSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using ecbSat)

/-- A state satisfying the ECB functions' precondition, without the working
space. -/
def ecbFrameSat : State := { ecbSat with mem := fun _ => 0, rd := [⟨0x1000, 272⟩], wr := [⟨0x3000, 16⟩] }

theorem ecbFrameSat_pre (d : Spec.Camellia.Direction) :
    ∃ s, (Spec.Camellia.ecbContract Arm.abi d 2816).pre s := by
  implies_sat [Spec.Camellia.ecbContract, Spec.Camellia.ecbSig, Spec.Camellia.ecbPre, Spec.Camellia.ecbPost,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [ecbFrameSat, ecbSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using ecbFrameSat

/-- ECB in the direction `dir`, with its working space on the stack. -/
theorem ecb_framed (dir : Dir) :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratchWiped 2816 0 680 (ecb dir))
      (Spec.Camellia.ecbContract Arm.abi (specDir dir) 2816) :=
  Arm.Verified.stackScratchWiped (sig := Spec.Camellia.ecbSig) (nm := "scratch") (e := .u64)
    (n := 340) (pre := Spec.Camellia.ecbPre Arm.abi.ptrBits)
    (post := Spec.Camellia.ecbPost (specDir dir) Arm.abi.ptrBits) (wa := false) (stack := 0)
    (bytes := 2816) (m := 0) (words := 680)
    (by rw [← Proof.Camellia.ecbScratchContract_eq]; exact ecb_verified dir)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (Proof.Camellia.ecbPre_local _) (Proof.Camellia.ecbPost_local _ _)
    (Proof.Camellia.ecbPostOut_local _ _) (ecbFrameSat_pre _)

end VG.Proof.Camellia.Arm
