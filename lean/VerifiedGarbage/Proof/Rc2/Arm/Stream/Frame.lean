module
public import VerifiedGarbage.Proof.Rc2.Arm.Stream.Common

import VerifiedGarbage.Proof.Rc2.Arm.Stream.Verified
import VerifiedGarbage.Proof.Framework.Arm.StackScratchWipe
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintSum
import VerifiedGarbage.Proof.Rc2.Arm.Lit

/-!
# RC2-CBC's `init` on ARMv7, with its working space on the stack

`init` runs its code, proved with the working space as an argument
(`Verified.lean`), in a frame of 592 bytes that allocates it and copies its
two other stack arguments (`Verified.stackScratchWipedC`, as it reads
PITABLE's table), and zeroes it before returning.
-/

@[expose] public section

namespace VG.Proof.Rc2.Arm.Stream

open VG VG.Arm
open VG.Impl.Rc2 (piSym piQuads piConsts)

/-- A state satisfying `vg_rc2_cbc_init`'s precondition, without the working
space. -/
def initFrameSat : State :=
  { initSatState with rd := [⟨0x1000, 0⟩, ⟨0x2000, 0⟩, ⟨0x6000, 8⟩], wr := [⟨0x3000, 144⟩] }

/-- `initFrameSat` with the table. -/
def initFrameSatC : State :=
  { initFrameSat with
    mem := initSatMem, rd := [⟨0x1000, 0⟩, ⟨0x2000, 0⟩, ⟨0x6000, 8⟩, ⟨0x100000, 256⟩], syms := fun _ => 0x100000 }

theorem initFrameSatC_arg {i : Nat} (hi : i < 3) : stackArg initFrameSatC i = stackArg initSatState i := by
  apply Mem.readW_congr
  intro j hj
  apply initSatMem_eq
  have h : ∀ i < 3, ∀ j < 4, ¬ (stackArgAddr initSatState i + BitVec.ofNat 64 j - 0x100000).toNat < 256 := by
    decide
  exact h i hi j hj

theorem initFrameSatC_pre : ∃ s, (Spec.Rc2.cbcInitContract (Arm.abi.withConsts piConsts) 600).pre s := by
  refine ⟨initFrameSatC, ?_⟩
  have hl : piQuads.length = 32 := piQuads_length
  have held := initSatMem_held
  have a0 := initFrameSatC_arg (i := 0) (by decide)
  have a1 := initFrameSatC_arg (i := 1) (by decide)
  rw [piConsts_eq]
  generalize piQuads = W at hl held ⊢
  generalize e : initFrameSatC = s at a0 a1
  sig_pre [Spec.Rc2.cbcInitContract, Spec.Rc2.cbcInitSig, Spec.Rc2.cbcInitPost, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow]
  subst e
  have v0 : stackArg initSatState 0 = 0 := by decide
  have v1 : stackArg initSatState 1 = 0x3000 := by decide
  rw [a0, a1, v0, v1, hl]
  refine ⟨by decide, by decide, by decide, fun i hi => held i (by rw [hl]; exact hi), by decide, ?_, ?_⟩
  · intro r hr
    change r ∈ ([⟨0x3000, 144⟩] : List Region) at hr
    simp only [List.mem_singleton] at hr
    subst hr
    exact Region.disjoint_of_sep (by decide)
  · repeat' apply And.intro
    all_goals first | rfl | decide | exact Region.disjoint_of_sep (by decide)

theorem init_framed :
    Verified Arm.target
      (Impl.StackScratch.Arm.withStackScratchWiped 592 2 144 Impl.Rc2.Arm.Stream.init)
      (Spec.Rc2.cbcInitContract (Arm.abi.withConsts piConsts) 600) :=
  Arm.Verified.stackScratchWipedC (c₀ := (piSym, piQuads)) (cs := []) (sig := Spec.Rc2.cbcInitSig)
    (nm := "scratch") (e := .u64) (n := 72) (post := Spec.Rc2.cbcInitPost Arm.abi.ptrBits) (wa := true)
    (stack := 8) (bytes := 592) (m := 2) (words := 144) init_verified (by decide) (by decide) (by decide)
    (by decide) (by decide)
    (fun vs _ m₂ _ _ _ => (congrFun (Curry.apply_const (fun _ : Mem => True) (Spec.Rc2.cbcInitSig.words abi.ptrBits)
      vs) m₂).mpr trivial)
    (cbcInitPost_local _) (cbcInitPostOut_local _) initFrameSatC_pre

end VG.Proof.Rc2.Arm.Stream
