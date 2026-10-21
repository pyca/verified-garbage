module

public import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract
public import VerifiedGarbage.Impl.Ffdh.Arm.VettedGroups
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Ffdh.Arm.VettedGroupsConsts
import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Lit
import Batteries.Logic
import Mathlib.Util.CompileInductive
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract
meta import VerifiedGarbage.TCB.Arm.Target

/-! The reviewed attempt contract has a concrete caller with its shared table. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm
open VG.Impl.Ffdh.Arm.VettedGroups

private def attemptBase : State where
  gpr r := match r with | .r0 => 0x1000 | .r1 => 275 | .r2 => 0x3000 | .r3 => 128 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x8000 then 64 else if a = 0x8005 then 0x90 else
    if a = 0x8008 then 0x20 else if a = 0x8009 then 4 else
    if a = 0x3000 then 0x80 else if a = 0x303f then 1 else if a = 0x307f then 2 else 0
  rd := [⟨0x3000,128⟩,⟨0x8000,12⟩]
  wr := [⟨0x1000,2200⟩,⟨0x9000,8448⟩]

@[irreducible] private def attemptMem (W : List (BitVec 64)) : Mem := fun a =>
  if (a - 0x100000).toNat < 17744 then constMem 0x100000 W a else attemptBase.mem a

private def attemptSat (W : List (BitVec 64)) : State :=
  { attemptBase with
    mem := attemptMem W
    rd := attemptBase.rd ++ [⟨0x100000, 17744⟩]
    syms := fun _ => 0x100000 }

private theorem attemptMem_held (W : List (BitVec 64)) (length : W.length = 2218) (i : Nat) (hi : i < W.length) :
    (attemptMem W).readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = W.getD i 0 := by
  rw [← constMem_held 0x100000 W (by rw [length]; decide) i hi]
  apply Mem.readW_congr
  intro j hj
  unfold attemptMem
  refine ite_eq_left ?_
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
  rw [length] at hi
  omega

private theorem attemptSat_arg (W : List (BitVec 64)) {i : Nat} (hi : i < 3) : stackArg (attemptSat W) i = stackArg attemptBase i := by
  apply Mem.readW_congr
  intro j hj
  change attemptMem W _ = attemptBase.mem _
  unfold attemptMem
  apply ite_eq_right
  have small : ∀ i < 3, ∀ j < 4,
      ¬ (stackArgAddr attemptBase i + BitVec.ofNat 64 j - 0x100000).toNat < 17744 := by decide
  exact small i hi j hj

private theorem attemptSat_domain (W : List (BitVec 64)) :
    Spec.Rsa.bytesAt (attemptMem W) 0x3000 128 = Spec.Rsa.bytesAt attemptBase.mem 0x3000 128 := by
  unfold Spec.Rsa.bytesAt
  apply List.map_congr_left
  intro i hi
  unfold attemptMem
  apply ite_eq_right
  have small : ∀ i < 128, ¬ ((0x3000 : Addr) + BitVec.ofNat 64 i - 0x100000).toNat < 17744 := by decide
  exact small i (List.mem_range.mp hi)

private theorem satAux (W : List (BitVec 64)) (length : W.length = 2218) :
    ∃ s, (Spec.Ffdh.generationPrecomputeContract (abi.withConsts [(tableSym, W)]) 176).pre s := by
  refine ⟨attemptSat W, pre_consts.mpr ⟨?_, ?_⟩⟩
  · have args (i : Nat) (hi : i < 3) := attemptSat_arg W hi
    sig_pre [Spec.Ffdh.generationPrecomputeContract, Spec.Ffdh.generationPrecomputeSig, Spec.Ffdh.pLenValid, Spec.Ffdh.domainLenValid, Spec.Ffdh.generationPrecomputedWords, Spec.Rsa.FixedBaseComb.precomputedWords, Spec.Rsa.modulusWords, Spec.Rsa.scratchWords, abi,
      argRegs, reduceClassify, Loc.val, State.addr]
    simp only [show ∀ (K : List (String × List (BitVec 64))) (s : State) (i : Nat), stackArg (stripConsts K s) i = stackArg s i by intros; rfl]
    simp only [args 0 (by decide), args 1 (by decide), args 2 (by decide)]
    dsimp only [stackArgAddr, stripConsts, State.withRegions, attemptSat, attemptBase]
    repeat' apply And.intro
    all_goals first
      | rfl
      | decide +kernel
      | (apply Region.disjoint_of_sep; decide +kernel)
      | (change Spec.Ffdh.domainValid 64 (Spec.Rsa.bytesAt (attemptMem W) 0x3000 128) = true
         rw [attemptSat_domain W]
         decide +kernel)
  · refine ⟨?_, ?_, ?_⟩
    · simp only [attemptSat, attemptBase, constRegs, Abi.constRegions, symAddr, List.map_cons, List.map_nil, length]
      rfl
    · intro c hc i hi
      simp only [List.mem_singleton] at hc
      subst c
      exact attemptMem_held W length i hi
    · intro r hr
      simp only [constRegs, Abi.constRegions, List.mem_map, List.mem_singleton] at hr
      obtain ⟨c, rfl, rfl⟩ := hr
      rw [length]
      dsimp only [symAddr, attemptSat]
      refine ⟨by decide, ?_, ?_⟩
      · intro q hq
        change q ∈ ([⟨0x1000,2200⟩,⟨0x9000,8448⟩] : List Region) at hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl
        all_goals first | (apply Region.disjoint_of_sep; decide)
      · intro q hq
        simp only [abi, stackBelow, List.mem_singleton] at hq
        subst q
        exact Region.disjoint_of_sep (by decide)

theorem combPrecompute_sat :
    ∃ s, (Spec.Ffdh.generationPrecomputeContract (abi.withConsts tableConsts) 176).pre s :=
  satAux tableWords VettedGroups.tableWords_length

end VG.Proof.Ffdh.Arm
