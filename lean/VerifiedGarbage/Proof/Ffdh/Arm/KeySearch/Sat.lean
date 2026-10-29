module

public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Contract
import VerifiedGarbage.Proof.Ffdh.Arm.CachedSatWitness
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.ConstantContract
import VerifiedGarbage.Proof.Ffdh.Arm.VettedGroupsConsts
import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import Batteries.Logic
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Ffdh.KeyGenerationContract
meta import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyConstants
public import Init.Data.BitVec.BasicAux
public import Init.Data.List.Basic
public import Init.Data.Nat.Bitwise.Basic
public import VerifiedGarbage.TCB.Arm.Target

/-! A concrete legal ARMv7 key-search invocation: a structurally valid
512-bit domain without q and an exhausted initialized retry budget. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
variable {sampling : VG.Proof.Ffdh.GenerationPolicy}

open VG VG.Arm VG.Spec.Ffdh

private def keySat : State where
  gpr r := match r with | .r0 => 0x1000 | .r1 => 64 | .r2 => 0x2000 | .r3 => 64 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x8001 then 0x50 else if a = 0x8005 then 0x30 else if a = 0x8008 then 0x80
    else if a = 0x800C then 0x40 else if a = 0x8011 then 0x70 else if a = 0x8019 then 0x90
    else if a = 0x801C then 0x20 else if a = 0x801D then 4 else if a = 0x8021 then 0x40
    else if a = 0x4010 then 0x40 else if a = 0x3000 then 0x80 else if a = 0x303F then 1
    else if a = 0x307F then 2 else 0
  rd := [⟨0x3000, 128⟩, ⟨0x7000, 0⟩, ⟨0x8000, 36⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x2000, 64⟩, ⟨0x5000, 8⟩, ⟨0x9000, 8448⟩, ⟨0x4000, 128⟩]

theorem plain_sat : ∃ s, (GenerationPolicy.searchContract .full abi (stackUse .full)).pre s := by
  refine ⟨keySat, ?_⟩
  rw [GenerationPolicy.searchContract_full]
  sig_iff
  sig_reduce [Spec.Ffdh.keySearchContract, keySearchSig, pLenValid, domainLenValid,
    abi, argRegs, reduceClassify, Loc.val, State.addr]
  sig_and_intros
  all_goals first
    | exact Region.disjoint_of_sep (by decide +kernel)
    | decide +kernel


@[irreducible] private def searchMem (W : List (BitVec 64)) : Mem := fun a =>
  if (a - 0x100000).toNat < 17744 then constMem 0x100000 W a else keySat.mem a

private def searchSat (W : List (BitVec 64)) : State :=
  { keySat with mem := searchMem W, rd := keySat.rd ++ [⟨0x100000, 17744⟩], syms := fun _ => 0x100000 }

private theorem searchMem_held (W : List (BitVec 64)) (length : W.length = 2218) (i : Nat) (hi : i < W.length) :
    (searchMem W).readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = W.getD i 0 := by
  rw [← constMem_held 0x100000 W (by rw [length]; decide) i hi]
  apply Mem.readW_congr
  intro j hj
  unfold searchMem
  refine ite_eq_left ?_
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
  rw [length] at hi
  omega

private theorem searchSat_arg (W : List (BitVec 64)) {i : Nat} (hi : i < 9) :
    stackArg (searchSat W) i = stackArg keySat i := by
  apply Mem.readW_congr
  intro j hj
  change searchMem W _ = keySat.mem _
  unfold searchMem
  apply ite_eq_right
  have small : ∀ i < 9, ∀ j < 4,
      ¬ (stackArgAddr keySat i + BitVec.ofNat 64 j - 0x100000).toNat < 17744 := by decide
  exact small i hi j hj

private theorem searchSat_domain (W : List (BitVec 64)) :
    Spec.Rsa.bytesAt (searchMem W) 0x3000 128 = Spec.Rsa.bytesAt keySat.mem 0x3000 128 := by
  unfold Spec.Rsa.bytesAt
  apply List.map_congr_left
  intro i hi
  unfold searchMem
  apply ite_eq_right
  have small : ∀ i < 128, ¬ ((0x3000 : Addr) + BitVec.ofNat 64 i - 0x100000).toNat < 17744 := by decide
  exact small i (List.mem_range.mp hi)

private theorem searchSat_control (W : List (BitVec 64)) {a : Addr}
    (ha : a ∈ [0x4000, 0x4008, 0x4010]) :
    (searchMem W).readW a 64 = keySat.mem.readW a 64 := by
  apply Mem.readW_congr
  intro j hj
  unfold searchMem
  apply ite_eq_right
  have small : ∀ a : Addr, a ∈ [0x4000, 0x4008, 0x4010] → ∀ j < 8,
      ¬ (a + BitVec.ofNat 64 j - 0x100000).toNat < 17744 := by decide
  exact small a ha j hj

private theorem vetted_satAux (W : List (BitVec 64)) (length : W.length = 2218) :
    ∃ s, (GenerationPolicy.vetted.searchContract (abi.withConsts [(VG.Impl.Ffdh.Arm.VettedGroups.tableSym, W)]) (stackUse .vetted)).pre s := by
  rw [GenerationPolicy.searchContract_vetted]
  unfold Spec.Ffdh.vettedKeySearchContract
  refine ⟨searchSat W, pre_consts.mpr ⟨?_, ?_⟩⟩
  · have args (i : Nat) (hi : i < 9) := searchSat_arg W hi
    sig_pre [Spec.Ffdh.vettedKeySearchContract, keySearchSig, pLenValid, domainLenValid,
      abi, argRegs, reduceClassify, Loc.val, State.addr]
    simp only [show ∀ (K : List (String × List (BitVec 64))) (s : State) (i : Nat),
      stackArg (stripConsts K s) i = stackArg s i by intros; rfl]
    simp only [args 0 (by decide), args 1 (by decide), args 2 (by decide), args 3 (by decide),
      args 4 (by decide), args 5 (by decide), args 6 (by decide), args 7 (by decide), args 8 (by decide)]
    have v0 : stackArg keySat 0 = 0x5000 := by decide
    have v1 : stackArg keySat 1 = 0x3000 := by decide
    have v2 : stackArg keySat 2 = 128 := by decide
    have v3 : stackArg keySat 3 = 64 := by decide
    have v4 : stackArg keySat 4 = 0x7000 := by decide
    have v5 : stackArg keySat 5 = 0 := by decide
    have v6 : stackArg keySat 6 = 0x9000 := by decide
    have v7 : stackArg keySat 7 = 1056 := by decide
    have v8 : stackArg keySat 8 = 0x4000 := by decide
    rw [v0, v1, v2, v3, v4, v5, v6, v7, v8]
    dsimp only [stackArgAddr, stripConsts, State.withRegions, searchSat, keySat]
    repeat' apply And.intro
    all_goals first
      | rfl
      | decide +kernel
      | (apply Region.disjoint_of_sep; decide +kernel)
      | (change domainValid 64 (Spec.Rsa.bytesAt (searchMem W) 0x3000 128) = true
         rw [searchSat_domain W]
         decide +kernel)
      | (change ((searchMem W).readW 0x4000 64).toNat ≤ 128
         rw [searchSat_control W (by simp)]
         decide +kernel)
      | (change ((searchMem W).readW 0x4008 64).toNat ≤ 128
         rw [searchSat_control W (by simp)]
         decide +kernel)
      | (change (searchMem W).readW 0x4010 64 = 64
         rw [searchSat_control W (by simp)]
         decide +kernel)
  · refine ⟨?_, ?_, ?_, fun r hr => by
      simp only [constRegs, Abi.constRegions, List.mem_map, List.mem_singleton] at hr
      obtain ⟨c, rfl, rfl⟩ := hr
      dsimp only [symAddr, searchSat]
      decide⟩
    · simp only [searchSat, keySat, constRegs, Abi.constRegions, symAddr, List.map_cons, List.map_nil, length]
      rfl
    · intro c hc i hi
      simp only [List.mem_singleton] at hc
      subst c
      exact searchMem_held W length i hi
    · intro r hr
      simp only [constRegs, Abi.constRegions, List.mem_map, List.mem_singleton] at hr
      obtain ⟨c, rfl, rfl⟩ := hr
      rw [length]
      dsimp only [symAddr, searchSat]
      refine ⟨by decide, ?_, ?_⟩
      · intro q hq
        change q ∈ ([⟨0x1000, 64⟩, ⟨0x2000, 64⟩, ⟨0x5000, 8⟩, ⟨0x9000, 8448⟩, ⟨0x4000, 128⟩] : List Region) at hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl
        all_goals apply Region.disjoint_of_sep; decide
      · intro q hq
        simp only [abi, stackBelow, stackUse, GenerationPolicy.searchStack, List.mem_singleton] at hq
        subst q
        exact Region.disjoint_of_sep (by decide)

private def cachedSearchBase : State :=
  { keySat with
    mem := fun a => if a=0x8026 then 0x10 else if a=0x8028 then 0x13
      else if a=0x8029 then 1 else keySat.mem a
    rd := [⟨0x3000,128⟩,⟨0x7000,0⟩,⟨0x100000,2200⟩,⟨0x8000,44⟩] }

private def cachedSearchSat : State :=
  {cachedSearchBase with mem := CachedSat.withContext cachedSearchBase.mem}

private theorem cachedSearch_arg (i : Nat) (hi : i<11) :
    stackArg cachedSearchSat i=stackArg cachedSearchBase i := by
  apply CachedSat.readW_outside
  have small : ∀ i<11, (stackArgAddr cachedSearchBase i).toNat+4≤0x100000 := by decide
  exact small i hi

private theorem cachedSearch_domain :
    Spec.Rsa.bytesAt cachedSearchSat.mem 0x3000 128=CachedSat.domain := by
  rw [show cachedSearchSat.mem=CachedSat.withContext cachedSearchBase.mem from rfl,CachedSat.domain_unchanged]
  unfold CachedSat.domain
  decide +kernel

private theorem cachedSearch_control {a : Addr} (ha : a ∈ [0x4000,0x4008,0x4010]) :
    cachedSearchSat.mem.readW a 64=cachedSearchBase.mem.readW a 64 := by
  apply CachedSat.readW_outside
  have small : ∀ a : Addr, a ∈ [0x4000,0x4008,0x4010] → a.toNat+8≤0x100000 := by decide
  exact small a ha

theorem cached_sat : ∃ s, (GenerationPolicy.cached.searchContract abi (stackUse .cached)).pre s := by
  refine ⟨cachedSearchSat,?_⟩
  sig_pre [GenerationPolicy.searchContract,cachedKeySearchContract,cachedKeySearchSig,keySearchSig,
    pLenValid,domainLenValid,abi,argRegs,reduceClassify,Loc.val,State.addr]
  simp only [cachedSearch_arg 0 (by decide),cachedSearch_arg 1 (by decide),cachedSearch_arg 2 (by decide),cachedSearch_arg 3 (by decide),cachedSearch_arg 4 (by decide),cachedSearch_arg 5 (by decide),cachedSearch_arg 6 (by decide),cachedSearch_arg 7 (by decide),cachedSearch_arg 8 (by decide),cachedSearch_arg 9 (by decide),cachedSearch_arg 10 (by decide)]
  have a0 : stackArg cachedSearchBase 0=0x5000 := by decide
  have a1 : stackArg cachedSearchBase 1=0x3000 := by decide
  have a2 : stackArg cachedSearchBase 2=128 := by decide
  have a3 : stackArg cachedSearchBase 3=64 := by decide
  have a4 : stackArg cachedSearchBase 4=0x7000 := by decide
  have a5 : stackArg cachedSearchBase 5=0 := by decide
  have a6 : stackArg cachedSearchBase 6=0x9000 := by decide
  have a7 : stackArg cachedSearchBase 7=1056 := by decide
  have a8 : stackArg cachedSearchBase 8=0x4000 := by decide
  have a9 : stackArg cachedSearchBase 9=0x100000 := by decide
  have a10 : stackArg cachedSearchBase 10=275 := by decide
  rw [a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10]
  dsimp only [cachedSearchSat,cachedSearchBase,keySat]
  repeat' apply And.intro
  all_goals first
    | (change domainValid 64 (Spec.Rsa.bytesAt cachedSearchSat.mem 0x3000 128)=true
       rw [cachedSearch_domain]; exact CachedSat.domain_valid)
    | (change Spec.Ffdh.generationPrecompute 64 (Spec.Rsa.bytesAt cachedSearchSat.mem 0x3000 128) =
         some (Spec.Rsa.wordsAt cachedSearchSat.mem 0x100000 275)
       rw [cachedSearch_domain]; exact (CachedSat.canonical _).2)
    | (change (cachedSearchSat.mem.readW 0x4000 64).toNat≤128
       rw [cachedSearch_control (by simp)]; decide +kernel)
    | (change (cachedSearchSat.mem.readW 0x4008 64).toNat≤128
       rw [cachedSearch_control (by simp)]; decide +kernel)
    | (change cachedSearchSat.mem.readW 0x4010 64=64
       rw [cachedSearch_control (by simp)]; decide +kernel)
    | decide +kernel
    | (apply Region.disjoint_of_sep; decide +kernel)

theorem sat : ∃ s, (GenerationPolicy.searchContract sampling (KeyConstants.abi sampling) (stackUse sampling)).pre s := by
  cases sampling with
  | full => exact plain_sat
  | vetted => exact vetted_satAux _ VettedGroups.tableWords_length
  | cached => exact cached_sat

end VG.Proof.Ffdh.Arm.KeySearch
