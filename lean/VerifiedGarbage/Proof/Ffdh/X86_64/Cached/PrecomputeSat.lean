module

public import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract
public import VerifiedGarbage.Impl.Ffdh.X86_64.VettedValidation
public import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Ffdh.CachedSat
import VerifiedGarbage.Proof.Ffdh.VettedTableFacts
import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.StackScratchConsts
import Batteries.Logic
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract
meta import VerifiedGarbage.TCB.X86_64.Target

/-! # FFDH's context on x86-64: a caller that meets the contract

A valid 64-byte domain (`CachedSat.domain`), the context, the working
space, the stack argument and the vetted groups' table. -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Cached

open VG VG.X86_64
open VG.Impl.Ffdh.X86_64.VettedValidation
open VG.Impl.Ffdh.VettedGroups

private def baseMem (a : Addr) : Byte :=
  if a = 0x8008 then 0x20 else if a = 0x8009 then 4 else CachedSat.domainMem a

@[irreducible] private def satMem (W : List (BitVec 64)) : Mem := fun a =>
  if (a - 0x200000).toNat < 17744 then constMem 0x200000 W a else baseMem a

private theorem satMem_low (W : List (BitVec 64)) {a : Addr} (h : a.toNat < 0x100000) :
    satMem W a = baseMem a := by
  unfold satMem
  refine ite_eq_right_iff.mpr fun hc => absurd hc ?_
  rw [BitVec.toNat_sub, show (0x200000 : Addr).toNat = 0x200000 from rfl]
  omega

private def satState (W : List (BitVec 64)) : State where
  gpr r := match r with
    | .rdi => 0x100000 | .rsi => 275 | .rdx => 0x3000 | .rcx => 128 | .r8 => 64 | .r9 => 0x9000
    | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem W
  rd := [⟨0x3000, 128⟩, ⟨0x8008, 8⟩, ⟨0x200000, 17744⟩]
  wr := [⟨0x100000, 2200⟩, ⟨0x9000, 8448⟩]
  syms _ := 0x200000

private theorem satArg (W : List (BitVec 64)) : stackArg (satState W) 0 = 1056 := by
  unfold stackArg stackArgAddr
  show (satMem W).readW (0x8000 + BitVec.ofNat 64 8) 64 = 1056
  rw [Mem.readW_congr (m' := baseMem) (fun i hi => satMem_low W (by
    rw [BitVec.toNat_add, BitVec.toNat_add, show (0x8000 : Addr).toNat = 0x8000 from rfl]
    simp only [BitVec.toNat_ofNat]; omega))]
  decide

private theorem satArg' (W : List (BitVec 64)) :
    stackArg (stripConsts [(tableSym, W)] (satState W)) 0 = 1056 := satArg W

private theorem satAddr' (W : List (BitVec 64)) :
    stackArgAddr (stripConsts [(tableSym, W)] (satState W)) 0 = 0x8008 := rfl

private theorem satArgs (W : List (BitVec 64)) :
    List.map (stackArg (stripConsts [(tableSym, W)] (satState W))) (List.range 1) = [1056] := by
  rw [show List.range 1 = [0] from rfl, List.map_cons, List.map_nil, satArg']

private theorem satDomain (W : List (BitVec 64)) :
    Spec.Rsa.bytesAt (satMem W) 0x3000 128 = CachedSat.domain := by
  apply CachedSat.bytesAt_eq
  intro i hi
  rw [satMem_low W (by
    rw [BitVec.toNat_add, show (0x3000 : Addr).toNat = 0x3000 from rfl]
    simp only [BitVec.toNat_ofNat]; omega)]
  have : ∀ i < 128, baseMem (0x3000 + BitVec.ofNat 64 i) = CachedSat.domainMem (0x3000 + BitVec.ofNat 64 i) := by
    decide
  exact this i hi

private theorem satHeld (W : List (BitVec 64)) (length : W.length = 2218) (i : Nat) (hi : i < W.length) :
    (satMem W).readW (0x200000 + BitVec.ofNat 64 (8 * i)) 64 = W.getD i 0 := by
  rw [← constMem_held 0x200000 W (by rw [length]; decide) i hi]
  apply Mem.readW_congr
  intro j hj
  unfold satMem
  refine ite_eq_left ?_
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
  rw [length] at hi
  omega

private theorem satAux (W : List (BitVec 64)) (length : W.length = 2218) :
    ∃ s, (Spec.Ffdh.generationPrecomputeContract (abi.withConsts [(tableSym, W)]) 8).pre s := by
  refine ⟨satState W, pre_consts.mpr ⟨?_, ?_⟩⟩
  · sig_pre [Spec.Ffdh.generationPrecomputeContract, Spec.Ffdh.generationPrecomputeSig, Spec.Ffdh.pLenValid,
      Spec.Ffdh.domainLenValid, Spec.Ffdh.generationPrecomputedWords, Spec.Rsa.FixedBaseComb.precomputedWords,
      Spec.Rsa.modulusWords, Spec.Rsa.scratchWords, abi, argRegs, satArgs, satArg', satAddr']
    repeat' apply And.intro
    all_goals first
      | rfl
      | decide
      | (apply Region.disjoint_of_sep; decide)
      | (change Spec.Ffdh.domainValid 64 (Spec.Rsa.bytesAt (satMem W) 0x3000 128) = true
         rw [satDomain W]; exact CachedSat.domain_valid)
      | exact (by decide : (36864 : Nat) + 1056 * 8 ≤ 2 ^ 64)
  · refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [satState, constRegs, Abi.constRegions, List.map_cons, List.map_nil, length]
      rfl
    · intro c hc i hi
      obtain rfl := List.mem_singleton.mp hc
      exact satHeld W length i hi
    · intro r hr
      simp only [constRegs, Abi.constRegions, List.mem_map, List.mem_singleton] at hr
      obtain ⟨c, rfl, rfl⟩ := hr
      rw [length]
      dsimp only [satState]
      refine ⟨by decide, ?_, ?_⟩
      · intro q hq
        change q ∈ ([⟨0x100000, 2200⟩, ⟨0x9000, 8448⟩] : List Region) at hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl
        all_goals exact Region.disjoint_of_sep (by decide)
      · intro q hq
        change q ∈ ([⟨0x8000, 8⟩, ⟨(0x8000 : Addr) - BitVec.ofNat 64 8, 8⟩] : List Region) at hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl
        all_goals exact Region.disjoint_of_sep (by decide)
    · intro r hr
      simp only [constRegs, Abi.constRegions, List.mem_map, List.mem_singleton] at hr
      obtain ⟨c, rfl, rfl⟩ := hr
      exact (by decide : (0x200000 : BitVec 64).toNat % 64 = 0)

theorem precompute_sat :
    ∃ s, (Spec.Ffdh.generationPrecomputeContract (abi.withConsts tableConsts) 8).pre s :=
  satAux tableWords VG.Proof.Ffdh.VettedTableFacts.tableWords_length

end VG.Proof.Ffdh.X86_64.Cached
