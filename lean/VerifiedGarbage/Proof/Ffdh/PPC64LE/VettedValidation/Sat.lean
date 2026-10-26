module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.VettedValidation.Geometry
import VerifiedGarbage.Proof.Ffdh.VettedTableFacts
import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import Batteries.Logic
import Mathlib.Util.CompileInductive
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Ffdh.Contract
meta import VerifiedGarbage.TCB.PPC64LE.Target

/-! A concrete PPC64LE caller satisfies the unchanged signature with the shared constants. -/

@[expose] public section
namespace VG.Proof.Ffdh.PPC64LE.VettedValidation
open VG VG.PPC64LE
open VG.Impl.Ffdh.PPC64LE.VettedValidation
open VG.Impl.Ffdh.VettedGroups

private def satState (words : List (BitVec 64)) : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 128 | .r5 => 64 | .r6 => 0x4000 | .r7 => 1056
    | _ => 0
  sp := 0x8000
  lr := 0
  mem := constMem 0x100000 words
  rd := [⟨0x1000, 128⟩, ⟨0x100000, 17744⟩]
  wr := [⟨0x4000, 8448⟩]
  syms _ := 0x100000

private theorem satPre (words : List (BitVec 64)) :
    (Spec.Ffdh.checkDomainContract abi).pre (stripConsts [(tableSym, words)] (satState words)) := by
  sig_pre [Spec.Ffdh.checkDomainContract, Spec.Ffdh.checkDomainSig, abi, argRegs,
    List.append_eq, Spec.Ffdh.pLenValid, Spec.Ffdh.domainLenValid, Spec.Rsa.scratchWords]
  repeat' apply And.intro
  all_goals first | rfl | decide | (apply Region.disjoint_of_sep; decide)

private theorem satLayout (words : List (BitVec 64)) (size : words.length = 2218) :
    (satState words).rd.drop ((satState words).rd.length - 1) =
      constRegs [(tableSym, words)] (satState words) := by
  simp only [constRegs, Abi.constRegions, satState, List.map_cons, List.map_nil, size]
  rfl

private theorem satHeld (words : List (BitVec 64)) (size : words.length = 2218) :
    Abi.constsHeld (satState words).mem (satState words).syms [(tableSym, words)] := by
  intro c hc i hi
  obtain rfl := List.mem_singleton.mp hc
  exact constMem_held 0x100000 words (by rw [size]; decide) i hi

private theorem fixedGeometry :
    (0x100000 : Addr).toNat + 17744 ≤ 2 ^ 64 ∧
    (⟨0x100000, 17744⟩ : Region).Disjoint ⟨0x4000, 8448⟩ := by
  exact ⟨by decide, Region.disjoint_of_sep (by decide)⟩

private theorem satRegions (words : List (BitVec 64)) (size : words.length = 2218) :
    ∀ r ∈ constRegs [(tableSym, words)] (satState words),
      r.base.toNat + r.len ≤ 2 ^ abi.ptrBits ∧
      (∀ q ∈ (satState words).wr, r.Disjoint q) ∧
      ∀ q ∈ abi.reserved 0 (satState words), r.Disjoint q := by
  intro r hr
  simp only [constRegs, Abi.constRegions, List.mem_map, List.mem_singleton] at hr
  obtain ⟨c, rfl, rfl⟩ := hr
  rw [size]
  refine ⟨fixedGeometry.1, ?_, ?_⟩
  · intro q hq
    change q ∈ ([⟨0x4000, 8448⟩] : List Region) at hq
    obtain rfl := List.mem_singleton.mp hq
    exact fixedGeometry.2
  · intro q hq
    change q ∈ ([] : List Region) at hq
    contradiction

private theorem satConsts (words : List (BitVec 64)) (size : words.length = 2218) :
    ConstsOk [(tableSym, words )] 0 (satState words) :=
  ⟨satLayout words size, satHeld words size, satRegions words size, fun r hr => by
    simp only [constRegs, Abi.constRegions, List.mem_map, List.mem_singleton] at hr
    obtain ⟨c, rfl, rfl⟩ := hr
    exact (by decide : (0x100000 : BitVec 64).toNat % 64 = 0)⟩

private theorem satAux (words : List (BitVec 64)) (size : words.length = 2218) :
    ∃ s, (Spec.Ffdh.checkDomainContract (abi.withConsts [(tableSym, words)])).pre s :=
  ⟨satState words, pre_consts.mpr ⟨satPre words, satConsts words size⟩⟩

theorem sat : ∃ s, contract.pre s :=
  satAux tableWords VG.Proof.Ffdh.VettedTableFacts.tableWords_length

end VG.Proof.Ffdh.PPC64LE.VettedValidation
