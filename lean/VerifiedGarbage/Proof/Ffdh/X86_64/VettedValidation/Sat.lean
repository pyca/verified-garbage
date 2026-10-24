module

public import VerifiedGarbage.Proof.Ffdh.X86_64.VettedValidation.Geometry
import VerifiedGarbage.Proof.Ffdh.VettedTableFacts
import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import Batteries.Logic
import Mathlib.Util.CompileInductive
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Ffdh.Contract
meta import VerifiedGarbage.TCB.X86_64.Target

/-! A concrete SysV caller satisfies the unchanged signature with the shared constants. -/

@[expose] public section
namespace VG.Proof.Ffdh.X86_64.VettedValidation
open VG VG.X86_64
open VG.Impl.Ffdh.X86_64.VettedValidation
open VG.Impl.Ffdh.VettedGroups

private def satState (words : List (BitVec 64)) : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 128 | .rdx => 64 | .rcx => 0x4000 | .r8 => 1056
    | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := constMem 0x100000 words
  rd := [⟨0x1000, 128⟩, ⟨0x100000, 17744⟩]
  wr := [⟨0x4000, 8448⟩]
  syms _ := 0x100000

private theorem satPre (words : List (BitVec 64)) :
    (Spec.Ffdh.checkDomainContract abi 8).pre (stripConsts [(tableSym, words)] (satState words)) := by
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
    (⟨0x100000, 17744⟩ : Region).Disjoint ⟨0x4000, 8448⟩ ∧
    (⟨0x100000, 17744⟩ : Region).Disjoint ⟨0x8000, 8⟩ ∧
    (⟨0x100000, 17744⟩ : Region).Disjoint ⟨(0x8000 : Addr) - BitVec.ofNat 64 8, 8⟩ := by
  refine ⟨by decide, ?_, ?_, ?_⟩
  all_goals exact Region.disjoint_of_sep (by decide)

private theorem satRegions (words : List (BitVec 64)) (size : words.length = 2218) :
    ∀ r ∈ constRegs [(tableSym, words)] (satState words),
      r.base.toNat + r.len ≤ 2 ^ abi.ptrBits ∧
      (∀ q ∈ (satState words).wr, r.Disjoint q) ∧
      ∀ q ∈ abi.reserved 8 (satState words), r.Disjoint q := by
  intro r hr
  simp only [constRegs, Abi.constRegions, List.mem_map, List.mem_singleton] at hr
  obtain ⟨c, rfl, rfl⟩ := hr
  rw [size]
  refine ⟨fixedGeometry.1, ?_, ?_⟩
  · intro q hq
    change q ∈ ([⟨0x4000, 8448⟩] : List Region) at hq
    obtain rfl := List.mem_singleton.mp hq
    exact fixedGeometry.2.1
  · intro q hq
    change q ∈ ([⟨0x8000, 8⟩, ⟨(0x8000 : Addr) - BitVec.ofNat 64 8, 8⟩] : List Region) at hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact fixedGeometry.2.2.1
    · obtain rfl := List.mem_singleton.mp hq
      exact fixedGeometry.2.2.2

private theorem satConsts (words : List (BitVec 64)) (size : words.length = 2218) :
    ConstsOk [(tableSym, words)] 8 (satState words) :=
  ⟨satLayout words size, satHeld words size, satRegions words size⟩

private theorem satAux (words : List (BitVec 64)) (size : words.length = 2218) :
    ∃ s, (Spec.Ffdh.checkDomainContract (abi.withConsts [(tableSym, words)]) 8).pre s :=
  ⟨satState words, pre_consts.mpr ⟨satPre words, satConsts words size⟩⟩

theorem sat : ∃ s, contract.pre s :=
  satAux tableWords VG.Proof.Ffdh.VettedTableFacts.tableWords_length

end VG.Proof.Ffdh.X86_64.VettedValidation
