module

public import VerifiedGarbage.Proof.Ffdh.X86.VettedValidation.Geometry
import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Ffdh.VettedTableFacts
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Ffdh.Contract
meta import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Ffdh.X86.CheckDomainVerified

/-! A concrete cdecl caller with disjoint input, scratch, stack, and static table. -/

@[expose] public section
namespace VG.Proof.Ffdh.X86.VettedValidation
open VG VG.X86
open VG.Impl.Ffdh.X86.VettedValidation VG.Impl.Ffdh.VettedGroups

private def satState (words : List (BitVec 64)) : State :=
  { CheckDomain.satState with
    mem := fun a => if a.toNat < 0x30000 then CheckDomain.satState.mem a else constMem 0x100000 words a
    rd := [⟨8192, 128⟩, ⟨0x100000, 17744⟩]
    syms := fun _ => 0x100000 }

private theorem satPre (words : List (BitVec 64)) :
    (Spec.Ffdh.checkDomainContract abi 172).pre (stripConsts [(tableSym, words)] (satState words)) := by
  have a0 : arg (satState words) 0 = 8192 := by change arg CheckDomain.satState 0 = 8192; decide
  have a1 : arg (satState words) 1 = 128 := by change arg CheckDomain.satState 1 = 128; decide
  have a2 : arg (satState words) 2 = 64 := by change arg CheckDomain.satState 2 = 64; decide
  have a3 : arg (satState words) 3 = 36864 := by change arg CheckDomain.satState 3 = 36864; decide
  have a4 : arg (satState words) 4 = 1056 := by change arg CheckDomain.satState 4 = 1056; decide
  have e : argAddr (satState words) 0 = 0x20004 := by change argAddr CheckDomain.satState 0 = 0x20004; decide
  have stripArg (i : Nat) : arg (stripConsts [(tableSym, words)] (satState words)) i = arg (satState words) i := rfl
  have stripAddr (i : Nat) : argAddr (stripConsts [(tableSym, words)] (satState words)) i = argAddr (satState words) i := rfl
  sig_pre [Spec.Ffdh.checkDomainContract, Spec.Ffdh.checkDomainSig, abi, argSlots, argVal, argBytes,
    stackBelow, Spec.Ffdh.pLenValid, Spec.Ffdh.domainLenValid, Spec.Rsa.scratchWords]
  simp only [stripArg, stripAddr, a0, a1, a2, a3, a4, e]
  repeat' apply And.intro
  all_goals first | rfl | decide | (apply Region.disjoint_of_sep; decide)

private theorem satLayout (words : List (BitVec 64)) (size : words.length = 2218) :
    (satState words).rd.drop ((satState words).rd.length - 1) = constRegs [(tableSym, words)] (satState words) := by
  simp only [constRegs, Abi.constRegions, satState, List.map_cons, List.map_nil, size, symAddr]
  rfl

private theorem satHeld (words : List (BitVec 64)) (size : words.length = 2218) :
    Abi.constsHeld (satState words).mem (symAddr (satState words)) [(tableSym, words)] := by
  intro c hc i hi
  obtain rfl := List.mem_singleton.mp hc
  have same : (satState words).mem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 =
      (constMem 0x100000 words).readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 := by
    apply Mem.readW_congr
    intro j hj
    change (if (0x100000 + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 j).toNat < 0x30000 then _ else _) = _
    have n : i < 2218 := by rw [size] at hi; exact hi
    rw [Offset.add_add, BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show 8 * i + j < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show (0x100000 : Addr).toNat + (8 * i + j) < 2 ^ 64 by change 1048576 + _ < _; omega)]
    simp only [show ¬ (0x100000 : Addr).toNat + (8 * i + j) < 0x30000 by change ¬ 1048576 + _ < _; omega,
      ↓reduceIte]
  exact same.trans (constMem_held 0x100000 words (by rw [size]; decide) i hi)

private theorem satRegions (words : List (BitVec 64)) (size : words.length = 2218) :
    ∀ r ∈ constRegs [(tableSym, words)] (satState words),
      r.base.toNat + r.len ≤ 2 ^ abi.ptrBits ∧
      (∀ q ∈ (satState words).wr, r.Disjoint q) ∧
      ∀ q ∈ abi.reserved 172 (satState words), r.Disjoint q := by
  intro r hr
  simp only [constRegs, Abi.constRegions, List.mem_map, List.mem_singleton] at hr
  obtain ⟨c, rfl, rfl⟩ := hr
  rw [size]
  change (0x100000 : Addr).toNat + 17744 ≤ 2 ^ 32 ∧
    (∀ q ∈ ([⟨36864, 8448⟩, ⟨0x20004, 20⟩] : List Region), (⟨0x100000, 17744⟩ : Region).Disjoint q) ∧
    ∀ q ∈ ([⟨0x20000, 4⟩, ⟨(0x20000 : Addr) - 172#64, 172⟩] : List Region),
      (⟨0x100000, 17744⟩ : Region).Disjoint q
  refine ⟨by decide +kernel, ?_, ?_⟩
  · intro q hq
    change q ∈ ([⟨36864, 8448⟩, ⟨0x20004, 20⟩] : List Region) at hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Region.disjoint_of_sep (by decide +kernel)
    · obtain rfl := List.mem_singleton.mp hq
      exact Region.disjoint_of_sep (by decide +kernel)
  · intro q hq
    change q ∈ ([⟨0x20000, 4⟩, ⟨(0x20000 : Addr) - 172#64, 172⟩] : List Region) at hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Region.disjoint_of_sep (by decide +kernel)
    · obtain rfl := List.mem_singleton.mp hq
      exact Region.disjoint_of_sep (by decide +kernel)

theorem sat : ∃ s, contract.pre s :=
  ⟨satState tableWords, pre_consts.mpr ⟨satPre tableWords, satLayout tableWords
    VG.Proof.Ffdh.VettedTableFacts.tableWords_length, satHeld tableWords
    VG.Proof.Ffdh.VettedTableFacts.tableWords_length, satRegions tableWords
    VG.Proof.Ffdh.VettedTableFacts.tableWords_length, fun r hr => by
      simp only [constRegs, Abi.constRegions, List.mem_map, List.mem_singleton] at hr
      obtain ⟨c, rfl, rfl⟩ := hr
      dsimp only [symAddr, satState]
      decide⟩⟩

end VG.Proof.Ffdh.X86.VettedValidation
