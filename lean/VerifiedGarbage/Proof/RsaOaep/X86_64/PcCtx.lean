module

public import VerifiedGarbage.Spec.RsaOaep.Tables
public import VerifiedGarbage.Proof.RsaOaep.X86_64.EncCall
import VerifiedGarbage.Proof.Framework.Omega

@[expose] public section

namespace VG.Proof.RsaOaep.X86_64.Pc

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

/-- The precomputed values, in bytes. -/
def preR (s : State) : Region := ⟨stackArg s 8, (stackArg s 9).toNat * 8⟩

/-- All nine stack arguments. -/
def argsR (s : State) : Region := ⟨stackArgAddr s 0, 80⟩

/-- The precondition of the original function, and the cache. -/
structure PPre (H : Spec.Mgf1.Hash) (s : State) : Prop extends EPre H s where
  sp3 : (s.gpr .rsp).toNat + 88 ≤ 2 ^ 64
  args : InRegions s.rd (stackArgAddr s 0) 80
  pre : InRegions s.rd (stackArg s 8) ((stackArg s 9).toNat * 8)
  argsOut : (argsR s).Disjoint (outR s)
  argsScr : (argsR s).Disjoint (scrR s)
  argsStack : (argsR s).Disjoint (stkR s)
  preOut : (preR s).Disjoint (outR s)
  preScr : (preR s).Disjoint (scrR s)
  preStack : (preR s).Disjoint (stkR s)
  preWrap : (stackArg s 8).toNat + (stackArg s 9).toNat * 8 ≤ 2 ^ 64
  preLen : (stackArg s 9).toNat = Spec.Rsa.precomputedWords (s.gpr .rcx).toNat

theorem stackArgs_twelve (s : State) :
    (List.range 12).map (stackArg s) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3, stackArg s 4,
      stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9, stackArg s 10, stackArg s 11] := rfl

/-- MGF1's table. -/
def tabE (s : State) : Region := ⟨stackArg s 11, 40⟩

/-- All ten stack arguments. -/
def argsT (s : State) : Region := ⟨stackArgAddr s 0, 96⟩

/-- The functions of the tables `ts`. -/
def tabFnsE (ts : List FnTable) : List String := (ts.map (·.fns)).flatten

/-- The contract, with the tables `ts` for both hash functions. -/
abbrev encC (ts : List FnTable) : Contract isa :=
  Spec.RsaOaep.encryptTablesContract (abi.withTables Spec.RsaOaep.encryptTablesSig [("hash", ts), ("mgf1", ts)])
    encStack

/-- The table of the label's hash function. -/
def tabLE (s : State) : Region := ⟨stackArg s 10, 40⟩

/-- `PPre`, with the tables: the label's hash function's (the stack argument
10) and MGF1's (11). -/
structure PPreT (H : Spec.Mgf1.Hash) (s : State) : Prop extends PPre H s where
  sp4 : (s.gpr .rsp).toNat + 104 ≤ 2 ^ 64
  argsT' : InRegions s.rd (stackArgAddr s 0) 96
  tab : InRegions s.rd (stackArg s 11) 40
  argsTOut : (argsT s).Disjoint (outR s)
  argsTScr : (argsT s).Disjoint (scrR s)
  argsTStack : (argsT s).Disjoint (stkR s)
  tabOut : (tabE s).Disjoint (outR s)
  tabScr : (tabE s).Disjoint (scrR s)
  tabStack : (tabE s).Disjoint (stkR s)
  tabWrap : (stackArg s 11).toNat + 40 ≤ 2 ^ 64
  tabL : InRegions s.rd (stackArg s 10) 40
  tabLOut : (tabLE s).Disjoint (outR s)
  tabLScr : (tabLE s).Disjoint (scrR s)
  tabLStack : (tabLE s).Disjoint (stkR s)
  tabLWrap : (stackArg s 10).toNat + 40 ≤ 2 ^ 64

/-- The tables: each one of `ts`. -/
theorem tabs_of {ts : List FnTable} {s : State} (h : (encC ts).pre s) :
    (∃ T ∈ ts, Abi.tableHeld 64 s.mem (stackArg s 10) (FnTable.words isa s T)) ∧
      (∃ T ∈ ts, Abi.tableHeld 64 s.mem (stackArg s 11) (FnTable.words isa s T)) ∧
      (tabFnsE ts).Pairwise (fun f g => f ≠ g → s.syms f ≠ s.syms g) := by
  sig_pre [Spec.RsaOaep.encryptTablesContract, Spec.RsaOaep.encryptTablesSig, Spec.RsaOaep.seedLenOk,
    Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex, abi, argRegs,
    encStack, stackArgs_twelve, List.append_eq, List.range, List.range.loop] at h
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left'] at h
  obtain ⟨-, -, t1, t2, fnd, -⟩ := h
  exact ⟨t1, t2, fnd.sublist (List.sublist_append_left _ _)⟩

/-- The precondition, for the hash function `H` that the table `hash` names. -/
theorem preT_of {H : Spec.Mgf1.Hash} {ts : List FnTable} {s : State} (h : (encC ts).pre s)
    (hH : Spec.HashTable.hashAt 64 s.mem (stackArg s 10) = some H) : PPreT H s := by
  sig_pre [Spec.RsaOaep.encryptTablesContract, Spec.RsaOaep.encryptTablesSig, Spec.RsaOaep.seedLenOk,
    Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex, abi, argRegs,
    encStack, stackArgs_twelve, List.append_eq, List.range, List.range.loop] at h
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left'] at h
  obtain ⟨sp1, sp3, -, -, -, hrd, hwr, dOn, dOe, dOl, dOm, dOsd, dOs, dOq, dOtL, dOt, dOa, dns, des, dls, dms,
    dsds, dsq, dstL, dst, dsa, dRo, dRn, dRe, dRl, dRm, dRsd, dRs, -, -, -, dRa, dKo, dKn, dKe, dKl, dKm, dKsd,
    dKs, dKq, dKtL, dKt, dKa, wO, wN, wE, wL, wM, wSd, wS, wQ, wTL, wT, ⟨k1, k2⟩, hsi, L1, L2, hsl, pl, hsd⟩ := h
  have hl := hsd H hH
  rw [hl] at hrd dOsd dsds dRsd dKsd wSd
  have ha : Region.Sub ⟨stackArgAddr s 0, 64⟩ ⟨stackArgAddr s 0, 96⟩ := Region.sub_prefix (by decide)
  have hb : Region.Sub ⟨stackArgAddr s 0, 80⟩ ⟨stackArgAddr s 0, 96⟩ := Region.sub_prefix (by decide)
  have hA : InRegions s.rd (stackArgAddr s 0) 96 := ⟨_, by rw [hrd]; simp, Region.contains_self _ _⟩
  refine ⟨⟨⟨sp1, by omega, ?_, hwr, dOn, dOe, dOl, dOm, dOsd, dOs, dOa.sub_right ha, dns, des, dls, dms, dsds,
    dsa.sub_right ha, dRo, dRn, dRe, dRl, dRm, dRsd, dRs, dRa.sub_right ha, dKo, dKn, dKe, dKl, dKm, dKsd, dKs,
    dKa.sub_right ha, wO, wN, wE, wL, wM, wSd, wS, k1, k2, hsi, L1, L2,
    by unfold Spec.RsaPss.publicScratchWords Spec.Rsa.publicScratchWords Spec.Rsa.modulusWords at hsl; omega⟩,
    by omega, ?_, ?_, (dOa.sub_right hb).symm, (dsa.sub_right hb).symm, (dKa.sub_right hb).symm, dOq.symm,
    dsq.symm, dKq.symm, wQ, pl⟩, sp3, hA, ⟨_, by rw [hrd]; simp [Sig.tableRegion], Region.contains_self _ _⟩,
    dOa.symm, dsa.symm, dKa.symm, dOt.symm, dst.symm, dKt.symm, wT,
    ⟨_, by rw [hrd]; simp [Sig.tableRegion], Region.contains_self _ _⟩, dOtL.symm, dstL.symm, dKtL.symm, wTL⟩
  · rw [hrd]
    apply Covers.of_sub
    intro r hr
    simp only [rdL, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
    · exact ⟨_, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
    · exact ⟨_, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
    · exact ⟨_, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
    · exact ⟨_, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
    · exact ⟨⟨stackArgAddr s 0, 96⟩, by simp, 0, (BitVec.add_zero _).symm, by dsimp only; decide⟩
  · exact ⟨⟨stackArgAddr s 0, 96⟩, by rw [hrd]; simp, by simp [Region.Contains]⟩
  · exact ⟨_, by rw [hrd]; simp, Region.contains_self _ _⟩

end VG.Proof.RsaOaep.X86_64.Pc
