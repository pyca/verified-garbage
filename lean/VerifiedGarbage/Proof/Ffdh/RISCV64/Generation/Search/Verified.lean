module

public import VerifiedGarbage.Proof.Ffdh.RISCV64.Generation.Search.Data
public import VerifiedGarbage.Impl.Ffdh.RISCV64.Generation.Search
public import VerifiedGarbage.Spec.Ffdh.GenerationContract
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Ffdh.RISCV64.ParameterCandidate.Verified
meta import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Ffdh.RISCV64.Generation.Search.Correct
import VerifiedGarbage.Proof.Ffdh.RISCV64.Generation.Search.CT
import VerifiedGarbage.Proof.Framework.Offset

/-! # The verified parameter search (RISC-V)

`searchContract` states the shared contract on the registers and the stack
(`search_implies`); with correctness (`search_correct`) and constant time
(`search_constantTime`), the search is verified for any candidate verified
against `vg_ffdh_parameter_candidate`'s contract with `S` bytes of stack
(`search_verified_of`), with `S + 32` bytes of its own; and for the
candidate calling each shared Miller–Rabin round (`search_verified`), as
`Generic/MillerRabin/RISCV64/Ffdh.lean` registers it.
-/

@[expose] public section

namespace VG.Proof.Ffdh.RISCV64.Generation

open VG VG.RISCV64 VG.Spec.Ffdh

theorem stackArgs_two (s : State) : List.map (stackArg s) (List.range 2) = [stackArg s 0, stackArg s 1] := rfl

private theorem args_nowrap {s : State} (h : s.sp.toNat + 8 * 2 ≤ 2 ^ 64) :
    (stackArgAddr s 0).toNat + 16 ≤ 2 ^ 64 := by
  simp only [stackArgAddr, Nat.mul_zero, BitVec.add_zero]
  omega

theorem search_implies_pre (S : Nat) (s : State) (h : (parameterSearchContract abi (stackUse S)).pre s) :
    (searchContract S).pre s := by
  sig_pre [parameterSearchContract, parameterSearchSig, abi, argRegs, stackBelow, searchContract, searchPre,
    inReads, inWrites, inOut, inUsed, inRand, inScr, inCtl, inArgs, stackArgs_two, List.append_eq] at h
  sig_pre [parameterSearchContract, parameterSearchSig, abi, argRegs, stackBelow, searchContract, searchPre,
    inReads, inWrites, inOut, inUsed, inRand, inScr, inCtl, inArgs, stackArgs_two, List.append_eq] at h
  sig_split h
  sig_reduce [parameterSearchContract, parameterSearchSig, abi, argRegs, stackBelow, searchContract, searchPre,
    inReads, inWrites, inOut, inUsed, inRand, inScr, inCtl, inArgs, stackArgs_two, List.append_eq]
  simp only [List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, List.pairwise_cons, List.Pairwise.nil, and_true, false_implies,
    implies_true]
  sig_and_intros
  sig_close
  all_goals first
    | (intro x hx; cases hx)
    | exact True.intro
    | with_reducible assumption
    | with_reducible rfl
    | omega
    | with_reducible exact Region.Disjoint.symm ‹_›
    | exact args_nowrap ‹_›

theorem search_implies_post (S : Nat) : ∀ s t, (parameterSearchContract abi (stackUse S)).pre s →
    (searchContract S).post s t → (parameterSearchContract abi (stackUse S)).post s t := by
  sig_implies_post [parameterSearchContract, parameterSearchSig, abi, argRegs, searchContract, searchPost,
    searchResult, genRand, genLen, genBits, genGen, genAttempts, stackArgs_two, List.append_eq,
    BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem search_implies_pub (S : Nat) (s t : State) (_hs : (parameterSearchContract abi (stackUse S)).pre s)
    (_ht : (parameterSearchContract abi (stackUse S)).pre t)
    (h : (parameterSearchContract abi (stackUse S)).pub s t) : (searchContract S).pub s t := by
  sig_pub [parameterSearchContract, parameterSearchSig, abi, argRegs, stackArgs_two, List.append_eq] at h
  simp only [List.getD_cons_succ, List.getD_cons_zero] at h
  obtain ⟨hsp, hleak, r0, r1, r2, r3, r4, r5, r6, r7, a0, a1⟩ := h
  have hl1 : (List.map (fun x => BitVec.toNat x) (Spec.Rsa.bytesAt s.mem (s.gpr .a5) (s.gpr .a6).toNat)).length =
      (List.map (fun x => BitVec.toNat x) (Spec.Rsa.bytesAt t.mem (t.gpr .a5) (t.gpr .a6).toNat)).length := by
    simp only [List.length_map, Spec.Rsa.bytesAt, List.length_range, r6]
  obtain ⟨hr, hw⟩ := List.append_inj hleak hl1
  exact ⟨hsp, hr, (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hw, r0, r1, r2, r3, r4, r5, r6, r7,
    a0, a1⟩

/-- A 512-bit search with an empty tape, its buffers above the stack. -/
private def searchSat : State where
  gpr r := match r with
    | .a0 => 0x300000 | .a1 => 64 | .a2 => 0x400000 | .a3 => 512 | .a4 => 2 | .a5 => 0x500000
    | .a7 => 0x600000 | _ => 0
  sp := 0x100000
  mem a := bif Nat.beq a.toNat 0x100000 then 0x20 else bif Nat.beq a.toNat 0x100001 then 0x04 else
    bif Nat.beq a.toNat 0x10000A then 0x20 else bif Nat.beq a.toNat 0x200008 then 0x40 else
    bif Nat.beq a.toNat 0x200010 then 0x40 else bif Nat.beq a.toNat 0x200012 then 0x20 else 0
  rd := [⟨0x500000, 0⟩, ⟨0x100000, 16⟩]
  wr := [⟨0x300000, 64⟩, ⟨0x400000, 8⟩, ⟨0x600000, 1056 * 8⟩, ⟨0x200000, 128⟩]

/-- The stack below `sp` is apart from a region above it. -/
private theorem below_apart {sp : Addr} {n : Nat} {r : Region} (hn : n ≤ sp.toNat)
    (hr : sp.toNat ≤ r.base.toNat) (hr' : r.base.toNat + r.len ≤ 2 ^ 64) :
    Region.Disjoint ⟨sp - BitVec.ofNat 64 n, n⟩ r := by
  refine Offset.disjoint_of_le ?_ hr'
  dsimp only
  rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]
  simp only [BitVec.toNat_ofNat]
  omega

theorem search_implies (S : Nat) (hS : S ≤ 2 ^ 16) :
    (searchContract S).Implies (parameterSearchContract abi (stackUse S)) where
  pre := search_implies_pre S
  post := search_implies_post S
  pub := search_implies_pub S
  sat := by
    refine ⟨searchSat, ?_⟩
    show (parameterSearchContract abi ((S + 31) + 1)).pre searchSat
    sig_iff
    sig_reduce [parameterSearchContract, parameterSearchSig, abi, argRegs, stackBelow, searchContract, searchPre,
      stackArgs_two, List.append_eq, parameterAttempts, parameterEntropy]
    sig_and_intros
    all_goals first
      | exact Region.disjoint_of_sep (by decide)
      | decide
      | (exact below_apart (by show S + 31 + 1 ≤ 1048576; omega) (by decide) (by decide))
      | (show S + 31 + 1 ≤ 1048576; omega)

theorem search_verified_of (c : Cand) :
    Verified target (Impl.Ffdh.RISCV64.Generation.Search.code c.call)
      (parameterSearchContract abi (stackUse c.S)) :=
  Verified.of_correct (search_correct c) (search_constantTime c) (search_implies c.S c.small)

/-- `vg_ffdh_parameter_candidate` calling the shared round `v`, as the search
calls it, with the round's 96 bytes of stack. -/
def Cand.ofRound (v : Proof.MillerRabin.RISCV64.RoundImpl) : Cand where
  name := "vg_ffdh_parameter_candidate" ++ v.suffix
  code := ParameterCandidate.candCode v
  S := 96
  pos := by decide
  small := by decide
  stack := ParameterCandidate.candidate_stack v
  verified := ParameterCandidate.candidate_verified v

/-- The search calling it. -/
abbrev searchCode (v : Proof.MillerRabin.RISCV64.RoundImpl) : Prog isa :=
  Impl.Ffdh.RISCV64.Generation.Search.code (Cand.ofRound v).call

theorem search_verified (v : Proof.MillerRabin.RISCV64.RoundImpl) :
    Verified target (searchCode v) (parameterSearchContract abi 128) :=
  search_verified_of (Cand.ofRound v)

end VG.Proof.Ffdh.RISCV64.Generation
