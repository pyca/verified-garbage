module

public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchContract
public import VerifiedGarbage.Spec.Ffdh.GenerationContract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # Match the complete native controller to its shared callable contract -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Spec.Ffdh VG.Proof.Ffdh.X86_64.ParameterCandidate

theorem stackArgs_four (s : State) : List.map (stackArg s) (List.range 4) =
    [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3] := rfl

private theorem candidate_gpr (s : State) : (candidateState s).gpr = s.gpr := rfl

private theorem candidate_rd (s : State) : (candidateState s).rd =
    [inputRand s, ⟨stackArgAddr s 0, 24⟩] := rfl

private theorem candidate_wr (s : State) : (candidateState s).wr = inputBuffers s := rfl

private theorem candidate_arg (s : State) (j : Nat) : stackArg (candidateState s) j = stackArg s j := rfl

private theorem candidate_argAddr (s : State) (j : Nat) :
    stackArgAddr (candidateState s) j = stackArgAddr s j := rfl

theorem search_implies_pre (s : State) (h : (parameterSearchContract abi 160).pre s) : searchContract.pre s := by
  sig_pre [parameterSearchContract, parameterSearchSig, abi, argRegs, stackBelow,
    searchContract, searchPre, pcPre, inputRand, inputArgs, inputBuffers,
    inputControl, candidate_gpr, candidate_rd, candidate_wr, candidate_arg, candidate_argAddr, stackArgs_four, List.append_eq] at h
  sig_pre [parameterSearchContract, parameterSearchSig, abi, argRegs, stackBelow,
    searchContract, searchPre, pcPre, inputRand, inputArgs, inputBuffers,
    inputControl, candidate_gpr, candidate_rd, candidate_wr, candidate_arg, candidate_argAddr, stackArgs_four, List.append_eq] at h
  sig_split h
  sig_reduce [parameterSearchContract, parameterSearchSig, abi, argRegs, stackBelow,
    searchContract, searchPre, pcPre, inputRand, inputArgs, inputBuffers,
    inputControl, candidate_gpr, candidate_rd, candidate_wr, candidate_arg, candidate_argAddr, stackArgs_four, List.append_eq]
  simp only [candidate_arg, candidate_argAddr, List.forall_mem_cons,
    BitVec.ofNat_toNat, BitVec.setWidth_eq] at *
  have haSub : Region.Sub ⟨stackArgAddr s 0, 24⟩ ⟨stackArgAddr s 0, 32⟩ := by
    simpa only [BitVec.add_zero] using Offset.sub_base (stackArgAddr s 0)
      (d := 0) (n := 24) (k := 32) (by decide)
  have hbSub : Region.Sub (below (s.gpr .rsp) 128) (below (s.gpr .rsp) 160) :=
    Offset.below_mono _ (by decide) (by decide)
  sig_and_intros
  sig_close
  all_goals first
    | (intro x hx; cases hx)
    | exact True.intro
    | with_reducible assumption
    | with_reducible rfl
    | omega
    | with_reducible exact Region.Disjoint.symm ‹_›
    | exact Region.Disjoint.sub_left (r₁ := ⟨stackArgAddr s 0, 32⟩)
        (by first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›) haSub
    | exact Region.Disjoint.sub_right (r₂ := below (s.gpr .rsp) 160)
        (by first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›) hbSub
    | exact Region.Disjoint.sub_right (r₂ := ⟨stackArgAddr s 0, 32⟩)
        (by first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›) haSub
    | exact Region.Disjoint.sub_left (r₁ := below (s.gpr .rsp) 160)
        (by first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›) hbSub
    | exact (Region.Disjoint.sub_right (r₁ := ⟨stackArgAddr s 0, 32⟩)
        (r₂ := below (s.gpr .rsp) 160)
        (by first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›) hbSub).sub_left haSub
    | exact ((Region.Disjoint.sub_right (r₁ := ⟨stackArgAddr s 0, 32⟩)
        (r₂ := below (s.gpr .rsp) 160)
        (by first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›) hbSub).sub_left haSub).symm

theorem search_implies_post : ∀ s t, (parameterSearchContract abi 160).pre s →
    searchContract.post s t → (parameterSearchContract abi 160).post s t := by
  sig_implies_post [parameterSearchContract, parameterSearchSig, abi, argRegs, searchContract,
    searchPost, searchResult, pcRand, stackArgs_four, List.append_eq, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem search_implies_pub (s t : State) (_hs : (parameterSearchContract abi 160).pre s)
    (_ht : (parameterSearchContract abi 160).pre t) (h : (parameterSearchContract abi 160).pub s t) :
    searchContract.pub s t := by
  sig_pub [parameterSearchContract, parameterSearchSig, abi, argRegs, stackArgs_four,
    List.append_eq] at h
  simp only [List.getD_cons_succ, List.getD_cons_zero] at h
  obtain ⟨hsp, hleak, rdi, rsi, rdx, rcx, r8, r9, a0, a1, a2, ast⟩ := h
  have hlen : (List.map (fun x => x.toNat) (pcRand s)).length =
      (List.map (fun x => x.toNat) (pcRand t)).length := by
    simp only [pcRand, Spec.Rsa.bytesAt, List.length_map, List.length_range, a0]
  obtain ⟨hbytes, hwords⟩ := List.append_inj hleak hlen
  have hc := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hwords
  exact ⟨⟨hsp, hbytes, rdi, rsi, rdx, rcx, r8, r9, a0, a1, a2⟩, ast, hc⟩

private def searchSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 64 | .rdx => 0x2000 | .rcx => 512 | .r8 => 2 | .r9 => 0x3000
    | .rsp => 0x6000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x6011 then 0x80 else if a = 0x6018 then 0x20 else if a = 0x6019 then 0x04
    else if a = 0x6021 then 0x40 else if a = 0x4008 then 0x40 else if a = 0x4010 then 0x40
    else if a = 0x4012 then 0x20 else 0
  rd := [⟨0x3000, 0⟩, ⟨0x6008, 32⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x2000, 8⟩, ⟨0x8000, 1056 * 8⟩, ⟨0x4000, 128⟩]

theorem search_implies : searchContract.Implies (parameterSearchContract abi 160) where
  pre := search_implies_pre
  post := search_implies_post
  pub := search_implies_pub
  sat := by
    sig_implies_sat [parameterSearchContract, parameterSearchSig, abi, argRegs, stackBelow,
      searchContract, searchPre, stackArgs_four, List.append_eq, searchSat]
      [searchSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using searchSat

end VG.Proof.Ffdh.X86_64.Generation
