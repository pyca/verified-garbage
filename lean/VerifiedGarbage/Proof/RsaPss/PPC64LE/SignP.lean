module

public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Verified
import VerifiedGarbage.Proof.Framework.Contract

@[expose] public section

namespace VG.Proof.RsaPss.PPC64LE.Sg

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE VG.Impl.RsaPss.PPC64LE.Sign
open VG.Proof.RsaOaep.PPC64LE

theorem stackArgs_eighteen (s : State) :
    List.map (stackArg s) (List.range 18) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9, stackArg s 10,
      stackArg s 11, stackArg s 12, stackArg s 13, stackArg s 14, stackArg s 15, stackArg s 16, stackArg s 17] := rfl

abbrev signPSpec (hs gs : List FnTable) : Contract isa :=
  Spec.RsaPss.signPrecomputedMdTableContract
    (abi.withTables Spec.RsaPss.signPrecomputedMdTableSig [("hash", hs), ("mgf1", gs)]) (stackBytes true)

macro "signP_pre" " at " h:ident : tactic => `(tactic| (
  have e : stackBytes true = 3791 + 1 := rfl
  unfold signPSpec at $h:ident
  rw [e] at $h:ident
  sig_pre [Spec.RsaPss.signPrecomputedMdTableContract, Spec.RsaPss.signPrecomputedMdTableSig,
    Spec.RsaPss.digestLenOk, Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns,
    Spec.MdHashTable.dataWords, Abi.withTables,
    Sig.wordIndex, abi, argRegs, stackArgs_eighteen, List.append_eq, List.range, List.range.loop] at $h:ident
  sig_pre [Spec.RsaPss.signPrecomputedMdTableContract, Spec.RsaPss.signPrecomputedMdTableSig,
    Spec.RsaPss.digestLenOk, Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns,
    Spec.MdHashTable.dataWords, Abi.withTables,
    Sig.wordIndex, abi, argRegs, stackArgs_eighteen, List.append_eq, List.range, List.range.loop] at $h:ident
  simp only [Option.map_some, Nat.reduceAdd, List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq,
    exists_eq_left'] at $h:ident))

theorem preS_ofP {H : Spec.Mgf1.Hash} {hs gs : List FnTable} {s : State} (h : (signPSpec hs gs).pre s)
    (hH : Spec.MdHashTable.hashAt 64 s.mem (stackArg s 14) = some H) : PreS true H.len s ∧ PreXS s := by
  signP_pre at h
  exact h

end VG.Proof.RsaPss.PPC64LE.Sg
