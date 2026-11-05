module

public import VerifiedGarbage.Spec.RsaPss.Table
public import VerifiedGarbage.Proof.RsaPss.AArch64.SignPre
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.PrecomputedCorrect
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract

/-!
# RSASSA-PSS verification on AArch64: the precondition

`PreV tsH tsG K s`: what the code needs of the contract's precondition
(`verifyPrecomputedTableContract`, with the stack `stk K` of the frame and a
callee using `K` bytes), by name. The frame is that of signing (`Sgn.fb`).
`preV_of` gives it from the contract's precondition.
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64.Vfy

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Proof.RsaPss.AArch64.Sgn (stk kR fb kb frame_sub0 stackArgAddr_eq keep_of_frame)

/-- The buffers: `n`, `e`, the digest, the signature, the working space, the
precomputed values, the tables and the arguments on the stack. -/
abbrev nR (s : State) : Region := ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
abbrev eR (s : State) : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
abbrev dgR (s : State) : Region := ⟨s.gpr .x4, (s.gpr .x5).toNat⟩
abbrev sgR (s : State) : Region := ⟨s.gpr .x6, (s.gpr .x7).toNat⟩
abbrev sR (s : State) : Region := ⟨stackArg s 2, (stackArg s 3).toNat * 8⟩
abbrev pR (s : State) : Region := ⟨stackArg s 4, (stackArg s 5).toNat * 8⟩
abbrev tHR (s : State) : Region := Sig.tableRegion 64 (stackArg s 6) 11
abbrev tGR (s : State) : Region := Sig.tableRegion 64 (stackArg s 7) 5
abbrev aR (s : State) : Region := ⟨stackArgAddr s 0, 64⟩

/-- The ABI the contract states, with the tables. -/
abbrev verifyAbi (tsH tsG : List FnTable) : Abi isa :=
  abi.withTables Spec.RsaPss.verifyPrecomputedTableSig [("hash", tsH), ("mgf1", tsG)]

/-- What the code needs of `verifyPrecomputedTableContract.pre`, by name, for
the tables `tsH` of `MdHash` and `tsG` of `Hash`. -/
structure PreV (tsH tsG : List FnTable) (K : Nat) (s : State) : Prop where
  sp1 : stk K ≤ s.sp.toNat
  sp2 : s.sp.toNat + 64 ≤ 2 ^ 64
  tabH : ∃ T ∈ tsH, Abi.tableHeld 64 s.mem (stackArg s 6) (FnTable.words isa s T)
  tabG : ∃ T ∈ tsG, Abi.tableHeld 64 s.mem (stackArg s 7) (FnTable.words isa s T)
  hsy : ((tsH.map (·.fns)).flatten ++ (tsG.map (·.fns)).flatten).Pairwise fun f g => f ≠ g → s.syms f ≠ s.syms g
  hrd : Covers [nR s, eR s, dgR s, sgR s, pR s, tHR s, tGR s, aR s] s.rd
  hws : sR s ∈ s.wr
  hwr : s.wr = [sR s]
  ns : (nR s).Disjoint (sR s)
  es : (eR s).Disjoint (sR s)
  dgs : (dgR s).Disjoint (sR s)
  sgs : (sgR s).Disjoint (sR s)
  sP : (sR s).Disjoint (pR s)
  stH : (sR s).Disjoint (tHR s)
  stG : (sR s).Disjoint (tGR s)
  sa : (sR s).Disjoint (aR s)
  kn : (kR K s).Disjoint (nR s)
  ke : (kR K s).Disjoint (eR s)
  kdg : (kR K s).Disjoint (dgR s)
  ksg : (kR K s).Disjoint (sgR s)
  ks : (kR K s).Disjoint (sR s)
  kP : (kR K s).Disjoint (pR s)
  ktH : (kR K s).Disjoint (tHR s)
  ktG : (kR K s).Disjoint (tGR s)
  ka : (kR K s).Disjoint (aR s)
  wn : (s.gpr .x0).toNat + (s.gpr .x1).toNat ≤ 2 ^ 64
  we : (s.gpr .x2).toNat + (s.gpr .x3).toNat ≤ 2 ^ 64
  wdg : (s.gpr .x4).toNat + (s.gpr .x5).toNat ≤ 2 ^ 64
  wsg : (s.gpr .x6).toNat + (s.gpr .x7).toNat ≤ 2 ^ 64
  ws : (stackArg s 2).toNat + (stackArg s 3).toNat * 8 ≤ 2 ^ 64
  wP : (stackArg s 4).toNat + (stackArg s 5).toNat * 8 ≤ 2 ^ 64
  wtH : (stackArg s 6).toNat + 88 ≤ 2 ^ 64
  wtG : (stackArg s 7).toNat + 40 ≤ 2 ^ 64
  k1 : 64 ≤ (s.gpr .x1).toNat
  k2 : (s.gpr .x1).toNat ≤ 1024
  e1 : 1 ≤ (s.gpr .x3).toNat
  e2 : (s.gpr .x3).toNat ≤ (s.gpr .x1).toNat
  sgl : (s.gpr .x7).toNat = (s.gpr .x1).toNat
  hs : 8 * (((s.gpr .x1).toNat + 7) / 8) + 48 + 1024 ≤ (stackArg s 3).toNat
  hl : (stackArg s 5).toNat = Spec.Rsa.precomputedWords (s.gpr .x1).toNat
  hdl : Spec.RsaPss.digestLenOk 64 s.mem (stackArg s 6) (s.gpr .x5)

theorem kb_toNat {tsH tsG : List FnTable} {K : Nat} {s : State} (hp : PreV tsH tsG K s) :
    (kb K s).toNat + stk K = s.sp.toNat ∧ s.sp.toNat + 64 ≤ 2 ^ 64 := by
  have := hp.sp1; have := hp.sp2
  simp only [kb, BitVec.toNat_sub, BitVec.toNat_ofNat]
  constructor <;> omega

theorem fb_toNat {tsH tsG : List FnTable} {K : Nat} {s : State} (hp : PreV tsH tsG K s) :
    (fb s).toNat + frameBytes = s.sp.toNat := by
  have := hp.sp1
  simp only [fb, BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold stk at this; omega

/-- The stack arguments are readable. -/
theorem arg_in {tsH tsG : List FnTable} {K : Nat} {s : State} (hp : PreV tsH tsG K s) {rs : List Region}
    (hrd : Covers s.rd rs) {j : Nat} (hj : j < 8) : InRegions rs (stackArgAddr s j) 8 :=
  hrd _ _ <| hp.hrd _ _ ⟨aR s, by simp, by
    rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by omega) (by omega)⟩

/-- A stack argument, in memory changed only in the frame. -/
theorem arg_frame {tsH tsG : List FnTable} {K : Nat} {s : State} (hp : PreV tsH tsG K s) {m : Mem}
    (h : Frame [⟨fb s, frameBytes⟩] s.mem m) {j : Nat} (hj : j < 8) : m.readW (stackArgAddr s j) 64 = stackArg s j :=
  h.readW (r := aR s) (by rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by omega) (by omega))
    (keep_of_frame hp.ka) (by decide)

theorem preV_of {tsH tsG : List FnTable} {K : Nat} {s : State}
    (h : (Spec.RsaPss.verifyPrecomputedTableContract (verifyAbi tsH tsG) (stk K)).pre s) : PreV tsH tsG K s := by
  have e : stk K = (frameBytes + K - 1) + 1 := by unfold stk frameBytes; omega
  rw [e] at h
  sig_pre [Spec.RsaPss.verifyPrecomputedTableContract, Spec.RsaPss.verifyPrecomputedTableSig,
    Spec.MdHashTable.param, Spec.HashTable.param,
    Spec.MdHashTable.wordCount, Spec.HashTable.wordCount, Spec.MdHashTable.fns, Spec.HashTable.fns,
    Spec.MdHashTable.dataWords, Spec.HashTable.dataWords, Abi.withTables, Sig.wordIndex, abi, argRegs,
    List.append_eq, _root_.List.range, _root_.List.range.loop] at h
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ, List.getD_cons_zero,
    Option.some.injEq, exists_eq_left'] at h
  sig_split h
  rename_i sp1 sp2 tabH tabG hsy hrd hwr ns es dgs sgs sP stH stG sa kn ke kdg ksg ks kP ktH ktG ka wn we wdg
    wsg ws wP wtH wtG _ob1 e1 e2 sgl hs hl
  obtain ⟨k1, k2⟩ := _ob1
  rw [← e] at sp1 kn ke kdg ksg ks kP ktH ktG ka
  exact ⟨sp1, sp2, tabH, tabG, hsy, by rw [hrd]; exact Covers.refl _, by rw [hwr]; simp, hwr, ns, es, dgs, sgs, sP,
    stH, stG, sa, kn, ke, kdg, ksg, ks, kP, ktH, ktG, ka, wn, we, wdg, wsg, ws, wP, wtH, wtG, k1, k2, e1, e2, sgl,
    by unfold Spec.RsaPss.publicScratchWords Spec.Rsa.publicScratchWords Spec.Rsa.modulusWords at hs; omega, hl, h⟩

end VG.Proof.RsaPss.AArch64.Vfy
