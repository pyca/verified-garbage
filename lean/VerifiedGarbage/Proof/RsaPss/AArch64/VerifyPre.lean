module

public import VerifiedGarbage.Spec.RsaPss.AnyHash
import VerifiedGarbage.Proof.RsaPss.AArch64.VerifyLogic
public import VerifiedGarbage.Proof.RsaPss.AArch64.SignPre
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.PrecomputedCorrect
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import Mathlib.Tactic.SplitIfs

/-!
# RSASSA-PSS verification on AArch64: the precondition

`PreV D K s`: the shared contract's precondition (`verifyAnyContract`, with
the stack `stk K` of the frame and a callee using `K` bytes), by name, for a
digest of `D` bytes, the length of the values of the hash function `hash`
names (`preV_of`). The frame is that of signing
(`Sgn.fb`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64.Vfy

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Proof.RsaPss.AArch64.Sgn (stk kR fb kb frame_sub0 stackArgAddr_eq keep_of_frame)

/-- The buffers: `n`, `e`, the digest, the signature, the working space, the
precomputed values, the arguments on the stack. -/
abbrev nR (s : State) : Region := ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
abbrev eR (s : State) : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
abbrev dgR (D : Nat) (s : State) : Region := ⟨s.gpr .x4, D⟩
abbrev sgR (s : State) : Region := ⟨s.gpr .x6, (s.gpr .x7).toNat⟩
abbrev sR (s : State) : Region := ⟨stackArg s 2, (stackArg s 3).toNat * 8⟩
abbrev pR (s : State) : Region := ⟨stackArg s 4, (stackArg s 5).toNat * 8⟩
abbrev aR (s : State) : Region := ⟨stackArgAddr s 0, 64⟩

theorem stackArgs_eight (s : State) :
    List.map (stackArg s) (List.range 8) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7] := rfl

/-- What the code needs of `verifyPrecomputedContract.pre`, by name. -/
structure PreV (D K : Nat) (s : State) : Prop where
  sp1 : stk K ≤ s.sp.toNat
  sp2 : s.sp.toNat + 64 ≤ 2 ^ 64
  hrd : Covers [nR s, eR s, dgR D s, sgR s, pR s, aR s] s.rd
  hws : sR s ∈ s.wr
  hwr : s.wr = [sR s]
  ns : (nR s).Disjoint (sR s)
  es : (eR s).Disjoint (sR s)
  dgs : (dgR D s).Disjoint (sR s)
  sgs : (sgR s).Disjoint (sR s)
  sP : (sR s).Disjoint (pR s)
  sa : (sR s).Disjoint (aR s)
  kn : (kR K s).Disjoint (nR s)
  ke : (kR K s).Disjoint (eR s)
  kdg : (kR K s).Disjoint (dgR D s)
  ksg : (kR K s).Disjoint (sgR s)
  ks : (kR K s).Disjoint (sR s)
  kP : (kR K s).Disjoint (pR s)
  ka : (kR K s).Disjoint (aR s)
  wn : (s.gpr .x0).toNat + (s.gpr .x1).toNat ≤ 2 ^ 64
  we : (s.gpr .x2).toNat + (s.gpr .x3).toNat ≤ 2 ^ 64
  wdg : (s.gpr .x4).toNat + D ≤ 2 ^ 64
  wsg : (s.gpr .x6).toNat + (s.gpr .x7).toNat ≤ 2 ^ 64
  ws : (stackArg s 2).toNat + (stackArg s 3).toNat * 8 ≤ 2 ^ 64
  wP : (stackArg s 4).toNat + (stackArg s 5).toNat * 8 ≤ 2 ^ 64
  k1 : 64 ≤ (s.gpr .x1).toNat
  k2 : (s.gpr .x1).toNat ≤ 1024
  e1 : 1 ≤ (s.gpr .x3).toNat
  e2 : (s.gpr .x3).toNat ≤ (s.gpr .x1).toNat
  sgl : (s.gpr .x7).toNat = (s.gpr .x1).toNat
  hs : 8 * (((s.gpr .x1).toNat + 7) / 8) + 48 + 1024 ≤ (stackArg s 3).toNat
  hl : (stackArg s 5).toNat = Spec.Rsa.precomputedWords (s.gpr .x1).toNat
  dl : (s.gpr .x5).toNat = D
  hh : (stackArg s 6).toNat < 8
  hg : (stackArg s 7).toNat < 8

theorem preV_of {Hs : Spec.Mgf1.Hash} {K : Nat} {s : State}
    (h : (Spec.RsaPss.verifyAnyContract abi (stk K)).pre s) (hk : Spec.HashId.mgf1 (stackArg s 6).toNat = some Hs) :
    PreV Hs.len K s := by
  have e : stk K = (frameBytes + K - 1) + 1 := by unfold stk frameBytes; omega
  rw [e] at h
  sig_pre [Spec.RsaPss.verifyAnyContract, Spec.RsaPss.verifyAnySig, abi, argRegs, stackArgs_eight,
    List.append_eq] at h
  sig_pre [Spec.RsaPss.verifyAnyContract, Spec.RsaPss.verifyAnySig, abi, argRegs, stackArgs_eight,
    List.append_eq] at h
  obtain ⟨sp1, sp2, hrd, hwr, ns, es, dgs, sgs, sP, sa, kn, ke, kdg, ksg, ks, kP, ka, wn, we, wdg, wsg, ws, wP,
    hh, hg, hdl, ⟨k1, k2⟩, e1, e2, sgl, hs, hl⟩ := h
  have dl := hdl Hs hk
  rw [dl] at dgs kdg wdg hrd
  rw [← e] at sp1 kn ke kdg ksg ks kP ka
  simp only [Spec.RsaPss.hashIds, List.mem_cons, List.not_mem_nil, or_false] at hh hg
  exact ⟨sp1, sp2, by rw [hrd]; exact Covers.refl _, by rw [hwr]; simp, hwr, ns, es, dgs, sgs, sP, sa, kn, ke,
    kdg, ksg, ks, kP, ka, wn, we, wdg, wsg, ws, wP, k1, k2, e1, e2, sgl,
    by unfold Spec.RsaPss.publicScratchWords Spec.Rsa.publicScratchWords Spec.Rsa.modulusWords at hs; omega, hl,
    dl, by omega, by omega⟩

/-- The hash functions' numbers, from `verifyAnyContract.pre`. -/
theorem sel_of {K : Nat} {s : State} (h : (Spec.RsaPss.verifyAnyContract abi (stk K)).pre s) :
    (stackArg s 6).toNat < 8 ∧ (stackArg s 7).toNat < 8 := by
  have e : stk K = (frameBytes + K - 1) + 1 := by unfold stk frameBytes; omega
  rw [e] at h
  sig_pre [Spec.RsaPss.verifyAnyContract, Spec.RsaPss.verifyAnySig, abi, argRegs, stackArgs_eight,
    List.append_eq] at h
  sig_pre [Spec.RsaPss.verifyAnyContract, Spec.RsaPss.verifyAnySig, abi, argRegs, stackArgs_eight,
    List.append_eq] at h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hh, hg, -⟩ := h
  simp only [Spec.RsaPss.hashIds, List.mem_cons, List.not_mem_nil, or_false] at hh hg
  omega

theorem kb_toNat {D K : Nat} {s : State} (hp : PreV D K s) :
    (kb K s).toNat + stk K = s.sp.toNat ∧ s.sp.toNat + 64 ≤ 2 ^ 64 := by
  have := hp.sp1; have := hp.sp2
  simp only [kb, BitVec.toNat_sub, BitVec.toNat_ofNat]
  constructor <;> omega

theorem fb_toNat {D K : Nat} {s : State} (hp : PreV D K s) : (fb s).toNat + frameBytes = s.sp.toNat := by
  have := hp.sp1
  simp only [fb, BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold stk at this; omega

/-- The stack arguments are readable. -/
theorem arg_in {D K : Nat} {s : State} (hp : PreV D K s) {rs : List Region} (hrd : Covers s.rd rs) {j : Nat}
    (hj : j < 8) : InRegions rs (stackArgAddr s j) 8 :=
  hrd _ _ <| hp.hrd _ _ ⟨aR s, by simp, by
    rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by omega) (by omega)⟩

/-- A stack argument, in memory changed only in the frame. -/
theorem arg_frame {D K : Nat} {s : State} (hp : PreV D K s) {m : Mem} (h : Frame [⟨fb s, frameBytes⟩] s.mem m)
    {j : Nat} (hj : j < 8) : m.readW (stackArgAddr s j) 64 = stackArg s j :=
  h.readW (r := aR s) (by rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by omega) (by omega))
    (keep_of_frame hp.ka) (by decide)

end VG.Proof.RsaPss.AArch64.Vfy
