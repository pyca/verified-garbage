module

public import VerifiedGarbage.Spec.RsaPkcs1Sig.Precomputed
import VerifiedGarbage.Impl.RsaPkcs1Sig.PPC64LE.Precomputed
import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Frame
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Impl.RsaPkcs1Sig.PPC64LE.Frame
public import VerifiedGarbage.TCB.Mem

/-!
# `vg_rsa_pkcs1_verify_precomputed` on PPC64LE: the precondition

Untrusted: everything here is checked by Lean. `PreV s`: the shared
contract's precondition (`verifyPrecomputedContract`, with the stack of the
frame, `frameBytes`), by name (`preV_of`). As on AArch64
(`Proof/RsaPkcs1Sig/AArch64/VerifyPre.lean`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.PPC64LE.Ver

open VG VG.PPC64LE VG.Impl.RsaPkcs1Sig.PPC64LE

theorem stackArgs_five (s : State) :
    List.map (stackArg s) (List.range 5) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4] := rfl

/-- The buffers: `n`, `e`, the hash value, the signature and the
precomputed values (the working space, the arguments on the stack and the
stack the function uses are `sR`, `aR` and `kR`). -/
abbrev nR (s : State) : Region := ⟨s.gpr .r3, (s.gpr .r4).toNat⟩
abbrev eR (s : State) : Region := ⟨s.gpr .r5, (s.gpr .r6).toNat⟩
abbrev dR (s : State) : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
abbrev gR (s : State) : Region := ⟨s.gpr .r10, (stackArg s 0).toNat⟩
abbrev pR (s : State) : Region := ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩

/-- What the code needs of `verifyPrecomputedContract.pre`, by name: the
buffers are readable or writable, apart from each other where one is written
and from the stack the function uses, and do not wrap around; the lengths
are within bounds. -/
structure PreV (s : State) : Prop where
  sp1 : frameBytes ≤ s.sp.toNat
  sp2 : s.sp.toNat + 136 ≤ 2 ^ 64
  hrd : s.rd = [nR s, eR s, dR s, gR s, pR s, aR s]
  hwr : s.wr = [sR s]
  ns : (nR s).Disjoint (sR s)
  es : (eR s).Disjoint (sR s)
  ds : (dR s).Disjoint (sR s)
  gs : (gR s).Disjoint (sR s)
  sp : (sR s).Disjoint (pR s)
  sa : (sR s).Disjoint (aR s)
  kn : (kR s).Disjoint (nR s)
  ke : (kR s).Disjoint (eR s)
  kd : (kR s).Disjoint (dR s)
  kg : (kR s).Disjoint (gR s)
  ks : (kR s).Disjoint (sR s)
  kp : (kR s).Disjoint (pR s)
  ka : (kR s).Disjoint (aR s)
  wn : (s.gpr .r3).toNat + (s.gpr .r4).toNat ≤ 2 ^ 64
  we : (s.gpr .r5).toNat + (s.gpr .r6).toNat ≤ 2 ^ 64
  wd : (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64
  wg : (s.gpr .r10).toNat + (stackArg s 0).toNat ≤ 2 ^ 64
  ws : (stackArg s 1).toNat + (stackArg s 2).toNat * 8 ≤ 2 ^ 64
  wp : (stackArg s 3).toNat + (stackArg s 4).toNat * 8 ≤ 2 ^ 64
  k1 : 64 ≤ (s.gpr .r4).toNat
  k2 : (s.gpr .r4).toNat ≤ 1024
  e1 : 1 ≤ (s.gpr .r6).toNat
  e2 : (s.gpr .r6).toNat ≤ (s.gpr .r4).toNat
  hs : Spec.Rsa.publicScratchWords (s.gpr .r4).toNat ≤ (stackArg s 2).toNat
  hp : (stackArg s 4).toNat = Spec.Rsa.precomputedWords (s.gpr .r4).toNat

theorem preV_of {s : State} (h : (Spec.RsaPkcs1Sig.verifyPrecomputedContract abi frameBytes).pre s) : PreV s := by
  have e : frameBytes = 2223 + 1 := rfl
  rw [e] at h
  sig_pre [Spec.RsaPkcs1Sig.verifyPrecomputedContract, Spec.RsaPkcs1Sig.verifyPrecomputedSig, abi, argRegs,
    stackArgs_five, List.append_eq] at h
  simp only [Sig.pairFacts, List.filterMap_cons, List.filterMap_nil, Bool.cond_true, Bool.cond_false,
    Bool.true_or, Bool.false_or, List.cons_append, List.nil_append, Sig.conj, List.append_nil] at h
  obtain ⟨sp1, sp2, hrd, hwr, ⟨ns, es, ds, gs, sp, sa⟩, kn, ke, kd, kg, ks, kp, ka, wn, we, wd, wg, ws, wp, ⟨k1, k2⟩,
    e1, e2, hs, hp⟩ := h
  exact ⟨sp1, by omega, hrd, hwr, ns, es, ds, gs, sp, sa, kn, ke, kd, kg, ks, kp, ka, wn, we, wd, wg, ws, wp, k1, k2,
    e1, e2, hs, hp⟩

end VG.Proof.RsaPkcs1Sig.PPC64LE.Ver
