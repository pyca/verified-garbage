module

public import VerifiedGarbage.Spec.RsaOaep.Precomputed
public import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Frame
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Mem

/-!
# RSAES-OAEP encryption on PPC64LE: the precondition

Untrusted: everything here is checked by Lean. `PreO Hs s`: the shared
contract's precondition (`Spec.RsaOaep.encryptPrecomputedContract`, with the
stack of the frame and of the streaming hash functions, 304 bytes), by name
(`preO_of`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE

open VG VG.PPC64LE

theorem stackArgs_seven (s : State) :
    List.map (stackArg s) (List.range 7) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6] := rfl

/-- The buffers: `out`, `n`, `e`, the label, the message, the seed, the
working space, the precomputed values and the arguments on the stack. -/
abbrev oR (s : State) : Region := ⟨s.gpr .r3, (s.gpr .r4).toNat⟩
abbrev nR (s : State) : Region := ⟨s.gpr .r5, (s.gpr .r6).toNat⟩
abbrev eR (s : State) : Region := ⟨s.gpr .r7, (s.gpr .r8).toNat⟩
abbrev lR (s : State) : Region := ⟨s.gpr .r9, (s.gpr .r10).toNat⟩
abbrev mR (s : State) : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩
abbrev sdR (D : Nat) (s : State) : Region := ⟨stackArg s 2, D⟩
abbrev scR (s : State) : Region := ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩
abbrev pR (s : State) : Region := ⟨stackArg s 5, (stackArg s 6).toNat * 8⟩
abbrev aR (s : State) : Region := ⟨stackArgAddr s 0, 56⟩

/-- What the code needs of `encryptPrecomputedContract.pre`, by name, for a
hash function of `D`-byte digests. -/
structure PreO (D : Nat) (s : State) : Prop where
  sp1 : 304 ≤ s.sp.toNat
  sp2 : s.sp.toNat + 152 ≤ 2 ^ 64
  hrd : s.rd = [nR s, eR s, lR s, mR s, sdR D s, pR s, aR s]
  hwr : s.wr = [oR s, scR s]
  on : (oR s).Disjoint (nR s)
  oe : (oR s).Disjoint (eR s)
  ol : (oR s).Disjoint (lR s)
  om : (oR s).Disjoint (mR s)
  osd : (oR s).Disjoint (sdR D s)
  osc : (oR s).Disjoint (scR s)
  op : (oR s).Disjoint (pR s)
  oa : (oR s).Disjoint (aR s)
  ns : (nR s).Disjoint (scR s)
  es : (eR s).Disjoint (scR s)
  ls : (lR s).Disjoint (scR s)
  ms : (mR s).Disjoint (scR s)
  sds : (sdR D s).Disjoint (scR s)
  sp : (scR s).Disjoint (pR s)
  sa : (scR s).Disjoint (aR s)
  ko : (kR s).Disjoint (oR s)
  kn : (kR s).Disjoint (nR s)
  ke : (kR s).Disjoint (eR s)
  kl : (kR s).Disjoint (lR s)
  km : (kR s).Disjoint (mR s)
  ksd : (kR s).Disjoint (sdR D s)
  ksc : (kR s).Disjoint (scR s)
  kp : (kR s).Disjoint (pR s)
  ka : (kR s).Disjoint (aR s)
  wo : (s.gpr .r3).toNat + (s.gpr .r4).toNat ≤ 2 ^ 64
  wn : (s.gpr .r5).toNat + (s.gpr .r6).toNat ≤ 2 ^ 64
  we : (s.gpr .r7).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64
  wl : (s.gpr .r9).toNat + (s.gpr .r10).toNat ≤ 2 ^ 64
  wm : (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64
  wsd : (stackArg s 2).toNat + D ≤ 2 ^ 64
  wsc : (stackArg s 3).toNat + (stackArg s 4).toNat * 8 ≤ 2 ^ 64
  wp : (stackArg s 5).toNat + (stackArg s 6).toNat * 8 ≤ 2 ^ 64
  k1 : 64 ≤ (s.gpr .r6).toNat
  k2 : (s.gpr .r6).toNat ≤ 1024
  ok : (s.gpr .r4).toNat = (s.gpr .r6).toNat
  e1 : 1 ≤ (s.gpr .r8).toNat
  e2 : (s.gpr .r8).toNat ≤ (s.gpr .r6).toNat
  hs : Spec.RsaPss.publicScratchWords (s.gpr .r6).toNat ≤ (stackArg s 4).toNat
  hp : (stackArg s 6).toNat = Spec.Rsa.precomputedWords (s.gpr .r6).toNat

theorem preO_of {H G : Spec.Mgf1.Hash} {s : State}
    (h : (Spec.RsaOaep.encryptPrecomputedContract H G abi 304).pre s) : PreO H.len s := by
  have e : (304 : Nat) = 303 + 1 := rfl
  rw [e] at h
  sig_pre [Spec.RsaOaep.encryptPrecomputedContract, Spec.RsaOaep.encryptPrecomputedSig, abi, argRegs,
    stackArgs_seven, List.append_eq] at h
  simp only [Sig.pairFacts, List.filterMap_cons, List.filterMap_nil, Bool.cond_true, Bool.cond_false,
    Bool.true_or, Bool.false_or, List.cons_append, List.nil_append, Sig.conj, List.append_nil] at h
  obtain ⟨sp1, sp2, hrd, hwr, on, oe, ⟨ol, om, osd, osc, op, oa, ns, es, ls, ms, sds, sp, sa⟩, ko, kn, ke, kl, km,
    ksd, ksc, kp, ka, wo, wn, we, wl, wm, wsd, wsc, wp, ⟨k1, k2⟩, ok, e1, e2, hs, hp⟩ := h
  exact ⟨sp1, by omega, hrd, hwr, on, oe, ol, om, osd, osc, op, oa, ns, es, ls, ms, sds, sp, sa, ko, kn, ke, kl, km,
    ksd, ksc, kp, ka, wo, wn, we, wl, wm, wsd, wsc, wp, k1, k2, ok, e1, e2, hs, hp⟩

end VG.Proof.RsaOaep.PPC64LE
