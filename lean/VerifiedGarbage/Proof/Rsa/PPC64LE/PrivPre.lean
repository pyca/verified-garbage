module

public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Impl.Rsa.PPC64LE.Priv
public import VerifiedGarbage.TCB.PPC64LE.Target

/-!
# `vg_rsa_private_checked` on PPC64LE: the precondition

`PreP s`: the shared contract's precondition (`privateCheckedContract`, with
the stack of the frame, `frameBytes`), by name (`preP_of`).
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.Priv

open VG VG.PPC64LE VG.Impl.Rsa.PPC64LE.Priv

theorem stackArgs_twelve (s : State) :
    List.map (stackArg s) (List.range 12) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9, stackArg s 10,
      stackArg s 11] := rfl

/-! ## The buffers -/

abbrev oR (s : State) : Region := ⟨s.gpr .r3, (s.gpr .r4).toNat⟩
abbrev nR (s : State) : Region := ⟨s.gpr .r5, (s.gpr .r6).toNat⟩
abbrev eR (s : State) : Region := ⟨s.gpr .r7, (s.gpr .r8).toNat⟩
abbrev iR (s : State) : Region := ⟨s.gpr .r9, (s.gpr .r10).toNat⟩
abbrev pR (s : State) : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩
abbrev qR (s : State) : Region := ⟨stackArg s 2, (stackArg s 3).toNat⟩
abbrev dpR (s : State) : Region := ⟨stackArg s 4, (stackArg s 5).toNat⟩
abbrev dqR (s : State) : Region := ⟨stackArg s 6, (stackArg s 7).toNat⟩
abbrev qiR (s : State) : Region := ⟨stackArg s 8, (stackArg s 9).toNat⟩
abbrev sR (s : State) : Region := ⟨stackArg s 10, (stackArg s 11).toNat * 8⟩
abbrev aR (s : State) : Region := ⟨stackArgAddr s 0, 96⟩

/-- The frame's base: the stack pointer in the frame. -/
abbrev fb (s : State) : Addr := s.sp - BitVec.ofNat 64 frameBytes

/-- The stack the function uses: the frame. -/
abbrev kR (s : State) : Region := ⟨fb s, frameBytes⟩

/-- What the code needs of `privateCheckedContract.pre`, by name. -/
structure PreP (s : State) : Prop where
  sp1 : frameBytes ≤ s.sp.toNat
  sp2 : s.sp.toNat + 192 ≤ 2 ^ 64
  hrd : s.rd = [nR s, eR s, iR s, pR s, qR s, dpR s, dqR s, qiR s, aR s]
  hwr : s.wr = [oR s, sR s]
  on : (oR s).Disjoint (nR s)
  oe : (oR s).Disjoint (eR s)
  oi : (oR s).Disjoint (iR s)
  op : (oR s).Disjoint (pR s)
  oq : (oR s).Disjoint (qR s)
  odp : (oR s).Disjoint (dpR s)
  odq : (oR s).Disjoint (dqR s)
  oqi : (oR s).Disjoint (qiR s)
  os : (oR s).Disjoint (sR s)
  oa : (oR s).Disjoint (aR s)
  ns : (nR s).Disjoint (sR s)
  es : (eR s).Disjoint (sR s)
  is : (iR s).Disjoint (sR s)
  ps : (pR s).Disjoint (sR s)
  qs : (qR s).Disjoint (sR s)
  dps : (dpR s).Disjoint (sR s)
  dqs : (dqR s).Disjoint (sR s)
  qis : (qiR s).Disjoint (sR s)
  sa : (sR s).Disjoint (aR s)
  ko : (kR s).Disjoint (oR s)
  kn : (kR s).Disjoint (nR s)
  ke : (kR s).Disjoint (eR s)
  ki : (kR s).Disjoint (iR s)
  kp : (kR s).Disjoint (pR s)
  kq : (kR s).Disjoint (qR s)
  kdp : (kR s).Disjoint (dpR s)
  kdq : (kR s).Disjoint (dqR s)
  kqi : (kR s).Disjoint (qiR s)
  ks : (kR s).Disjoint (sR s)
  ka : (kR s).Disjoint (aR s)
  wo : (s.gpr .r3).toNat + (s.gpr .r4).toNat ≤ 2 ^ 64
  wn : (s.gpr .r5).toNat + (s.gpr .r6).toNat ≤ 2 ^ 64
  we : (s.gpr .r7).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64
  wi : (s.gpr .r9).toNat + (s.gpr .r10).toNat ≤ 2 ^ 64
  wp : (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64
  wq : (stackArg s 2).toNat + (stackArg s 3).toNat ≤ 2 ^ 64
  wdp : (stackArg s 4).toNat + (stackArg s 5).toNat ≤ 2 ^ 64
  wdq : (stackArg s 6).toNat + (stackArg s 7).toNat ≤ 2 ^ 64
  wqi : (stackArg s 8).toNat + (stackArg s 9).toNat ≤ 2 ^ 64
  ws : (stackArg s 10).toNat + (stackArg s 11).toNat * 8 ≤ 2 ^ 64
  k1 : 64 ≤ (s.gpr .r6).toNat
  k2 : (s.gpr .r6).toNat ≤ 1024
  h4 : (s.gpr .r4).toNat = (s.gpr .r6).toNat
  h10 : (s.gpr .r10).toNat = (s.gpr .r6).toNat
  e1 : 1 ≤ (s.gpr .r8).toNat
  e2 : (s.gpr .r8).toNat ≤ (s.gpr .r6).toNat
  p1 : 1 ≤ (stackArg s 1).toNat
  p2 : (stackArg s 1).toNat < (s.gpr .r6).toNat
  q1 : 1 ≤ (stackArg s 3).toNat
  q2 : (stackArg s 3).toNat < (s.gpr .r6).toNat
  h5 : (stackArg s 5).toNat = (stackArg s 1).toNat
  h9 : (stackArg s 9).toNat = (stackArg s 1).toNat
  h7 : (stackArg s 7).toNat = (stackArg s 3).toNat
  hs : Spec.Rsa.scratchWords (s.gpr .r6).toNat ≤ (stackArg s 11).toNat

theorem preP_of {s : State} (h : (Spec.Rsa.privateCheckedContract abi frameBytes).pre s) : PreP s := by
  have e : frameBytes = 3327 + 1 := rfl
  rw [e] at h
  sig_pre [Spec.Rsa.privateCheckedContract, Spec.Rsa.privateCheckedSig, abi, argRegs,
    stackArgs_twelve, List.append_eq] at h
  simp only [Sig.pairFacts, List.filterMap_cons, List.filterMap_nil, Bool.cond_true, Bool.cond_false,
    Bool.true_or, Bool.false_or, List.cons_append, List.nil_append, Sig.conj, List.append_nil] at h
  obtain ⟨sp1, sp2, hrd, hwr, on, oe, ⟨oi, op, oq, odp, odq, oqi, os, oa, ns, es, is, ps, qs, dps, dqs, qis, sa⟩,
    ko, kn, ke, ki, kp, kq, kdp, kdq, kqi, ks, ka, wo, wn, we, wi, wp, wq, wdp, wdq, wqi, ws, ⟨k1, k2⟩, h4, h10,
    e1, e2, p1, p2, q1, q2, h5, h9, h7, hs⟩ := h
  exact ⟨sp1, by omega, hrd, hwr, on, oe, oi, op, oq, odp, odq, oqi, os, oa, ns, es, is, ps, qs, dps, dqs, qis, sa,
    ko, kn, ke, ki, kp, kq, kdp, kdq, kqi, ks, ka, wo, wn, we, wi, wp, wq, wdp, wdq, wqi, ws, k1, k2, h4, h10, e1,
    e2, p1, p2, q1, q2, h5, h9, h7, hs⟩

end VG.Proof.Rsa.PPC64LE.Priv
