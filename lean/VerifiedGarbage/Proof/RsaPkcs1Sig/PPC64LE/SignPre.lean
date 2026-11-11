module

public import VerifiedGarbage.Spec.RsaPkcs1Sig.Contract
public import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Impl.RsaPkcs1Sig.PPC64LE.Sign
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Framework.PowLit

/-!
# `vg_rsa_pkcs1_sign` on PPC64LE: the precondition

`SPre pc s`: the shared contract's precondition (`signContract`, or with
`pc` `signPrecomputedContract`, with the stack of the frame and of
`vg_rsa_private_checked`'s, `stackBytes`), by name (`sPre_of`); with `pc`,
what it says of `pre` (`PreX`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.PPC64LE.Sign

open VG VG.PPC64LE

/-- The stack the function uses: its frame and `vg_rsa_private_checked`'s
(or `vg_rsa_private_checked_precomputed`'s, the same). -/
def stackBytes : Nat := Impl.RsaPkcs1Sig.PPC64LE.Sign.frameBytes + Impl.Rsa.PPC64LE.Priv.frameBytes

theorem stackArgs_thirteen (s : State) :
    List.map (stackArg s) (List.range 13) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9, stackArg s 10,
      stackArg s 11, stackArg s 12] := rfl

/-! ## The buffers -/

abbrev oR (s : State) : Region := ⟨s.gpr .r3, (s.gpr .r4).toNat⟩
abbrev nR (s : State) : Region := ⟨s.gpr .r5, (s.gpr .r6).toNat⟩
abbrev eR (s : State) : Region := ⟨s.gpr .r7, (s.gpr .r8).toNat⟩
abbrev dR (s : State) : Region := ⟨s.gpr .r10, (stackArg s 0).toNat⟩
abbrev pR (s : State) : Region := ⟨stackArg s 1, (stackArg s 2).toNat⟩
abbrev qR (s : State) : Region := ⟨stackArg s 3, (stackArg s 4).toNat⟩
abbrev dpR (s : State) : Region := ⟨stackArg s 5, (stackArg s 6).toNat⟩
abbrev dqR (s : State) : Region := ⟨stackArg s 7, (stackArg s 8).toNat⟩
abbrev qiR (s : State) : Region := ⟨stackArg s 9, (stackArg s 10).toNat⟩
abbrev sR (s : State) : Region := ⟨stackArg s 11, (stackArg s 12).toNat * 8⟩
/-- Our stack arguments: thirteen, or with `pc` fifteen. -/
abbrev aR (pc : Bool) (s : State) : Region := ⟨stackArgAddr s 0, if pc then 120 else 104⟩
/-- With `pc`, the key's precomputed values, `pre_len` words. -/
abbrev preR (s : State) : Region := ⟨stackArg s 13, (stackArg s 14).toNat * 8⟩

/-- The buffers the function reads. -/
abbrev rdL (pc : Bool) (s : State) : List Region :=
  [nR s, eR s, dR s, pR s, qR s, dpR s, dqR s, qiR s] ++ (if pc then [preR s] else []) ++ [aR pc s]

/-- The base of the frame. -/
abbrev fb (s : State) : Addr := s.sp - BitVec.ofNat 64 Impl.RsaPkcs1Sig.PPC64LE.Sign.frameBytes

/-- The stack the function and its callee use. -/
abbrev kR (s : State) : Region := ⟨s.sp - BitVec.ofNat 64 stackBytes, stackBytes⟩

/-- The precondition, by name. -/
structure SPre (pc : Bool) (s : State) : Prop where
  sp1 : stackBytes ≤ s.sp.toNat
  sp2 : s.sp.toNat + (if pc then 216 else 200) ≤ 2 ^ 64
  hrd : s.rd = rdL pc s
  hwr : s.wr = [oR s, sR s]
  on : (oR s).Disjoint (nR s)
  oe : (oR s).Disjoint (eR s)
  od : (oR s).Disjoint (dR s)
  op : (oR s).Disjoint (pR s)
  oq : (oR s).Disjoint (qR s)
  odp : (oR s).Disjoint (dpR s)
  odq : (oR s).Disjoint (dqR s)
  oqi : (oR s).Disjoint (qiR s)
  os : (oR s).Disjoint (sR s)
  oa : (oR s).Disjoint (aR pc s)
  ns : (nR s).Disjoint (sR s)
  es : (eR s).Disjoint (sR s)
  ds : (dR s).Disjoint (sR s)
  ps : (pR s).Disjoint (sR s)
  qs : (qR s).Disjoint (sR s)
  dps : (dpR s).Disjoint (sR s)
  dqs : (dqR s).Disjoint (sR s)
  qis : (qiR s).Disjoint (sR s)
  sa : (sR s).Disjoint (aR pc s)
  ko : (kR s).Disjoint (oR s)
  kn : (kR s).Disjoint (nR s)
  ke : (kR s).Disjoint (eR s)
  kd : (kR s).Disjoint (dR s)
  kp : (kR s).Disjoint (pR s)
  kq : (kR s).Disjoint (qR s)
  kdp : (kR s).Disjoint (dpR s)
  kdq : (kR s).Disjoint (dqR s)
  kqi : (kR s).Disjoint (qiR s)
  ks : (kR s).Disjoint (sR s)
  ka : (kR s).Disjoint (aR pc s)
  wo : (s.gpr .r3).toNat + (s.gpr .r4).toNat ≤ 2 ^ 64
  wn : (s.gpr .r5).toNat + (s.gpr .r6).toNat ≤ 2 ^ 64
  we : (s.gpr .r7).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64
  wd : (s.gpr .r10).toNat + (stackArg s 0).toNat ≤ 2 ^ 64
  wp : (stackArg s 1).toNat + (stackArg s 2).toNat ≤ 2 ^ 64
  wq : (stackArg s 3).toNat + (stackArg s 4).toNat ≤ 2 ^ 64
  wdp : (stackArg s 5).toNat + (stackArg s 6).toNat ≤ 2 ^ 64
  wdq : (stackArg s 7).toNat + (stackArg s 8).toNat ≤ 2 ^ 64
  wqi : (stackArg s 9).toNat + (stackArg s 10).toNat ≤ 2 ^ 64
  ws : (stackArg s 11).toNat + (stackArg s 12).toNat * 8 ≤ 2 ^ 64
  k1 : 64 ≤ (s.gpr .r6).toNat
  k2 : (s.gpr .r6).toNat ≤ 1024
  h4 : (s.gpr .r4).toNat = (s.gpr .r6).toNat
  e1 : 1 ≤ (s.gpr .r8).toNat
  e2 : (s.gpr .r8).toNat ≤ (s.gpr .r6).toNat
  p1 : 1 ≤ (stackArg s 2).toNat
  p2 : (stackArg s 2).toNat < (s.gpr .r6).toNat
  q1 : 1 ≤ (stackArg s 4).toNat
  q2 : (stackArg s 4).toNat < (s.gpr .r6).toNat
  h6 : (stackArg s 6).toNat = (stackArg s 2).toNat
  h10 : (stackArg s 10).toNat = (stackArg s 2).toNat
  h8 : (stackArg s 8).toNat = (stackArg s 4).toNat
  hs : Spec.Rsa.scratchWords (s.gpr .r6).toNat ≤ (stackArg s 12).toNat

/-- With `pc`, `pre` holds the key's precomputed values. -/
abbrev HypS (pc : Bool) (s : State) : Prop :=
  pc = true → Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 1) (stackArg s 2).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 3) (stackArg s 4).toNat) =
    some (Spec.Rsa.wordsAt s.mem (stackArg s 13) (stackArg s 14).toNat)

/-- What `vg_rsa_pkcs1_sign_precomputed`'s precondition adds: `pre`'s facts. -/
structure PreX (s : State) : Prop where
  oP : (oR s).Disjoint (preR s)
  sP : (sR s).Disjoint (preR s)
  kP : (kR s).Disjoint (preR s)
  wP : (stackArg s 13).toNat + (stackArg s 14).toNat * 8 ≤ 2 ^ 64
  pl : (stackArg s 14).toNat =
    Spec.Rsa.privatePrecomputedWords (s.gpr .r6).toNat (stackArg s 2).toNat (stackArg s 4).toNat
  hyp : HypS true s

theorem sPre_of {s : State} (h : (Spec.RsaPkcs1Sig.signContract abi stackBytes).pre s) : SPre false s := by
  have e : stackBytes = 4607 + 1 := rfl
  rw [e] at h
  sig_pre [Spec.RsaPkcs1Sig.signContract, Spec.RsaPkcs1Sig.signSig, abi, argRegs,
    stackArgs_thirteen, List.append_eq, List.range, List.range.loop] at h
  obtain ⟨sp1, sp2, hrd, hwr, on, oe, od, op, oq, odp, odq, oqi, os, oa, ns, es, ds, ps, qs, dps, dqs, qis, sa,
    ko, kn, ke, kd, kp, kq, kdp, kdq, kqi, ks, ka, wo, wn, we, wd, wp, wq, wdp, wdq, wqi, ws, ⟨k1, k2⟩, h4,
    e1, e2, p1, p2, q1, q2, h6, h10, h8, hs⟩ := h
  exact ⟨sp1, by simp only [Bool.false_eq_true, ↓reduceIte]; omega, hrd, hwr, on, oe, od, op, oq, odp, odq, oqi, os, oa, ns, es, ds, ps, qs, dps, dqs, qis, sa,
    ko, kn, ke, kd, kp, kq, kdp, kdq, kqi, ks, ka, wo, wn, we, wd, wp, wq, wdp, wdq, wqi, ws, k1, k2, h4, e1, e2,
    p1, p2, q1, q2, h6, h10, h8, hs⟩

end VG.Proof.RsaPkcs1Sig.PPC64LE.Sign
