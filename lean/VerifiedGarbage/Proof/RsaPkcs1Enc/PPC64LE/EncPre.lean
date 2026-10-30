module

public import VerifiedGarbage.Spec.RsaPkcs1Enc.Precomputed
import VerifiedGarbage.Impl.RsaPkcs1Enc.PPC64LE.Precomputed
public import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Frame
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Impl.RsaPkcs1Sig.PPC64LE.Frame

/-!
# `vg_rsa_pkcs1_encrypt_precomputed` on PPC64LE: the precondition

Untrusted: everything here is checked by Lean. `PreE s`: the shared
contract's precondition (`encryptPrecomputedContract`, with the stack of the
frame, `frameBytes`), by name (`preE_of`). As
`vg_rsa_pkcs1_verify_precomputed`'s (`Proof/RsaPkcs1Sig/PPC64LE/VerifyPre.lean`),
whose frame it shares.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.PPC64LE.Enc

open VG VG.PPC64LE VG.Impl.RsaPkcs1Sig.PPC64LE VG.Proof.RsaPkcs1Sig.PPC64LE

theorem stackArgs_six (s : State) :
    List.map (stackArg s) (List.range 6) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5] := rfl

/-- The buffers: `out`, `n`, `e`, the message, `PS`, the working space, the
precomputed values and the arguments on the stack (the stack the function
uses is `kR`). -/
abbrev oR (s : State) : Region := ⟨s.gpr .r3, (s.gpr .r4).toNat⟩
abbrev nR (s : State) : Region := ⟨s.gpr .r5, (s.gpr .r6).toNat⟩
abbrev eR (s : State) : Region := ⟨s.gpr .r7, (s.gpr .r8).toNat⟩
abbrev mR (s : State) : Region := ⟨s.gpr .r9, (s.gpr .r10).toNat⟩
abbrev psR (s : State) : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩
abbrev scR (s : State) : Region := ⟨stackArg s 2, (stackArg s 3).toNat * 8⟩
abbrev pR (s : State) : Region := ⟨stackArg s 4, (stackArg s 5).toNat * 8⟩
abbrev a6R (s : State) : Region := ⟨stackArgAddr s 0, 48⟩

/-- What the code needs of `encryptPrecomputedContract.pre`, by name. -/
structure PreE (s : State) : Prop where
  sp1 : frameBytes ≤ s.sp.toNat
  sp2 : s.sp.toNat + 144 ≤ 2 ^ 64
  hrd : s.rd = [nR s, eR s, mR s, psR s, pR s, a6R s]
  hwr : s.wr = [oR s, scR s]
  on : (oR s).Disjoint (nR s)
  oe : (oR s).Disjoint (eR s)
  om : (oR s).Disjoint (mR s)
  ops : (oR s).Disjoint (psR s)
  osc : (oR s).Disjoint (scR s)
  op : (oR s).Disjoint (pR s)
  oa : (oR s).Disjoint (a6R s)
  ns : (nR s).Disjoint (scR s)
  es : (eR s).Disjoint (scR s)
  ms : (mR s).Disjoint (scR s)
  pss : (psR s).Disjoint (scR s)
  sp : (scR s).Disjoint (pR s)
  sa : (scR s).Disjoint (a6R s)
  ko : (kR s).Disjoint (oR s)
  kn : (kR s).Disjoint (nR s)
  ke : (kR s).Disjoint (eR s)
  km : (kR s).Disjoint (mR s)
  kps : (kR s).Disjoint (psR s)
  ksc : (kR s).Disjoint (scR s)
  kp : (kR s).Disjoint (pR s)
  ka : (kR s).Disjoint (a6R s)
  wo : (s.gpr .r3).toNat + (s.gpr .r4).toNat ≤ 2 ^ 64
  wn : (s.gpr .r5).toNat + (s.gpr .r6).toNat ≤ 2 ^ 64
  we : (s.gpr .r7).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64
  wm : (s.gpr .r9).toNat + (s.gpr .r10).toNat ≤ 2 ^ 64
  wps : (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64
  wsc : (stackArg s 2).toNat + (stackArg s 3).toNat * 8 ≤ 2 ^ 64
  wp : (stackArg s 4).toNat + (stackArg s 5).toNat * 8 ≤ 2 ^ 64
  k1 : 64 ≤ (s.gpr .r6).toNat
  k2 : (s.gpr .r6).toNat ≤ 1024
  ok : (s.gpr .r4).toNat = (s.gpr .r6).toNat
  e1 : 1 ≤ (s.gpr .r8).toNat
  e2 : (s.gpr .r8).toNat ≤ (s.gpr .r6).toNat
  ml : (s.gpr .r10).toNat + 11 ≤ (s.gpr .r6).toNat
  pl : (stackArg s 1).toNat = (s.gpr .r6).toNat - (s.gpr .r10).toNat - 3
  hs : Spec.Rsa.publicScratchWords (s.gpr .r6).toNat ≤ (stackArg s 3).toNat
  hp : (stackArg s 5).toNat = Spec.Rsa.precomputedWords (s.gpr .r6).toNat

theorem preE_of {s : State} (h : (Spec.RsaPkcs1Enc.encryptPrecomputedContract abi frameBytes).pre s) : PreE s := by
  have e : frameBytes = 2223 + 1 := rfl
  rw [e] at h
  sig_pre [Spec.RsaPkcs1Enc.encryptPrecomputedContract, Spec.RsaPkcs1Enc.encryptPrecomputedSig, abi, argRegs,
    stackArgs_six, List.append_eq, List.range, List.range.loop] at h
  obtain ⟨sp1, sp2, hrd, hwr, on, oe, om, ops, osc, op, oa, ns, es, ms, pss, sp, sa, ko, kn, ke, km, kps, ksc, kp,
    ka, wo, wn, we, wm, wps, wsc, wp, ⟨k1, k2⟩, ok, e1, e2, ml, pl, hs, hp⟩ := h
  exact ⟨sp1, by omega, hrd, hwr, on, oe, om, ops, osc, op, oa, ns, es, ms, pss, sp, sa, ko, kn, ke, km, kps, ksc,
    kp, ka, wo, wn, we, wm, wps, wsc, wp, k1, k2, ok, e1, e2, ml, pl, hs, hp⟩

end VG.Proof.RsaPkcs1Enc.PPC64LE.Enc
