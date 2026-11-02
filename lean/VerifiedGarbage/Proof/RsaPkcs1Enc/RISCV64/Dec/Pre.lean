module

public import VerifiedGarbage.Spec.RsaPkcs1Enc.Contract
public import VerifiedGarbage.Impl.RsaPkcs1Enc.RISCV64.Decrypt
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# `vg_rsa_pkcs1_decrypt` on RISC-V: the precondition

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaPkcs1Enc/PPC64LE/DecPre.lean`): `DPre s`, the shared contract's
precondition (`decryptContract`, with the stack of the frame and of
`vg_rsa_private_checked`'s, `stackBytes`), by name (`dPre_of`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.RISCV64.Dec

open VG VG.RISCV64

/-- The stack the function uses: its frame and `vg_rsa_private_checked`'s. -/
def stackBytes : Nat := Impl.RsaPkcs1Enc.RISCV64.Decrypt.frameBytes + Impl.Rsa.RISCV64.Priv.frameBytes

theorem stackArgs_fifteen (s : State) :
    List.map (stackArg s) (List.range 15) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9, stackArg s 10,
      stackArg s 11, stackArg s 12, stackArg s 13, stackArg s 14] := rfl

/-! ## The buffers -/

abbrev oR (s : State) : Region := ⟨s.gpr .a0, (s.gpr .a1).toNat⟩
abbrev mlR (s : State) : Region := ⟨s.gpr .a2, 8⟩
abbrev nR (s : State) : Region := ⟨s.gpr .a3, (s.gpr .a4).toNat⟩
abbrev eR (s : State) : Region := ⟨s.gpr .a5, (s.gpr .a6).toNat⟩
abbrev dR (s : State) : Region := ⟨s.gpr .a7, (stackArg s 0).toNat⟩
abbrev iR (s : State) : Region := ⟨stackArg s 1, (stackArg s 2).toNat⟩
abbrev pR (s : State) : Region := ⟨stackArg s 3, (stackArg s 4).toNat⟩
abbrev qR (s : State) : Region := ⟨stackArg s 5, (stackArg s 6).toNat⟩
abbrev dpR (s : State) : Region := ⟨stackArg s 7, (stackArg s 8).toNat⟩
abbrev dqR (s : State) : Region := ⟨stackArg s 9, (stackArg s 10).toNat⟩
abbrev qiR (s : State) : Region := ⟨stackArg s 11, (stackArg s 12).toNat⟩
abbrev sR (s : State) : Region := ⟨stackArg s 13, (stackArg s 14).toNat * 8⟩
abbrev aR (s : State) : Region := ⟨stackArgAddr s 0, 120⟩

/-- The base of the frame. -/
abbrev fb (s : State) : Addr := s.sp - BitVec.ofNat 64 Impl.RsaPkcs1Enc.RISCV64.Decrypt.frameBytes

/-- The stack the function and its callees use. -/
abbrev kR (s : State) : Region := ⟨s.sp - BitVec.ofNat 64 stackBytes, stackBytes⟩

/-- The precondition, by name. -/
structure DPre (s : State) : Prop where
  sp16 : s.sp.toNat % 16 = 0
  sp1 : stackBytes ≤ s.sp.toNat
  sp2 : s.sp.toNat + 120 ≤ 2 ^ 64
  hrd : s.rd = [nR s, eR s, dR s, iR s, pR s, qR s, dpR s, dqR s, qiR s, aR s]
  hwr : s.wr = [oR s, mlR s, sR s]
  om : (oR s).Disjoint (mlR s)
  on : (oR s).Disjoint (nR s)
  oe : (oR s).Disjoint (eR s)
  od : (oR s).Disjoint (dR s)
  oi : (oR s).Disjoint (iR s)
  op : (oR s).Disjoint (pR s)
  oq : (oR s).Disjoint (qR s)
  odp : (oR s).Disjoint (dpR s)
  odq : (oR s).Disjoint (dqR s)
  oqi : (oR s).Disjoint (qiR s)
  os : (oR s).Disjoint (sR s)
  oa : (oR s).Disjoint (aR s)
  mn : (mlR s).Disjoint (nR s)
  me : (mlR s).Disjoint (eR s)
  md : (mlR s).Disjoint (dR s)
  mi : (mlR s).Disjoint (iR s)
  mp : (mlR s).Disjoint (pR s)
  mq : (mlR s).Disjoint (qR s)
  mdp : (mlR s).Disjoint (dpR s)
  mdq : (mlR s).Disjoint (dqR s)
  mqi : (mlR s).Disjoint (qiR s)
  ms : (mlR s).Disjoint (sR s)
  ma : (mlR s).Disjoint (aR s)
  ns : (nR s).Disjoint (sR s)
  es : (eR s).Disjoint (sR s)
  ds : (dR s).Disjoint (sR s)
  is : (iR s).Disjoint (sR s)
  ps : (pR s).Disjoint (sR s)
  qs : (qR s).Disjoint (sR s)
  dps : (dpR s).Disjoint (sR s)
  dqs : (dqR s).Disjoint (sR s)
  qis : (qiR s).Disjoint (sR s)
  sa : (sR s).Disjoint (aR s)
  ko : (kR s).Disjoint (oR s)
  km : (kR s).Disjoint (mlR s)
  kn : (kR s).Disjoint (nR s)
  ke : (kR s).Disjoint (eR s)
  kd : (kR s).Disjoint (dR s)
  ki : (kR s).Disjoint (iR s)
  kp : (kR s).Disjoint (pR s)
  kq : (kR s).Disjoint (qR s)
  kdp : (kR s).Disjoint (dpR s)
  kdq : (kR s).Disjoint (dqR s)
  kqi : (kR s).Disjoint (qiR s)
  ks : (kR s).Disjoint (sR s)
  ka : (kR s).Disjoint (aR s)
  wo : (s.gpr .a0).toNat + (s.gpr .a1).toNat ≤ 2 ^ 64
  wm : (s.gpr .a2).toNat + 8 ≤ 2 ^ 64
  wn : (s.gpr .a3).toNat + (s.gpr .a4).toNat ≤ 2 ^ 64
  we : (s.gpr .a5).toNat + (s.gpr .a6).toNat ≤ 2 ^ 64
  wd : (s.gpr .a7).toNat + (stackArg s 0).toNat ≤ 2 ^ 64
  wi : (stackArg s 1).toNat + (stackArg s 2).toNat ≤ 2 ^ 64
  wp : (stackArg s 3).toNat + (stackArg s 4).toNat ≤ 2 ^ 64
  wq : (stackArg s 5).toNat + (stackArg s 6).toNat ≤ 2 ^ 64
  wdp : (stackArg s 7).toNat + (stackArg s 8).toNat ≤ 2 ^ 64
  wdq : (stackArg s 9).toNat + (stackArg s 10).toNat ≤ 2 ^ 64
  wqi : (stackArg s 11).toNat + (stackArg s 12).toNat ≤ 2 ^ 64
  ws : (stackArg s 13).toNat + (stackArg s 14).toNat * 8 ≤ 2 ^ 64
  k1 : 64 ≤ (s.gpr .a4).toNat
  k2 : (s.gpr .a4).toNat ≤ 1024
  h1 : (s.gpr .a1).toNat = (s.gpr .a4).toNat
  hi : (stackArg s 2).toNat = (s.gpr .a4).toNat
  e1 : 1 ≤ (s.gpr .a6).toNat
  e2 : (s.gpr .a6).toNat ≤ (s.gpr .a4).toNat
  d1 : 1 ≤ (stackArg s 0).toNat
  d2 : (stackArg s 0).toNat ≤ (s.gpr .a4).toNat
  p1 : 1 ≤ (stackArg s 4).toNat
  p2 : (stackArg s 4).toNat < (s.gpr .a4).toNat
  q1 : 1 ≤ (stackArg s 6).toNat
  q2 : (stackArg s 6).toNat < (s.gpr .a4).toNat
  h8 : (stackArg s 8).toNat = (stackArg s 4).toNat
  h12 : (stackArg s 12).toNat = (stackArg s 4).toNat
  h10 : (stackArg s 10).toNat = (stackArg s 6).toNat
  hs : Spec.Rsa.scratchWords (s.gpr .a4).toNat ≤ (stackArg s 14).toNat
  mal : (s.gpr .a2).toNat % 8 = 0
  al : (stackArg s 13).toNat % 8 = 0

theorem dPre_of {s : State} (h : (Spec.RsaPkcs1Enc.decryptContract RISCV64.abi stackBytes).pre s) : DPre s := by
  have e : stackBytes = 3439 + 1 := rfl
  rw [e] at h
  sig_pre [Spec.RsaPkcs1Enc.decryptContract, Spec.RsaPkcs1Enc.decryptSig, RISCV64.abi, RISCV64.argRegs,
    stackArgs_fifteen, List.append_eq, List.range, List.range.loop] at h
  obtain ⟨sp16, sp1, sp2, hrd, hwr, om, on, oe, od, oi, op, oq, odp, odq, oqi, os, oa, mn, me, md, mi, mp, mq, mdp,
    mdq, mqi, ms, ma, ns, es, ds, is, ps, qs, dps, dqs, qis, sa, ko, km, kn, ke, kd, ki, kp, kq, kdp, kdq, kqi, ks,
    ka, wo, wm, wn, we, wd, wi, wp, wq, wdp, wdq, wqi, ws, ⟨k1, k2⟩, h1, hi, e1, e2, d1, d2, p1, p2, q1, q2, h8, h12,
    h10, hs, mal, al⟩ := h
  exact ⟨sp16, sp1, sp2, hrd, hwr, om, on, oe, od, oi, op, oq, odp, odq, oqi, os, oa, mn, me, md, mi, mp, mq, mdp,
    mdq, mqi, ms, ma, ns, es, ds, is, ps, qs, dps, dqs, qis, sa, ko, km, kn, ke, kd, ki, kp, kq, kdp, kdq, kqi, ks,
    ka, wo, wm, wn, we, wd, wi, wp, wq, wdp, wdq, wqi, ws, k1, k2, h1, hi, e1, e2, d1, d2, p1, p2, q1, q2, h8, h12,
    h10, hs, mal, al⟩

end VG.Proof.RsaPkcs1Enc.RISCV64.Dec
