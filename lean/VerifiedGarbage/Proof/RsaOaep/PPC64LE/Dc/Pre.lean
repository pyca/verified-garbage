module

public import VerifiedGarbage.Spec.RsaOaep.Contract
public import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Base
public import VerifiedGarbage.Impl.RsaOaep.PPC64LE.Decrypt
import VerifiedGarbage.Proof.Framework.Offset

/-!
# RSAES-OAEP decryption on PPC64LE: the precondition

Untrusted: everything here is checked by Lean. `PreD s`: the shared
contract's precondition (`Spec.RsaOaep.decryptContract`, with the stack of
the frames and of `vg_rsa_private_checked`, `stackBytes`), by name
(`preD_of`); the working space `Sd s` and the values the decoding keeps in
`r15`–`r23` (`vD s rc`, with the private operation's result `rc` in `r20`),
both functions of the entry state `s` alone, as `Base` takes them; and
`Fits` for any state with `s`'s stack pointer and regions.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE.Dec

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE VG.Impl.RsaOaep.PPC64LE.Dec

theorem stackArgs_fifteen (s : State) :
    List.map (stackArg s) (List.range 15) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9, stackArg s 10,
      stackArg s 11, stackArg s 12, stackArg s 13, stackArg s 14] := rfl

/-- The stack the function uses: its frame (`frameBytes`), the private
operation's (`privBytes`) and that function's own. -/
def stackBytes : Nat := frameBytes + privBytes + Impl.Rsa.PPC64LE.Priv.frameBytes

theorem stackBytes_eq : stackBytes = 3776 := rfl

/-! ## The buffers -/

abbrev oR (s : State) : Region := ⟨s.gpr .r3, (s.gpr .r4).toNat⟩
abbrev mlR (s : State) : Region := ⟨s.gpr .r5, 8⟩
abbrev nR (s : State) : Region := ⟨s.gpr .r6, (s.gpr .r7).toNat⟩
abbrev eR (s : State) : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
abbrev pR (s : State) : Region := ⟨s.gpr .r10, (stackArg s 0).toNat⟩
abbrev qR (s : State) : Region := ⟨stackArg s 1, (stackArg s 2).toNat⟩
abbrev dpR (s : State) : Region := ⟨stackArg s 3, (stackArg s 4).toNat⟩
abbrev dqR (s : State) : Region := ⟨stackArg s 5, (stackArg s 6).toNat⟩
abbrev qiR (s : State) : Region := ⟨stackArg s 7, (stackArg s 8).toNat⟩
abbrev lR (s : State) : Region := ⟨stackArg s 9, (stackArg s 10).toNat⟩
abbrev ctR (s : State) : Region := ⟨stackArg s 11, (stackArg s 12).toNat⟩
abbrev scR (s : State) : Region := ⟨stackArg s 13, (stackArg s 14).toNat * 8⟩
abbrev aR (s : State) : Region := ⟨stackArgAddr s 0, 120⟩
/-- The stack the function uses. -/
abbrev kD (s : State) : Region := ⟨s.sp - BitVec.ofNat 64 stackBytes, stackBytes⟩

/-- What the code needs of `decryptContract.pre`, by name. -/
structure PreD (s : State) : Prop where
  sp1 : stackBytes ≤ s.sp.toNat
  sp2 : s.sp.toNat + 216 ≤ 2 ^ 64
  hrd : s.rd = [nR s, eR s, pR s, qR s, dpR s, dqR s, qiR s, lR s, ctR s, aR s]
  hwr : s.wr = [oR s, mlR s, scR s]
  oml : (oR s).Disjoint (mlR s)
  on : (oR s).Disjoint (nR s)
  oe : (oR s).Disjoint (eR s)
  op : (oR s).Disjoint (pR s)
  oq : (oR s).Disjoint (qR s)
  odp : (oR s).Disjoint (dpR s)
  odq : (oR s).Disjoint (dqR s)
  oqi : (oR s).Disjoint (qiR s)
  ol : (oR s).Disjoint (lR s)
  oct : (oR s).Disjoint (ctR s)
  os : (oR s).Disjoint (scR s)
  oa : (oR s).Disjoint (aR s)
  mln : (mlR s).Disjoint (nR s)
  mle : (mlR s).Disjoint (eR s)
  mlp : (mlR s).Disjoint (pR s)
  mlq : (mlR s).Disjoint (qR s)
  mldp : (mlR s).Disjoint (dpR s)
  mldq : (mlR s).Disjoint (dqR s)
  mlqi : (mlR s).Disjoint (qiR s)
  mll : (mlR s).Disjoint (lR s)
  mlct : (mlR s).Disjoint (ctR s)
  mls : (mlR s).Disjoint (scR s)
  mla : (mlR s).Disjoint (aR s)
  ns : (nR s).Disjoint (scR s)
  es : (eR s).Disjoint (scR s)
  ps : (pR s).Disjoint (scR s)
  qs : (qR s).Disjoint (scR s)
  dps : (dpR s).Disjoint (scR s)
  dqs : (dqR s).Disjoint (scR s)
  qis : (qiR s).Disjoint (scR s)
  ls : (lR s).Disjoint (scR s)
  cts : (ctR s).Disjoint (scR s)
  sa : (scR s).Disjoint (aR s)
  ko : (kD s).Disjoint (oR s)
  kml : (kD s).Disjoint (mlR s)
  kn : (kD s).Disjoint (nR s)
  ke : (kD s).Disjoint (eR s)
  kp : (kD s).Disjoint (pR s)
  kq : (kD s).Disjoint (qR s)
  kdp : (kD s).Disjoint (dpR s)
  kdq : (kD s).Disjoint (dqR s)
  kqi : (kD s).Disjoint (qiR s)
  kl : (kD s).Disjoint (lR s)
  kct : (kD s).Disjoint (ctR s)
  ks : (kD s).Disjoint (scR s)
  ka : (kD s).Disjoint (aR s)
  wo : (s.gpr .r3).toNat + (s.gpr .r4).toNat ≤ 2 ^ 64
  wml : (s.gpr .r5).toNat + 8 ≤ 2 ^ 64
  wn : (s.gpr .r6).toNat + (s.gpr .r7).toNat ≤ 2 ^ 64
  we : (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64
  wp : (s.gpr .r10).toNat + (stackArg s 0).toNat ≤ 2 ^ 64
  wq : (stackArg s 1).toNat + (stackArg s 2).toNat ≤ 2 ^ 64
  wdp : (stackArg s 3).toNat + (stackArg s 4).toNat ≤ 2 ^ 64
  wdq : (stackArg s 5).toNat + (stackArg s 6).toNat ≤ 2 ^ 64
  wqi : (stackArg s 7).toNat + (stackArg s 8).toNat ≤ 2 ^ 64
  wl : (stackArg s 9).toNat + (stackArg s 10).toNat ≤ 2 ^ 64
  wct : (stackArg s 11).toNat + (stackArg s 12).toNat ≤ 2 ^ 64
  wsc : (stackArg s 13).toNat + (stackArg s 14).toNat * 8 ≤ 2 ^ 64
  k1 : 64 ≤ (s.gpr .r7).toNat
  k2 : (s.gpr .r7).toNat ≤ 1024
  ok : (s.gpr .r4).toNat = (s.gpr .r7).toNat
  oc : (stackArg s 12).toNat = (s.gpr .r7).toNat
  e1 : 1 ≤ (s.gpr .r9).toNat
  e2 : (s.gpr .r9).toNat ≤ (s.gpr .r7).toNat
  p1 : 1 ≤ (stackArg s 0).toNat
  p2 : (stackArg s 0).toNat < (s.gpr .r7).toNat
  q1 : 1 ≤ (stackArg s 2).toNat
  q2 : (stackArg s 2).toNat < (s.gpr .r7).toNat
  h4 : (stackArg s 4).toNat = (stackArg s 0).toNat
  h8 : (stackArg s 8).toNat = (stackArg s 0).toNat
  h6 : (stackArg s 6).toNat = (stackArg s 2).toNat
  hs : Spec.RsaPss.scratchWords (s.gpr .r7).toNat ≤ (stackArg s 14).toNat

theorem preD_of {H G : Spec.Mgf1.Hash} {s : State}
    (h : (Spec.RsaOaep.decryptContract H G abi stackBytes).pre s) : PreD s := by
  have e : stackBytes = 3775 + 1 := rfl
  rw [e] at h
  sig_pre [Spec.RsaOaep.decryptContract, Spec.RsaOaep.decryptSig, abi, argRegs,
    stackArgs_fifteen, List.append_eq] at h
  simp only [Sig.pairFacts, List.filterMap_cons, List.filterMap_nil, Bool.cond_true, Bool.cond_false,
    Bool.true_or, Bool.false_or, List.cons_append, List.nil_append, Sig.conj, List.append_nil] at h
  obtain ⟨sp1, sp2, hrd, hwr, oml, on, ⟨oe, op, oq, odp, odq, oqi, ol, oct, os, oa, mln, mle, mlp, mlq, mldp, mldq,
    mlqi, mll, mlct, mls, mla, ns, es, ps, qs, dps, dqs, qis, ls, cts, sa⟩, ko, kml, kn, ke, kp, kq, kdp, kdq, kqi,
    kl, kct, ks, ka, wo, wml, wn, we, wp, wq, wdp, wdq, wqi, wl, wct, wsc, ⟨k1, k2⟩, ok, oc, e1, e2, p1, p2, q1, q2,
    h4, h8, h6, hs⟩ := h
  exact ⟨sp1, by omega, hrd, hwr, oml, on, oe, op, oq, odp, odq, oqi, ol, oct, os, oa, mln, mle, mlp, mlq, mldp, mldq,
    mlqi, mll, mlct, mls, mla, ns, es, ps, qs, dps, dqs, qis, ls, cts, sa, ko, kml, kn, ke, kp, kq, kdp, kdq, kqi, kl,
    kct, ks, ka, wo, wml, wn, we, wp, wq, wdp, wdq, wqi, wl, wct, wsc, k1, k2, ok, oc, e1, e2, p1, p2, q1, q2, h4, h8,
    h6, hs⟩

/-! ## The working space and the registers the decoding keeps -/

/-- The working space. -/
abbrev Sd (s : State) : Addr := stackArg s 13

/-- `k`. -/
abbrev kk (s : State) : Nat := (s.gpr .r7).toNat

/-- The values `Base` fixes in `r15`–`r23` once the private operation has
returned `rc`: `k`, `out`, `msg_len`, the label and its length, `rc`, and
our caller's `r21`–`r23`. -/
def vD (s : State) (rc : Nat) : Reg → BitVec 64
  | .r15 => s.gpr .r7
  | .r16 => s.gpr .r3
  | .r17 => s.gpr .r5
  | .r18 => stackArg s 9
  | .r19 => stackArg s 10
  | .r20 => BitVec.ofNat 64 rc
  | .r21 => s.gpr .r21
  | .r22 => s.gpr .r22
  | .r23 => s.gpr .r23
  | _ => 0

/-- The working space and `vD`, as `Base` takes them: of the entry state `s`,
whatever the state. -/
abbrev SD (s : State) : State → Addr := fun _ => Sd s
abbrev VD (s : State) (rc : Nat) : State → Reg → BitVec 64 := fun _ => vD s rc

section
variable {s : State} (P : PreD s)
include P

theorem scLen : oRsa ≤ (stackArg s 14).toNat * 8 := by
  have := P.hs; unfold Spec.RsaPss.scratchWords Spec.Rsa.scratchWords at this; unfold oRsa; omega

theorem sc_sub : Region.Sub (SC (SD s) s) (scR s) := Region.sub_prefix (scLen P)

omit P in
theorem kR_sub : Region.Sub (kR s) (kD s) := below_sub (by rw [stackBytes_eq]; decide) (by rw [stackBytes_eq]; decide)

/-- `Fits` for any state with the entry's stack pointer and regions. -/
theorem fits {s' : State} (hsp : s'.sp = s.sp) (hwr : s'.wr = s.wr) : Fits (SD s) s' where
  sp1 := by rw [hsp]; have := P.sp1; rw [stackBytes_eq] at this; omega
  sc := ⟨scR s, by rw [hwr, P.hwr]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)),
    rfl, scLen P⟩
  ksc := by
    have e : kR s' = kR s := by simp only [kR, hsp]
    rw [e]; exact (P.ks.sub_left kR_sub).sub_right (sc_sub P)
  wS := by show (stackArg s 13).toNat + oRsa ≤ 2 ^ 64; have := P.wsc; have := scLen P; omega

end

section
variable {s s' t : State} {rc : Nat} (h : Base (SD s) (VD s rc) s' t)
include h

theorem Base.r14 : t.gpr .r14 = Sd s := h.r14
theorem Base.r15 : t.gpr .r15 = s.gpr .r7 := h.vs .r15 (by decide)
theorem Base.r16 : t.gpr .r16 = s.gpr .r3 := h.vs .r16 (by decide)
theorem Base.r17 : t.gpr .r17 = s.gpr .r5 := h.vs .r17 (by decide)
theorem Base.r18 : t.gpr .r18 = stackArg s 9 := h.vs .r18 (by decide)
theorem Base.r19 : t.gpr .r19 = stackArg s 10 := h.vs .r19 (by decide)
theorem Base.r20 : t.gpr .r20 = BitVec.ofNat 64 rc := h.vs .r20 (by decide)

end

end VG.Proof.RsaOaep.PPC64LE.Dec
