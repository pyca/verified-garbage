module

public import VerifiedGarbage.Spec.RsaOaep.Contract
public import VerifiedGarbage.Spec.RsaOaep.MdTables
public import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Base
public import VerifiedGarbage.Impl.RsaOaep.PPC64LE.Decrypt
import VerifiedGarbage.Proof.Framework.Offset

/-!
# RSAES-OAEP decryption on PPC64LE: the precondition

Untrusted: everything here is checked by Lean. `PreD s`: the contract's
precondition (`Spec.RsaOaep.decryptMdTablesContract`, with the stack of the
frames and of `vg_rsa_private_checked`, `stackBytes`), by name (`preD_of`),
and what it says of the tables (`spec_tabD`); the working space `Sd s` and the values the decoding keeps in
`r15`–`r23` (`vD s rc`, with the private operation's result `rc` in `r20`),
both functions of the entry state `s` alone, as `Base` takes them; and
`Fits` for any state with `s`'s stack pointer and regions.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE.Dec

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE VG.Impl.RsaOaep.PPC64LE.Dec

theorem stackArgs_seventeen (s : State) :
    List.map (stackArg s) (List.range 17) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9, stackArg s 10,
      stackArg s 11, stackArg s 12, stackArg s 13, stackArg s 14, stackArg s 15, stackArg s 16] := rfl

/-- The stack the function uses: its frame (`frameBytes`), the private
operation's (`privBytes`) and that function's own. -/
def stackBytes : Nat := frameBytes + privBytes + Impl.Rsa.PPC64LE.Priv.frameBytes

theorem stackBytes_eq : stackBytes = 3792 := rfl

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
abbrev tLR (s : State) : Region := Sig.tableRegion 64 (stackArg s 15) 11
abbrev tR (s : State) : Region := Sig.tableRegion 64 (stackArg s 16) 11
/-- Our stack arguments: seventeen, or with `pc` nineteen. -/
abbrev aR (pc : Bool) (s : State) : Region := ⟨stackArgAddr s 0, if pc then 152 else 136⟩
/-- With `pc`, the key's precomputed values, `pre_len` words. -/
abbrev preR (s : State) : Region := ⟨stackArg s 17, (stackArg s 18).toNat * 8⟩
/-- The stack the function uses. -/
abbrev kD (s : State) : Region := ⟨s.sp - BitVec.ofNat 64 stackBytes, stackBytes⟩

/-- The buffers the function reads. -/
abbrev rdL (pc : Bool) (s : State) : List Region :=
  [nR s, eR s, pR s, qR s, dpR s, dqR s, qiR s, lR s, ctR s] ++ (if pc then [preR s] else []) ++
    [tLR s, tR s, aR pc s]

/-- What the code needs of `decryptMdTablesContract.pre`, or with `pc` of
`decryptPrecomputedMdTablesContract.pre`, by name. -/
structure PreD (pc : Bool) (s : State) : Prop where
  sp1 : stackBytes ≤ s.sp.toNat
  sp2 : s.sp.toNat + (if pc then 240 else 224) ≤ 2 ^ 64
  hrd : s.rd = rdL pc s
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
  otl : (oR s).Disjoint (tLR s)
  ot : (oR s).Disjoint (tR s)
  oa : (oR s).Disjoint (aR pc s)
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
  mltl : (mlR s).Disjoint (tLR s)
  mlt : (mlR s).Disjoint (tR s)
  mla : (mlR s).Disjoint (aR pc s)
  ns : (nR s).Disjoint (scR s)
  es : (eR s).Disjoint (scR s)
  ps : (pR s).Disjoint (scR s)
  qs : (qR s).Disjoint (scR s)
  dps : (dpR s).Disjoint (scR s)
  dqs : (dqR s).Disjoint (scR s)
  qis : (qiR s).Disjoint (scR s)
  ls : (lR s).Disjoint (scR s)
  cts : (ctR s).Disjoint (scR s)
  stl : (scR s).Disjoint (tLR s)
  st : (scR s).Disjoint (tR s)
  sa : (scR s).Disjoint (aR pc s)
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
  ktl : (kD s).Disjoint (tLR s)
  kt : (kD s).Disjoint (tR s)
  ka : (kD s).Disjoint (aR pc s)
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
  wtl : (stackArg s 15).toNat + 88 ≤ 2 ^ 64
  wt : (stackArg s 16).toNat + 88 ≤ 2 ^ 64
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

/-- The contract, with both hash functions each one of the tables `ts`, and
the stack of the frames and of `vg_rsa_private_checked`. -/
abbrev decSpec (ts : List FnTable) : Contract isa :=
  Spec.RsaOaep.decryptMdTablesContract (abi.withTables Spec.RsaOaep.decryptMdTablesSig [("hash", ts), ("mgf1", ts)])
    stackBytes

/-- Unfolds the precondition at `h`. -/
macro "dec_pre" " at " h:ident : tactic => `(tactic| (
  have e : stackBytes = 3791 + 1 := rfl
  unfold decSpec at $h:ident
  rw [e] at $h:ident
  sig_pre [Spec.RsaOaep.decryptMdTablesContract, Spec.RsaOaep.decryptMdTablesSig, Spec.RsaOaep.decryptSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Abi.withTables, Sig.wordIndex, abi, argRegs,
    stackArgs_seventeen, List.append_eq, List.range, List.range.loop] at $h:ident
  sig_pre [Spec.RsaOaep.decryptMdTablesContract, Spec.RsaOaep.decryptMdTablesSig, Spec.RsaOaep.decryptSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Abi.withTables, Sig.wordIndex, abi, argRegs,
    stackArgs_seventeen, List.append_eq, List.range, List.range.loop] at $h:ident
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left', Sig.pairFacts, List.filterMap_cons, List.filterMap_nil,
    Bool.cond_true, Bool.cond_false, Bool.true_or, Bool.false_or, List.cons_append, List.nil_append, Sig.conj,
    List.append_nil] at $h:ident))

/-- With `pc`, `pre` holds the key's precomputed values. -/
abbrev HypS (s : State) : Prop :=
  Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .r6) (s.gpr .r7).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .r10) (stackArg s 0).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 1) (stackArg s 2).toNat) =
    some (Spec.Rsa.wordsAt s.mem (stackArg s 17) (stackArg s 18).toNat)

/-- What `vg_rsa_oaep_decrypt_precomputed`'s precondition adds: `pre`'s facts. -/
structure PreXD (s : State) : Prop where
  oP : (oR s).Disjoint (preR s)
  mlP : (mlR s).Disjoint (preR s)
  sP : (scR s).Disjoint (preR s)
  kP : (kD s).Disjoint (preR s)
  wP : (stackArg s 17).toNat + (stackArg s 18).toNat * 8 ≤ 2 ^ 64
  pl : (stackArg s 18).toNat =
    Spec.Rsa.privatePrecomputedWords (s.gpr .r7).toNat (stackArg s 0).toNat (stackArg s 2).toNat
  hyp : HypS s

theorem preD_of {ts : List FnTable} {s : State} (h : (decSpec ts).pre s) : PreD false s := by
  dec_pre at h
  obtain ⟨sp1, sp2, -, -, -, hrd, hwr, oml, on, oe, op, oq, odp, odq, oqi, ol, oct, os, otl, ot, oa, mln, mle, mlp,
    mlq, mldp, mldq, mlqi, mll, mlct, mls, mltl, mlt, mla, ns, es, ps, qs, dps, dqs, qis, ls, cts, stl, st, sa, ko,
    kml, kn, ke, kp, kq, kdp, kdq, kqi, kl, kct, ks, ktl, kt, ka, wo, wml, wn, we, wp, wq, wdp, wdq, wqi, wl, wct, wsc,
    wtl, wt, ⟨k1, k2⟩, ok, oc, e1, e2, p1, p2, q1, q2, h4, h8, h6, hs⟩ := h
  exact ⟨sp1, by simp only [Bool.false_eq_true, ↓reduceIte]; omega_using [sp2], hrd, hwr, oml, on, oe, op, oq, odp, odq, oqi, ol, oct, os, otl, ot, oa, mln, mle, mlp, mlq,
    mldp, mldq, mlqi, mll, mlct, mls, mltl, mlt, mla, ns, es, ps, qs, dps, dqs, qis, ls, cts, stl, st, sa, ko, kml, kn,
    ke, kp, kq, kdp, kdq, kqi, kl, kct, ks, ktl, kt, ka, wo, wml, wn, we, wp, wq, wdp, wdq, wqi, wl, wct, wsc, wtl, wt,
    k1, k2, ok, oc, e1, e2, p1, p2, q1, q2, h4, h8, h6, hs⟩

/-- The tables, as the contract gives them: each one of `ts`, the label's
hash function's at the stack argument 15 and MGF1's at 16, with the
functions of distinct names at distinct addresses. -/
theorem spec_tabD {ts : List FnTable} {s : State} (h : (decSpec ts).pre s) :
    (∃ T ∈ ts, Abi.tableHeld 64 s.mem (stackArg s 15) (FnTable.words isa s T)) ∧
      (∃ T ∈ ts, Abi.tableHeld 64 s.mem (stackArg s 16) (FnTable.words isa s T)) ∧
      ((ts.map (fun T : FnTable => T.fns)).flatten ++ (ts.map (fun T : FnTable => T.fns)).flatten).Pairwise
        (fun f g => f ≠ g → s.syms f ≠ s.syms g) := by
  dec_pre at h
  exact ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩

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
variable {pc : Bool} {s : State} (P : PreD pc s)
include P

theorem scLen : oRsa ≤ (stackArg s 14).toNat * 8 := by
  have := P.hs; unfold Spec.RsaPss.scratchWords Spec.Rsa.scratchWords at this; unfold oRsa; omega_using [this]

theorem sc_sub : Region.Sub (SC (SD s) s) (scR s) := Region.sub_prefix (scLen P)

omit P in
theorem kR_sub : Region.Sub (kR s) (kD s) := below_sub (by rw [stackBytes_eq]; decide) (by rw [stackBytes_eq]; decide)

/-- `Fits` for any state with the entry's stack pointer and regions. -/
theorem fits {s' : State} (hsp : s'.sp = s.sp) (hwr : s'.wr = s.wr) : Fits (SD s) s' where
  sp1 := by rw [hsp]; have := P.sp1; rw [stackBytes_eq] at this; omega_using [this]
  sc := ⟨scR s, by rw [hwr, P.hwr]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)),
    rfl, scLen P⟩
  ksc := by
    have e : kR s' = kR s := by simp only [kR, hsp]
    rw [e]; exact (P.ks.sub_left kR_sub).sub_right (sc_sub P)
  wS := by show (stackArg s 13).toNat + oRsa ≤ 2 ^ 64; have := P.wsc; have := scLen P; omega_arith

end

section
variable {s s' t : State} {rc : Nat} (h : Base (SD s) (VD s rc) s' t)
include h

theorem Base.r15 : t.gpr .r15 = s.gpr .r7 := h.vs .r15 (by decide)
theorem Base.r16 : t.gpr .r16 = s.gpr .r3 := h.vs .r16 (by decide)
theorem Base.r17 : t.gpr .r17 = s.gpr .r5 := h.vs .r17 (by decide)
theorem Base.r18 : t.gpr .r18 = stackArg s 9 := h.vs .r18 (by decide)
theorem Base.r19 : t.gpr .r19 = stackArg s 10 := h.vs .r19 (by decide)
theorem Base.r20 : t.gpr .r20 = BitVec.ofNat 64 rc := h.vs .r20 (by decide)

end

end VG.Proof.RsaOaep.PPC64LE.Dec
