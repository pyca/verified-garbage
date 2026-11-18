module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.PrivCorrect
public import VerifiedGarbage.Proof.Rsa.PPC64LE.PrivPreCopy
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Rsa.PPC64LE.PrivPCT
public import VerifiedGarbage.Proof.Framework.PPC64LE.CallAny
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Entry
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Base
public import VerifiedGarbage.Spec.RsaOaep.Contract
public import VerifiedGarbage.Spec.RsaOaep.MdTables
public import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Impl.RsaOaep.PPC64LE.Decrypt

/-! ### `RsaOaep.PPC64LE.Dc.PrivArgs`, which this module and modules that import it used -/

section

/-! ### `RsaOaep.PPC64LE.Dc.Entry`, which this module and modules that import it used -/

section

/-! ### `RsaOaep.PPC64LE.Dc.Pre`, which this module and modules that import it used -/

section

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
  sig_split h
  rename_i sp1 sp2 _ _ _ hrd hwr oml on oe op oq odp odq oqi ol oct os otl ot oa mln mle mlp mlq mldp mldq mlqi
    mll mlct mls mltl mlt mla ns es ps qs dps dqs qis ls cts stl st sa ko kml kn ke kp kq kdp kdq kqi kl kct ks
    ktl kt ka wo wml wn we wp wq wdp wdq wqi wl wct wsc wtl wt h_k1_k2 ok oc e1 e2 p1 p2 q1 q2 h4 h8 h6
  have hs := h
  obtain ⟨k1, k2⟩ := h_k1_k2
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

end

end

/-!
# RSAES-OAEP decryption on PPC64LE: the entry

Untrusted: everything here is checked by Lean. `entry_ok`: from the state
after the frame's push, the saves and the prologue leave our caller's
registers and return address in their slots, `r14`–`r19` holding `scratch`,
`k`, `out`, `msg_len`, the label and its length, and `r6`–`r10` and `r12` the
entry's `n`, `n_len`, `e`, `e_len`, `p` and the frame's base (`Entered`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE.Dec

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE VG.Impl.RsaOaep.PPC64LE.Dec
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep wp_ld wp_mov wp_nil)

/-- The stack arguments are in `aR`. -/
theorem in_aR {pc : Bool} {s : State} {j : Nat} (hj : j < 17) : (aR pc s).Contains (stackArgAddr s j) 8 := by
  rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by split <;> omega_using [hj]) (by omega_using [hj])

/-- With `pc`, our stack arguments 17 and 18 too. -/
theorem in_aRP {s : State} {j : Nat} (hj : j < 19) : (aR true s).Contains (stackArgAddr s j) 8 := by
  rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by simp only [↓reduceIte]; omega_using [hj]) (by omega_using [hj])

theorem aR_mem {pc : Bool} {s : State} : aR pc s ∈ rdL pc s := by cases pc <;> simp

/-- After the saves and the prologue. -/
structure Entered (s t : State) : Prop where
  sv : Saves s t
  rd : t.rd = s.rd
  mem : Frame [kR s] s.mem t.mem
  r12 : t.gpr .r12 = fb s
  r14 : t.gpr .r14 = Sd s
  r15 : t.gpr .r15 = s.gpr .r7
  r16 : t.gpr .r16 = s.gpr .r3
  r17 : t.gpr .r17 = s.gpr .r5
  r18 : t.gpr .r18 = stackArg s 9
  r19 : t.gpr .r19 = stackArg s 10
  args : ∀ r ∈ [Reg.r6, .r7, .r8, .r9, .r10, .r20, .r21, .r22, .r23], t.gpr r = s.gpr r

section
variable {pc : Bool} {s : State} (P : PreD pc s)
include P

omit P in
theorem toD {m m' : Mem} (h : Frame [kR s] m m') : Frame [kD s] m m' :=
  h.sub fun r hr => ⟨kD s, List.mem_singleton_self _, by rw [List.mem_singleton.mp hr]; exact kR_sub⟩

/-- A load of our stack argument `j`, in `aR`, through `r`, which holds `fb s + o`. -/
theorem wp_argA {t : State} {r b : Reg} {j o : Nat} {is : List Instr} {Q : State → Prop}
    (hin : (aR pc s).Contains (stackArgAddr s j) 8)
    (hb : t.gpr b = fb s - BitVec.ofNat 64 o) (hrd : t.rd = s.rd) (hm : Frame [kD s] s.mem t.mem)
    (k : ∀ t', Only [r] t t' → t'.gpr r = stackArg s j → WP isa (.block is) t' Q)
    (ho : o + arg j < 2 ^ 15 ∧ (o + arg j) % 4 = 0) (hb0 : b ≠ .r0) :
    WP isa (.block (.load .d r b (o + arg j) :: is)) t Q := by
  refine wp_ld (a := stackArgAddr s j) (by
    rw [hb, stackArgAddr_fb, BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.sub_add_cancel]) ?_
    (fun t' o' e => k t' o' ?_) hb0 ho
  · rw [hrd, P.hrd]; exact ⟨aR pc s, List.mem_append_left _ aR_mem, hin⟩
  · rw [e, stackArg, hm.readW hin (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact P.ka.symm) (by decide)]

/-- A load of our stack argument `j` through `r`, which holds `fb s + o`. -/
theorem wp_argD {t : State} {r b : Reg} {j o : Nat} {is : List Instr} {Q : State → Prop} (hj : j < 17)
    (hb : t.gpr b = fb s - BitVec.ofNat 64 o) (hrd : t.rd = s.rd) (hm : Frame [kD s] s.mem t.mem)
    (k : ∀ t', Only [r] t t' → t'.gpr r = stackArg s j → WP isa (.block is) t' Q)
    (ho : o + arg j < 2 ^ 15 ∧ (o + arg j) % 4 = 0 := by decide) (hb0 : b ≠ .r0 := by decide) :
    WP isa (.block (.load .d r b (o + arg j) :: is)) t Q :=
  wp_argA P (in_aR hj) hb hrd hm k ho hb0

omit P in
/-- With `pc`, a load of our stack argument `j < 19`. -/
theorem wp_argP (P : PreD true s) {t : State} {r b : Reg} {j o : Nat} {is : List Instr} {Q : State → Prop}
    (hj : j < 19) (hb : t.gpr b = fb s - BitVec.ofNat 64 o) (hrd : t.rd = s.rd) (hm : Frame [kD s] s.mem t.mem)
    (k : ∀ t', Only [r] t t' → t'.gpr r = stackArg s j → WP isa (.block is) t' Q)
    (ho : o + arg j < 2 ^ 15 ∧ (o + arg j) % 4 = 0 := by decide) (hb0 : b ≠ .r0 := by decide) :
    WP isa (.block (.load .d r b (o + arg j) :: is)) t Q :=
  wp_argA P (in_aRP hj) hb hrd hm k ho hb0

theorem entry_ok : WP isa (.block (save ++ Dec.prologue)) (allocated frameBytes s) (Entered s) := by
  have hm0 : Frame [kR s] s.mem (allocated frameBytes s).mem := by
    rw [allocated_mem]
    exact (Frame.refl _ _).write (List.mem_singleton_self _) _ (by
      have := frame_contains s (d := 0) (n := 8) (by decide); rwa [BitVec.add_zero] at this)
  refine save_ok (allocated_sp _ _) (by rw [allocated_wr, frameR_eq]) hm0 (fun r _ => by rw [allocated_gpr])
    (allocated_lr _ _) fun v kv h12 hm hsv hls => ?_
  have hrd : v.rd = s.rd := kv.rd.trans (allocated_rd _ _)
  have h12' : v.gpr .r12 = fb s - BitVec.ofNat 64 0 := by rw [h12, BitVec.sub_zero]
  simp only [Dec.prologue]
  refine wp_argD P (j := 13) (o := 0) (by decide) h12' hrd (toD hm) fun v₁ o₁ e₁ => ?_
  refine wp_mov fun v₂ o₂ e₂ => wp_mov fun v₃ o₃ e₃ => wp_mov fun v₄ o₄ e₄ => ?_
  have k₄ : Only [.r14, .r15, .r16, .r17] v v₄ := (o₁.trans (o₂.trans (o₃.trans o₄))).mono
  have g4 : v₄.gpr .r12 = fb s - BitVec.ofNat 64 0 := by rw [k₄.get .r12]; exact h12'
  have m4 : Frame [kR s] s.mem v₄.mem := by rw [k₄.mem]; exact hm
  refine wp_argD P (j := 9) (o := 0) (by decide) g4 (k₄.rd.trans hrd) (toD m4) fun v₅ o₅ e₅ => ?_
  have g5 : v₅.gpr .r12 = fb s - BitVec.ofNat 64 0 := by rw [o₅.get .r12]; exact g4
  have m5 : Frame [kR s] s.mem v₅.mem := by rw [o₅.mem]; exact m4
  refine wp_argD P (j := 10) (o := 0) (by decide) g5 (o₅.rd.trans (k₄.rd.trans hrd)) (toD m5) fun w ow ew => wp_nil ?_
  have kw : Only [.r14, .r15, .r16, .r17, .r18, .r19] v w := (k₄.trans (o₅.trans ow)).mono
  have gs : ∀ r ∉ [Reg.r12, .r0], v.gpr r = s.gpr r := fun r hr => by
    rw [kv.gpr r hr, allocated_gpr]
  refine ⟨⟨by rw [kw.sp, kv.sp, allocated_sp], by rw [kw.wr, kv.wr, allocated_wr, frameR_eq],
    fun r hr => by rw [kw.gpr r (by revert r; decide), gs r (by revert r; decide)],
    by rw [kw.mem]; exact hsv, by rw [kw.mem]; exact hls⟩, kw.rd.trans hrd, by rw [kw.mem]; exact hm,
    by rw [kw.get .r12]; exact h12, ?_, ?_, ?_, ?_, ?_, ew, fun r hr => ?_⟩
  · rw [ow.get .r14, o₅.get .r14, o₄.get .r14, o₃.get .r14, o₂.get .r14]; exact e₁
  · rw [ow.get .r15, o₅.get .r15, o₄.get .r15, o₃.get .r15, e₂, o₁.get .r7, gs .r7 (by decide)]
  · rw [ow.get .r16, o₅.get .r16, o₄.get .r16, e₃, o₂.get .r3, o₁.get .r3, gs .r3 (by decide)]
  · rw [ow.get .r17, o₅.get .r17, e₄, o₃.get .r5, o₂.get .r5, o₁.get .r5, gs .r5 (by decide)]
  · rw [ow.get .r18]; exact e₅
  · rw [kw.gpr r (by revert r; decide), gs r (by revert r; decide)]

end

end VG.Proof.RsaOaep.PPC64LE.Dec

end

end

/-!
# RSAES-OAEP decryption on PPC64LE: the private operation's arguments

Untrusted: everything here is checked by Lean. In the frame of `privBytes`
bytes below ours (`pb`), `privArgs` writes `vg_rsa_private_checked`'s twelve
stack arguments to its Parameter Save Area (`psa`: `p`, our stack arguments
0 to 8, the rest of `scratch` and its length in words) and sets its
registers (`AtPriv`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE.Dec

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE VG.Impl.RsaOaep.PPC64LE.Dec
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep MemTo wp_ld wp_std wp_mov wp_li wp_add wp_addi wp_subi wp_addSp wp_nil)

/-- The base of the private operation's frame. -/
abbrev pb (s : State) : Addr := fb s - BitVec.ofNat 64 privBytes

/-- Its stack argument `i`, as `privArgs` (and `preArgs`) write it. -/
def psa (s : State) : Nat → BitVec 64
  | 0 => s.gpr .r10
  | 10 => Sd s + BitVec.ofNat 64 oRsa
  | 11 => BitVec.ofNat 64 ((stackArg s 14).toNat - 1024)
  | 12 => stackArg s 17
  | 13 => stackArg s 18
  | i + 1 => stackArg s i

theorem pb_eq (s : State) : pb s = s.sp - BitVec.ofNat 64 (frameBytes + privBytes) := by
  rw [pb, fb, BitVec.sub_sub, BitVec.ofNat_add]

/-- The region of `pb s + d` within the stack the function uses. -/
theorem pb_base (s : State) :
    pb s = (s.sp - BitVec.ofNat 64 stackBytes) + BitVec.ofNat 64 Impl.Rsa.PPC64LE.Priv.frameBytes := by
  rw [pb, fb, ← Offset.sub_add_eq, ← BitVec.ofNat_add, ← Offset.sub_sub_eq, Offset.ofNat_sub_ofNat (by decide)]; rfl

/-- The region of `pb s + d` within the stack the function uses. -/
theorem pb_sub (s : State) {d n : Nat} (h : d + n ≤ frameBytes + privBytes) :
    Region.Sub ⟨pb s + BitVec.ofNat 64 d, n⟩ (kD s) := by
  rw [pb_base, Offset.add_add]; exact Offset.sub_base _ (by unfold stackBytes; omega_using [h])

/-- In the private operation's frame, at the call: with `pc`, of
`vg_rsa_private_checked_precomputed`, with two more stack arguments. -/
structure AtPriv (pc : Bool) (s t : State) : Prop where
  sp : t.sp = pb s
  rd : t.rd = s.rd
  wr : t.wr = ⟨pb s + BitVec.ofNat 64 32, 176⟩ :: fr s :: s.wr
  mem : Frame [kD s] s.mem t.mem
  sv : Spill.Saved (fb s) s.gpr saved t.mem
  ls : t.mem.readW (fb s + BitVec.ofNat 64 oLr) 64 = s.lr
  hi : ∀ r ∈ hiRegs, t.gpr r = s.gpr r
  r3 : t.gpr .r3 = Sd s
  r4 : t.gpr .r4 = s.gpr .r7
  r5 : t.gpr .r5 = s.gpr .r6
  r6 : t.gpr .r6 = s.gpr .r7
  r7 : t.gpr .r7 = s.gpr .r8
  r8 : t.gpr .r8 = s.gpr .r9
  r9 : t.gpr .r9 = stackArg s 11
  r10 : t.gpr .r10 = s.gpr .r7
  r14 : t.gpr .r14 = Sd s
  r15 : t.gpr .r15 = s.gpr .r7
  r16 : t.gpr .r16 = s.gpr .r3
  r17 : t.gpr .r17 = s.gpr .r5
  r18 : t.gpr .r18 = stackArg s 9
  r19 : t.gpr .r19 = stackArg s 10
  keep : ∀ r ∈ [Reg.r20, .r21, .r22, .r23], t.gpr r = s.gpr r
  r12 : t.gpr .r12 = pb s
  psa : ∀ i < nCallArgs pc, t.mem.readW (pb s + BitVec.ofNat 64 (96 + 8 * i)) 64 = psa s i

/-- The state of the copies of our stack arguments: `n` of them done. -/
structure Cp (s t₀ : State) (n : Nat) (t : State) : Prop where
  k : Keep [.r0] t₀ t
  mem : Frame [⟨pb s + BitVec.ofNat 64 104, 72⟩] t₀.mem t.mem
  got : ∀ j < n, t.mem.readW (pb s + BitVec.ofNat 64 (104 + 8 * j)) 64 = stackArg s j

theorem privArgs_eq : privArgs = ([.addSp .r12 0, .store .d .r10 .r12 96] : List Instr) ++
    ((List.range 9).flatMap fun j => [.load .d .r0 .r12 (argP j), .store .d .r0 .r12 (104 + 8 * j)]) ++
    ([.li .r0 oRsa, .add .r0 .r14 .r0, .store .d .r0 .r12 176, .load .d .r11 .r12 (argP 14),
      .subi .r11 .r11 1024, .store .d .r11 .r12 184, .addi .r3 .r14 oEm, Impl.AesGcm.PPC64LE.mov .r4 .r15,
      Impl.AesGcm.PPC64LE.mov .r5 .r6, Impl.AesGcm.PPC64LE.mov .r6 .r15, Impl.AesGcm.PPC64LE.mov .r7 .r8,
      Impl.AesGcm.PPC64LE.mov .r8 .r9, .load .d .r9 .r12 (argP 11), Impl.AesGcm.PPC64LE.mov .r10 .r15] :
      List Instr) := rfl

theorem sub_ofNat {x : BitVec 64} {a : Nat} (h : a ≤ x.toNat) : x - BitVec.ofNat 64 a = BitVec.ofNat 64 (x.toNat - a) := by
  apply BitVec.eq_of_toNat_eq
  have := x.isLt
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := a) (by omega_using [h]), Nat.mod_eq_of_lt (a := x.toNat - a) (by omega_using [])]; omega_using [h]

/-- The private operation's frame. -/
abbrev PB (s : State) : Region := ⟨pb s, privBytes⟩

theorem pb_in (s : State) {d : Nat} (h : d + 8 ≤ privBytes) : (PB s).Contains (pb s + BitVec.ofNat 64 d) 8 :=
  Offset.contains_base _ h (by unfold privBytes at h; omega_using [h])

/-- Our frame's slots are outside the private operation's frame. -/
theorem slot_PB (s : State) {d : Nat} (hd : d + 8 ≤ frameBytes) :
    ∀ r ∈ [PB s], Region.Disjoint ⟨fb s + BitVec.ofNat 64 d, 8⟩ r := fun r hr => by
  rw [List.mem_singleton.mp hr]
  obtain h := Offset.disjoint_below_above (fb s) (m := privBytes) (a := 0) (l := frameBytes) (by decide)
  rw [BitVec.add_zero] at h
  exact (h.sub_right (Offset.sub_base _ hd)).symm

section
variable {pc : Bool} {s : State} (P : PreD pc s)
include P

omit P in
theorem psa_in {d : Nat} (h₁ : 32 ≤ d) (h₂ : d + 8 ≤ privBytes) :
    InRegions (⟨pb s + BitVec.ofNat 64 32, 176⟩ :: fr s :: s.wr) (pb s + BitVec.ofNat 64 d) 8 :=
  ⟨_, List.mem_cons_self .., Offset.contains _ h₁ (by unfold privBytes at h₂; omega_using [h₂]) (by decide)⟩

/-- The copies of our stack arguments 0 to `n - 1`. -/
theorem copies_ok {t₀ : State} (h12 : t₀.gpr .r12 = pb s) (hrd : t₀.rd = s.rd)
    (hwr : t₀.wr = ⟨pb s + BitVec.ofNat 64 32, 176⟩ :: fr s :: s.wr) (hm : Frame [kD s] s.mem t₀.mem) :
    ∀ n ≤ 9, WP isa (.block ((List.range n).flatMap fun j =>
      [.load .d .r0 .r12 (argP j), .store .d .r0 .r12 (104 + 8 * j)])) t₀ (Cp s t₀ n)
  | 0, _ => wp_nil ⟨Keep.refl _ _, Frame.refl _ _, fun _ h => absurd h (by omega_using [])⟩
  | n + 1, hn => by
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (copies_ok h12 hrd hwr hm n (by omega_using [hn])) fun t ⟨k, fm, got⟩ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    obtain hmt : Frame [kD s] s.mem t.mem := hm.trans (fm.sub fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact ⟨kD s, List.mem_singleton_self _, pb_sub s (by unfold frameBytes privBytes; omega_using [])⟩)
    obtain hb : t.gpr .r12 = fb s - BitVec.ofNat 64 privBytes := by rw [k.get .r12, h12]
    refine wp_argD P (j := n) (o := privBytes) (by omega_using [hn]) hb (k.rd.trans hrd) ?_ (fun t₁ o₁ e₁ => ?_)
      ⟨by unfold arg frameBytes privBytes; omega_using [hn], by unfold arg frameBytes privBytes; omega_using []⟩
    · exact Frame.mono hmt fun _ h => h
    obtain hw : InRegions t₁.wr (pb s + BitVec.ofNat 64 (104 + 8 * n)) 8 := by
      rw [o₁.wr, k.wr, hwr]; exact psa_in (by omega_using []) (by unfold privBytes; omega_using [hn])
    refine wp_std (a := pb s + BitVec.ofNat 64 (104 + 8 * n)) (by rw [o₁.get .r12, hb]) hw (fun t₂ m₂ => wp_nil ?_)
      (by decide) ⟨by omega_using [hn], by omega_using []⟩
    obtain k₂ : Keep [.r0] t₀ t₂ := (k.trans (o₁.keep.trans m₂.keep)).mono
    refine ⟨k₂, ?_, fun j hj => ?_⟩
    · rw [m₂.mem, o₁.mem]
      exact fm.writeW (List.mem_singleton_self _) _ (Offset.contains _ (by omega_using []) (by omega_using [hn]) (by omega_using []))
    · rw [m₂.mem, o₁.mem]
      by_cases hj' : j < n
      · rw [Mem.readW_writeW_sep (Offset.sep _ (.inl (by omega_using [hj'])) (by omega_using [hn, hj]) (by omega_using [hn])) (by decide), got j hj']
      · rw [show j = n by omega_using [hj, hj'], Mem.readW_writeW_self64, e₁]

theorem privArgs_ok {t : State} (E : Entered s t) :
    WP isa (.block privArgs) (allocated privBytes t) (AtPriv false s) := by
  have hsp : t.sp = fb s := E.sv.sp
  have usp : (allocated privBytes t).sp = pb s := by rw [allocated_sp, hsp]
  have uwr : (allocated privBytes t).wr = ⟨pb s + BitVec.ofNat 64 32, 176⟩ :: fr s :: s.wr := by
    rw [allocated_wr, E.sv.wr, frameR, hsp]; rfl
  have urd : (allocated privBytes t).rd = s.rd := by rw [allocated_rd, E.rd]
  have um : Frame [PB s] t.mem (allocated privBytes t).mem := by
    rw [allocated_mem]
    refine (Frame.refl _ _).write (List.mem_singleton_self _) _ ?_
    rw [hsp, show fb s - BitVec.ofNat 64 privBytes = pb s + BitVec.ofNat 64 0 by rw [BitVec.add_zero]]
    exact pb_in s (by decide)
  have ug : (allocated privBytes t).gpr = t.gpr := rfl
  rw [privArgs_eq, WP.block_append_iff, WP.block_append_iff]
  refine wp_addSp fun u₁ o₁ e₁ => ?_
  rw [usp, BitVec.add_zero] at e₁
  refine wp_std (a := pb s + BitVec.ofNat 64 96) (by rw [e₁]) (by rw [o₁.wr, uwr]; exact psa_in (by decide) (by decide)) fun u₂ m₂ => wp_nil ?_
  have k₂ : Keep [.r12] (allocated privBytes t) u₂ := (o₁.keep.trans m₂.keep).mono
  have f₂ : Frame [PB s] t.mem u₂.mem := by
    rw [m₂.mem, o₁.mem]; exact um.writeW (List.mem_singleton_self _) _ (pb_in s (by decide))
  have r₂ : u₂.mem.readW (pb s + BitVec.ofNat 64 96) 64 = s.gpr .r10 := by
    rw [m₂.mem, Mem.readW_writeW_self64, o₁.get .r10, ug, E.args .r10 (by decide)]
  have hmD : ∀ {x : State}, Frame [PB s] t.mem x.mem → Frame [kD s] s.mem x.mem := fun h =>
    (toD E.mem).trans (h.sub fun r hr => ⟨kD s, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]
      have := pb_sub s (d := 0) (n := privBytes) (by decide); rwa [BitVec.add_zero] at this⟩)
  have g₂ : u₂.gpr .r12 = pb s := by rw [m₂.gpr, e₁]
  refine WP.mono (copies_ok P (t₀ := u₂) g₂ (by rw [k₂.rd, urd]) (by rw [k₂.wr, uwr]) (hmD f₂) 9 (Nat.le_refl 9))
    fun u₃ ⟨k₃, f₃, got⟩ => ?_
  have g₃ : u₃.gpr .r12 = pb s := by rw [k₃.get .r12, g₂]
  have w₃ : u₃.wr = ⟨pb s + BitVec.ofNat 64 32, 176⟩ :: fr s :: s.wr := by rw [k₃.wr, k₂.wr, uwr]
  have f₃' : Frame [PB s] t.mem u₃.mem := f₂.trans (f₃.sub fun r hr => ⟨PB s, List.mem_singleton_self _, by
    rw [List.mem_singleton.mp hr]; exact Offset.sub_base _ (by decide)⟩)
  refine wp_li (by decide) fun u₄ o₄ e₄ => wp_add fun u₅ o₅ e₅ => ?_
  have g₅ : u₅.gpr .r12 = pb s := by rw [o₅.get .r12, o₄.get .r12, g₃]
  refine wp_std (a := pb s + BitVec.ofNat 64 176) (by rw [g₅]) (by rw [o₅.wr, o₄.wr, w₃]; exact psa_in (by decide) (by decide)) fun u₆ m₆ => ?_
  have f₆ : Frame [PB s] t.mem u₆.mem := by
    rw [m₆.mem, o₅.mem, o₄.mem]; exact f₃'.writeW (List.mem_singleton_self _) _ (pb_in s (by decide))
  have rd₆ : u₆.rd = s.rd := by rw [m₆.rd, o₅.rd, o₄.rd, k₃.rd, k₂.rd, urd]
  refine wp_argD P (j := 14) (o := privBytes) (by decide) (by rw [m₆.gpr, g₅]) rd₆ (hmD f₆) fun u₇ o₇ e₇ => ?_
  refine wp_subi fun u₈ o₈ e₈ => ?_
  refine wp_std (a := pb s + BitVec.ofNat 64 184) (by rw [o₈.get .r12, o₇.get .r12, m₆.gpr, g₅])
    (by rw [o₈.wr, o₇.wr, m₆.wr, o₅.wr, o₄.wr, w₃]; exact psa_in (by decide) (by decide)) fun u₉ m₉ => ?_
  have f₉ : Frame [PB s] t.mem u₉.mem := by
    rw [m₉.mem, o₈.mem, o₇.mem]; exact f₆.writeW (List.mem_singleton_self _) _ (pb_in s (by decide))
  refine wp_addi fun u₁₀ o₁₀ e₁₀ => wp_mov fun u₁₁ o₁₁ e₁₁ => wp_mov fun u₁₂ o₁₂ e₁₂ =>
    wp_mov fun u₁₃ o₁₃ e₁₃ => wp_mov fun u₁₄ o₁₄ e₁₄ => wp_mov fun u₁₅ o₁₅ e₁₅ => ?_
  have k₁₅ : Only [.r3, .r4, .r5, .r6, .r7, .r8] u₉ u₁₅ :=
    (o₁₀.trans (o₁₁.trans (o₁₂.trans (o₁₃.trans (o₁₄.trans o₁₅))))).mono
  refine wp_argD P (j := 11) (o := privBytes) (by decide) (by rw [k₁₅.get .r12, m₉.gpr, o₈.get .r12, o₇.get .r12,
    m₆.gpr, g₅]) (by rw [k₁₅.rd, m₉.rd, o₈.rd, o₇.rd, rd₆]) (by rw [k₁₅.mem]; exact hmD f₉)
    fun u₁₆ o₁₆ e₁₆ => wp_mov fun w ow ew => wp_nil ?_
  -- What the block keeps.
  have K : Keep [.r12, .r0, .r11, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10] (allocated privBytes t) w :=
    (((o₁.keep.trans m₂.keep).trans (k₃.trans ((o₄.keep.trans o₅.keep).trans
      (m₆.keep.trans (o₇.keep.trans (o₈.keep.trans (m₉.keep.trans (k₁₅.keep.trans (o₁₆.keep.trans
      ow.keep)))))))))).mono
  have kt : ∀ r ∉ [Reg.r12, .r0, .r11, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10], w.gpr r = t.gpr r :=
    fun r hr => by rw [K.gpr r hr]; rfl
  have K₉ : Keep [.r12, .r0, .r11] (allocated privBytes t) u₉ :=
    (((o₁.keep.trans m₂.keep).trans (k₃.trans ((o₄.keep.trans o₅.keep).trans
      (m₆.keep.trans (o₇.keep.trans (o₈.keep.trans m₉.keep))))))).mono
  have k9 : ∀ r ∉ [Reg.r12, .r0, .r11], u₉.gpr r = t.gpr r := fun r hr => by rw [K₉.gpr r hr]; rfl
  have hl : 1024 ≤ (stackArg s 14).toNat := by
    have := P.hs; unfold Spec.RsaPss.scratchWords Spec.Rsa.scratchWords at this; omega_using [this]
  have v184 : u₈.gpr .r11 = psa s 11 := by
    rw [e₈, e₇]; exact sub_ofNat hl
  have v176 : u₅.gpr .r0 = psa s 10 := by
    rw [e₅, o₄.get .r14, e₄, k₃.get .r14, m₂.gpr, o₁.get .r14, ug, E.r14]; rfl
  have wm : w.mem = (u₆.mem.writeW (pb s + BitVec.ofNat 64 184) (psa s 11)) := by
    rw [ow.mem, o₁₆.mem, k₁₅.mem, m₉.mem, o₈.mem, o₇.mem, v184]
  have m6 : u₆.mem = (u₃.mem.writeW (pb s + BitVec.ofNat 64 176) (psa s 10)) := by
    rw [m₆.mem, o₅.mem, o₄.mem, v176]
  have fw : Frame [PB s] t.mem w.mem := by rw [ow.mem, o₁₆.mem, k₁₅.mem]; exact f₉
  have sl : ∀ {d : Nat}, d + 8 ≤ frameBytes → ∀ r ∈ [PB s], Region.Disjoint ⟨fb s + BitVec.ofNat 64 d, 8⟩ r :=
    fun hd => slot_PB s hd
  -- The stack arguments.
  have sep : ∀ {a b : Nat}, a + 8 ≤ b ∨ b + 8 ≤ a → a + 8 ≤ privBytes → b + 8 ≤ privBytes →
      Mem.Sep (pb s + BitVec.ofNat 64 a) (64 / 8) (pb s + BitVec.ofNat 64 b) (64 / 8) := fun h ha hb =>
    Offset.sep _ h (by unfold privBytes at ha; omega_using [ha]) (by unfold privBytes at hb; omega_using [hb])
  have hpsa : ∀ i < 12, w.mem.readW (pb s + BitVec.ofNat 64 (96 + 8 * i)) 64 = psa s i := by
    intro i hi
    rw [wm]
    by_cases h11 : i = 11
    · subst h11; exact Mem.readW_writeW_self64 _ _ _
    rw [Mem.readW_writeW_sep (sep (by omega_using [h11]) (by unfold privBytes; omega_using [hi]) (by decide)) (by decide), m6]
    by_cases h10 : i = 10
    · subst h10; exact Mem.readW_writeW_self64 _ _ _
    rw [Mem.readW_writeW_sep (sep (by omega_using [h10]) (by unfold privBytes; omega_using [hi]) (by decide)) (by decide)]
    by_cases h0 : i = 0
    · subst h0
      rw [f₃.readW (r := ⟨pb s + BitVec.ofNat 64 96, 8⟩) (Region.contains_self _ _) (fun r hr => by
        rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide))
        (by decide)]
      exact r₂
    · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega_using [h0]⟩
      rw [show 96 + 8 * (j + 1) = 104 + 8 * j by omega_using [], got j (by omega_using [hi, h11, h10])]
      rcases (by omega_using [hi, h11, h10] : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  refine ⟨by rw [K.sp, usp], by rw [K.rd, urd], by rw [K.wr, uwr], hmD fw,
    E.sv.sv.frame fw fun p hp r hr => sl (by have := saved_offs p hp; unfold oLr frameBytes at *; omega_using [this]) r hr,
    by rw [fw.readW (Region.contains_self _ _) (sl (by decide)) (by decide)]; exact E.sv.ls,
    fun r hr => by rw [kt r (by revert r; decide)]; exact E.sv.hi r hr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    by rw [kt _ (by decide)]; exact E.r14, by rw [kt _ (by decide)]; exact E.r15,
    by rw [kt _ (by decide)]; exact E.r16, by rw [kt _ (by decide)]; exact E.r17,
    by rw [kt _ (by decide)]; exact E.r18, by rw [kt _ (by decide)]; exact E.r19,
    fun r hr => by rw [kt r (by revert r; decide)]; exact E.args r (by revert r; decide),
    by rw [ow.get .r12, o₁₆.get .r12, k₁₅.get .r12, m₉.gpr, o₈.get .r12, o₇.get .r12, m₆.gpr, g₅],
    fun i hi => hpsa i (by simpa only [nCallArgs, Bool.false_eq_true, ↓reduceIte] using hi)⟩
  · rw [ow.get .r3, o₁₆.get .r3, o₁₅.get .r3, o₁₄.get .r3, o₁₃.get .r3, o₁₂.get .r3, o₁₁.get .r3, e₁₀,
      k9 .r14 (by decide), E.r14]; exact BitVec.add_zero _
  · rw [ow.get .r4, o₁₆.get .r4, o₁₅.get .r4, o₁₄.get .r4, o₁₃.get .r4, o₁₂.get .r4, e₁₁, o₁₀.get .r15,
      k9 .r15 (by decide), E.r15]
  · rw [ow.get .r5, o₁₆.get .r5, o₁₅.get .r5, o₁₄.get .r5, o₁₃.get .r5, e₁₂, o₁₁.get .r6, o₁₀.get .r6,
      k9 .r6 (by decide), E.args .r6 (by decide)]
  · rw [ow.get .r6, o₁₆.get .r6, o₁₅.get .r6, o₁₄.get .r6, e₁₃, o₁₂.get .r15, o₁₁.get .r15, o₁₀.get .r15,
      k9 .r15 (by decide), E.r15]
  · rw [ow.get .r7, o₁₆.get .r7, o₁₅.get .r7, e₁₄, o₁₃.get .r8, o₁₂.get .r8, o₁₁.get .r8, o₁₀.get .r8,
      k9 .r8 (by decide), E.args .r8 (by decide)]
  · rw [ow.get .r8, o₁₆.get .r8, e₁₅, o₁₄.get .r9, o₁₃.get .r9, o₁₂.get .r9, o₁₁.get .r9, o₁₀.get .r9,
      k9 .r9 (by decide), E.args .r9 (by decide)]
  · rw [ow.get .r9]; exact e₁₆
  · rw [ew, o₁₆.get .r15, k₁₅.get .r15, k9 .r15 (by decide), E.r15]

/-- With `pc`, the copies of our stack arguments 17 and 18 (`pre`,
`pre_len`) as the call's 12 and 13. -/
theorem preArgs_ok {u : State} (A : AtPriv false s u) : WP isa (.block (preArgs pc)) u (AtPriv pc s) := by
  cases pc with
  | false => exact wp_nil A
  | true =>
    simp only [preArgs]
    refine wp_argP P (j := 17) (o := privBytes) (by decide) A.r12 A.rd A.mem fun u₁ o₁ e₁ => ?_
    refine wp_std (a := pb s + BitVec.ofNat 64 192) (by rw [o₁.get .r12, A.r12])
      (by rw [o₁.wr, A.wr]; exact psa_in (by decide) (by decide)) fun u₂ m₂ => ?_
    have f₂ : Frame [PB s] u.mem u₂.mem := by
      rw [m₂.mem, o₁.mem]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (pb_in s (by decide))
    have hmD : ∀ {x : State}, Frame [PB s] u.mem x.mem → Frame [kD s] s.mem x.mem := fun h =>
      A.mem.trans (h.sub fun r hr => ⟨kD s, List.mem_singleton_self _, by
        rw [List.mem_singleton.mp hr]
        have := pb_sub s (d := 0) (n := privBytes) (by decide); rwa [BitVec.add_zero] at this⟩)
    refine wp_argP P (j := 18) (o := privBytes) (by decide) (by rw [m₂.gpr, o₁.get .r12, A.r12])
      (by rw [m₂.rd, o₁.rd, A.rd]) (hmD f₂) fun u₃ o₃ e₃ => ?_
    refine wp_std (a := pb s + BitVec.ofNat 64 200) (by rw [o₃.get .r12, m₂.gpr, o₁.get .r12, A.r12])
      (by rw [o₃.wr, m₂.wr, o₁.wr, A.wr]; exact psa_in (by decide) (by decide)) fun w m₄ => wp_nil ?_
    have K : Keep [.r0] u w := (o₁.keep.trans (m₂.keep.trans (o₃.keep.trans m₄.keep))).mono
    have kg : ∀ r, r ≠ .r0 → w.gpr r = u.gpr r := fun r hr => K.gpr r (by simpa using hr)
    have fw : Frame [PB s] u.mem w.mem := by
      rw [m₄.mem, o₃.mem]; exact f₂.writeW (List.mem_singleton_self _) _ (pb_in s (by decide))
    have sep : ∀ {a b : Nat}, a + 8 ≤ b ∨ b + 8 ≤ a → a + 8 ≤ privBytes → b + 8 ≤ privBytes →
        Mem.Sep (pb s + BitVec.ofNat 64 a) (64 / 8) (pb s + BitVec.ofNat 64 b) (64 / 8) := fun h ha hb =>
      Offset.sep _ h (by unfold privBytes at ha; omega_using [ha]) (by unfold privBytes at hb; omega_using [hb])
    refine ⟨by rw [K.sp, A.sp], by rw [K.rd, A.rd], by rw [K.wr, A.wr], hmD fw,
      A.sv.frame fw fun p hp r hr => slot_PB s (by have := saved_offs p hp; unfold oLr frameBytes at *; omega_using [this]) r hr,
      by rw [fw.readW (Region.contains_self _ _) (slot_PB s (by decide)) (by decide)]; exact A.ls,
      fun r hr => by rw [kg r (by revert r; decide)]; exact A.hi r hr,
      by rw [kg _ (by decide)]; exact A.r3, by rw [kg _ (by decide)]; exact A.r4,
      by rw [kg _ (by decide)]; exact A.r5, by rw [kg _ (by decide)]; exact A.r6,
      by rw [kg _ (by decide)]; exact A.r7, by rw [kg _ (by decide)]; exact A.r8,
      by rw [kg _ (by decide)]; exact A.r9, by rw [kg _ (by decide)]; exact A.r10,
      by rw [kg _ (by decide)]; exact A.r14, by rw [kg _ (by decide)]; exact A.r15,
      by rw [kg _ (by decide)]; exact A.r16, by rw [kg _ (by decide)]; exact A.r17,
      by rw [kg _ (by decide)]; exact A.r18, by rw [kg _ (by decide)]; exact A.r19,
      fun r hr => by rw [kg r (by revert r; decide)]; exact A.keep r hr,
      by rw [kg _ (by decide)]; exact A.r12, fun i hi => ?_⟩
    simp only [nCallArgs, ↓reduceIte] at hi
    rw [m₄.mem]
    by_cases h13 : i = 13
    · subst h13; rw [Mem.readW_writeW_self64, e₃]; rfl
    rw [Mem.readW_writeW_sep (sep (by omega_using [h13]) (by unfold privBytes; omega_using [hi]) (by decide)) (by decide), o₃.mem, m₂.mem,
      o₁.mem]
    by_cases h12 : i = 12
    · subst h12; rw [Mem.readW_writeW_self64, e₁]; rfl
    rw [Mem.readW_writeW_sep (sep (by omega_using [h12]) (by unfold privBytes; omega_using [hi]) (by decide)) (by decide)]
    exact A.psa i (by simp only [nCallArgs, Bool.false_eq_true, ↓reduceIte]; omega_using [hi, h13, h12])

/-- The arguments, with `pc` `pre` and `pre_len` too. -/
theorem privArgsG_ok {t : State} (E : Entered s t) :
    WP isa (.block (privArgs ++ preArgs pc)) (allocated privBytes t) (AtPriv pc s) := by
  rw [WP.block_append_iff]
  exact WP.mono (privArgs_ok P E) fun _ A => preArgs_ok P A

end

end VG.Proof.RsaOaep.PPC64LE.Dec

end

end

/-! ### `RsaOaep.PPC64LE.Dc.PrivPre`, which only this module used -/

section

/-!
# RSAES-OAEP decryption on PPC64LE: the private operation's precondition

Untrusted: everything here is checked by Lean. The regions the call of
`vg_rsa_private_checked` is narrowed to (`callRd`, `callWr`): `n`, `e`, the
ciphertext, the private key and its stack arguments; `EM`'s place and the
rest of `scratch`. Its precondition at the call (`preP_at`), from the
caller's (`PreD`) and the state at the call (`AtPriv`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE.Dec

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE VG.Impl.RsaOaep.PPC64LE.Dec

/-- `EM`'s place and the rest of `scratch`, which the call writes. -/
abbrev emR (s : State) : Region := ⟨Sd s, kk s⟩
abbrev rsR (s : State) : Region := ⟨Sd s + BitVec.ofNat 64 oRsa, ((stackArg s 14).toNat - 1024) * 8⟩
variable {pc : Bool}

/-- The call's stack arguments: twelve, or with `pc` fourteen. -/
abbrev psaR (pc : Bool) (s : State) : Region := ⟨pb s + BitVec.ofNat 64 96, if pc then 112 else 96⟩

/-- The regions the call reads and writes. -/
abbrev callRd (pc : Bool) (s : State) : List Region :=
  [nR s, eR s, ⟨stackArg s 11, kk s⟩, pR s, qR s, dpR s, dqR s, qiR s] ++ (if pc then [preR s] else []) ++
    [psaR pc s]

abbrev callWr (s : State) : List Region := [emR s, rsR s]

/-- The call's narrowed entry state. -/
abbrev callE (pc : Bool) (s t : State) : State := t.callEntry.withRegions (callRd pc s) (callWr s)

theorem callE_gpr (s t : State) {r : Reg} (hr : r ∉ linkRegs := by decide) : (callE pc s t).gpr r = t.gpr r :=
  State.callEntry_gpr t hr

theorem callE_sp (s t : State) : (callE pc s t).sp = t.sp := rfl
theorem callE_stackArg {s t : State} (A : AtPriv pc s t) {i : Nat} (hi : i < nCallArgs pc) :
    stackArg (callE pc s t) i = psa s i := by
  show t.mem.readW (stackArgAddr (callE pc s t) i) 64 = _
  rw [stackArgAddr, callE_sp, A.sp, show 32 + 8 * (8 + i) = 96 + 8 * i by omega_using []]
  exact A.psa i hi

theorem callE_addr {s t : State} (A : AtPriv pc s t) : stackArgAddr (callE pc s t) 0 = pb s + BitVec.ofNat 64 96 := by
  rw [stackArgAddr, callE_sp, A.sp]

theorem lt_nCall {i : Nat} (hi : i < 12) : i < nCallArgs pc := by
  cases pc <;> simp only [nCallArgs, Bool.false_eq_true, ↓reduceIte] <;> omega_using [hi]

theorem psa_subD (s : State) : Region.Sub (psaR pc s) (kD s) := by
  cases pc
  · exact pb_sub s (by decide)
  · exact pb_sub s (by decide)

/-- The callee's frame and the call's stack arguments. -/
theorem callee_psa (s : State) :
    Region.Disjoint ⟨s.sp - BitVec.ofNat 64 stackBytes, Impl.Rsa.PPC64LE.Priv.frameBytes⟩ (psaR pc s) := by
  show Region.Disjoint _ ⟨pb s + BitVec.ofNat 64 96, _⟩
  rw [pb_base, Offset.add_add]
  cases pc
  · exact (Offset.disjoint_base _ (by decide) (by decide)).symm
  · exact (Offset.disjoint_base _ (by decide) (by decide)).symm

section
variable {s : State} (P : PreD pc s)
include P

theorem em_sub : Region.Sub (emR s) (scR s) :=
  Region.sub_prefix (by show kk s ≤ _; have := scLen P; have := P.k2; unfold kk oRsa at *; omega_arith)

theorem rs_sub : Region.Sub (rsR s) (scR s) := by
  have := P.hs; unfold Spec.RsaPss.scratchWords Spec.Rsa.scratchWords at this
  exact Offset.sub_base _ (by unfold oRsa; omega_using [this])


theorem em_rs : (emR s).Disjoint (rsR s) := by
  obtain h := Offset.disjoint_base (Sd s) (d := oRsa) (n := ((stackArg s 14).toNat - 1024) * 8) (k := kk s)
    (by have := P.k2; unfold kk oRsa; omega_using [this]) (by have := P.wsc; have := scLen P; unfold oRsa at *; omega_arith)
  exact h.symm

theorem pb_toNat : (pb s).toNat = s.sp.toNat - 464 := by
  have sp1 := P.sp1
  rw [pb_eq, Offset.toNat_sub_ofNat, Nat.mod_eq_of_lt (a := frameBytes + privBytes) (by decide)]
  unfold stackBytes at sp1; unfold frameBytes privBytes at *; omega_using [sp1]

theorem preP_at {t : State} (A : AtPriv pc s t) : Rsa.PPC64LE.Priv.PreP pc (callE pc s t) := by
  have hk := P.k2
  have hk1 := P.k1
  obtain sa := fun i (hi : i < 12) => callE_stackArg A (i := i) (lt_nCall hi)
  have hsp : (callE pc s t).sp = pb s := A.sp
  have sp1 := P.sp1
  obtain hpbt : (pb s).toNat = s.sp.toNat - 464 := by
    rw [pb_eq, Offset.toNat_sub_ofNat, Nat.mod_eq_of_lt (a := frameBytes + privBytes) (by decide)]
    unfold stackBytes at sp1; unfold frameBytes privBytes at *; omega_using [sp1]
  obtain g3 : (callE pc s t).gpr .r3 = Sd s := (callE_gpr (pc := pc) s t).trans A.r3
  obtain g4 : (callE pc s t).gpr .r4 = s.gpr .r7 := (callE_gpr (pc := pc) s t).trans A.r4
  obtain g5 : (callE pc s t).gpr .r5 = s.gpr .r6 := (callE_gpr (pc := pc) s t).trans A.r5
  obtain g6 : (callE pc s t).gpr .r6 = s.gpr .r7 := (callE_gpr (pc := pc) s t).trans A.r6
  obtain g7 : (callE pc s t).gpr .r7 = s.gpr .r8 := (callE_gpr (pc := pc) s t).trans A.r7
  obtain g8 : (callE pc s t).gpr .r8 = s.gpr .r9 := (callE_gpr (pc := pc) s t).trans A.r8
  obtain g9 : (callE pc s t).gpr .r9 = stackArg s 11 := (callE_gpr (pc := pc) s t).trans A.r9
  obtain g10 : (callE pc s t).gpr .r10 = s.gpr .r7 := (callE_gpr (pc := pc) s t).trans A.r10
  obtain hO : Rsa.PPC64LE.Priv.oR (callE pc s t) = emR s := by simp only [Rsa.PPC64LE.Priv.oR, g3, g4, emR, kk]
  obtain hN : Rsa.PPC64LE.Priv.nR (callE pc s t) = nR s := by simp only [Rsa.PPC64LE.Priv.nR, g5, g6]
  obtain hE : Rsa.PPC64LE.Priv.eR (callE pc s t) = eR s := by simp only [Rsa.PPC64LE.Priv.eR, g7, g8]
  obtain hI : Rsa.PPC64LE.Priv.iR (callE pc s t) = ctR s := by simp only [Rsa.PPC64LE.Priv.iR, g9, g10, ctR, P.oc]
  obtain hI' : (⟨stackArg s 11, kk s⟩ : Region) = ctR s := by simp only [ctR, kk, P.oc]
  obtain hP : Rsa.PPC64LE.Priv.pR (callE pc s t) = pR s := by
    simp only [Rsa.PPC64LE.Priv.pR, sa 0 (by decide), sa 1 (by decide)]; rfl
  obtain hQ : Rsa.PPC64LE.Priv.qR (callE pc s t) = qR s := by
    simp only [Rsa.PPC64LE.Priv.qR, sa 2 (by decide), sa 3 (by decide)]; rfl
  obtain hDP : Rsa.PPC64LE.Priv.dpR (callE pc s t) = dpR s := by
    simp only [Rsa.PPC64LE.Priv.dpR, sa 4 (by decide), sa 5 (by decide)]; rfl
  obtain hDQ : Rsa.PPC64LE.Priv.dqR (callE pc s t) = dqR s := by
    simp only [Rsa.PPC64LE.Priv.dqR, sa 6 (by decide), sa 7 (by decide)]; rfl
  obtain hQI : Rsa.PPC64LE.Priv.qiR (callE pc s t) = qiR s := by
    simp only [Rsa.PPC64LE.Priv.qiR, sa 8 (by decide), sa 9 (by decide)]; rfl
  obtain hl : 1024 ≤ (stackArg s 14).toNat := by
    have := P.hs; unfold Spec.RsaPss.scratchWords Spec.Rsa.scratchWords at this; omega_using [this]
  obtain w11 : (BitVec.ofNat 64 ((stackArg s 14).toNat - 1024)).toNat = (stackArg s 14).toNat - 1024 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := (stackArg s 14).isLt; omega_using [])]
  obtain hS : Rsa.PPC64LE.Priv.sR (callE pc s t) = rsR s := by
    simp only [Rsa.PPC64LE.Priv.sR, sa 10 (by decide), sa 11 (by decide), psa, w11]
  obtain hA : Rsa.PPC64LE.Priv.aR pc (callE pc s t) = psaR pc s := by simp only [Rsa.PPC64LE.Priv.aR, callE_addr A]
  obtain hK : Rsa.PPC64LE.Priv.kR (callE pc s t) = ⟨s.sp - BitVec.ofNat 64 stackBytes,
      Impl.Rsa.PPC64LE.Priv.frameBytes⟩ := by
    simp only [Rsa.PPC64LE.Priv.kR, Rsa.PPC64LE.Priv.fb, hsp, pb_base, BitVec.add_sub_cancel]
  obtain kD' : Region.Sub ⟨s.sp - BitVec.ofNat 64 stackBytes, Impl.Rsa.PPC64LE.Priv.frameBytes⟩ (kD s) := by
    have := Offset.sub_base (s.sp - BitVec.ofNat 64 stackBytes) (d := 0) (n := Impl.Rsa.PPC64LE.Priv.frameBytes)
      (k := stackBytes) (by decide)
    rwa [BitVec.add_zero] at this
  obtain ka := callee_psa (pc := pc) s
  obtain es := em_sub P
  obtain rss := rs_sub P
  obtain ps : Region.Sub (psaR pc s) (kD s) := psa_subD s
  obtain s1 := sa 1 (by decide)
  obtain s3 := sa 3 (by decide)
  obtain s5 := sa 5 (by decide)
  obtain s7 := sa 7 (by decide)
  obtain s9 := sa 9 (by decide)
  obtain s11 := sa 11 (by decide)
  simp only [psa] at s1 s3 s5 s7 s9 s11
  obtain wS : (Sd s + BitVec.ofNat 64 oRsa).toNat = (stackArg s 13).toNat + oRsa := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := oRsa) (by decide),
      Nat.mod_eq_of_lt (by
        have e : (Sd s).toNat = (stackArg s 13).toNat := rfl
        have := P.wsc; have := P.hs; unfold Spec.RsaPss.scratchWords Spec.Rsa.scratchWords oRsa at *; omega_arith)]
  obtain q1 : Impl.Rsa.PPC64LE.Priv.frameBytes ≤ (callE pc s t).sp.toNat := by
    rw [hsp, hpbt]; rw [stackBytes_eq] at sp1; unfold Impl.Rsa.PPC64LE.Priv.frameBytes; omega_using [sp1]
  obtain q2 : (callE pc s t).sp.toNat + 192 ≤ 2 ^ 64 := by rw [hsp, hpbt]; have := P.sp2; split at this <;> omega_using []
  have hkk : kk s = (s.gpr .r7).toNat := rfl
  refine ⟨q1, q2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Rsa.PPC64LE.Priv.rdL]
    rw [hN, hE, hI, hP, hQ, hDP, hDQ, hQI, hA, ← hI']
    cases pc
    · rfl
    · simp only [↓reduceIte, Rsa.PPC64LE.Priv.preR, callE_stackArg A (i := 12) (by decide),
        callE_stackArg A (i := 13) (by decide), psa]
      rfl
  · rw [hO, hS]; rfl
  · rw [hO, hN]; exact (P.ns.sub_right es).symm
  · rw [hO, hE]; exact (P.es.sub_right es).symm
  · rw [hO, hI]; exact (P.cts.sub_right es).symm
  · rw [hO, hP]; exact (P.ps.sub_right es).symm
  · rw [hO, hQ]; exact (P.qs.sub_right es).symm
  · rw [hO, hDP]; exact (P.dps.sub_right es).symm
  · rw [hO, hDQ]; exact (P.dqs.sub_right es).symm
  · rw [hO, hQI]; exact (P.qis.sub_right es).symm
  · rw [hO, hS]; exact em_rs P
  · rw [hO, hA]; exact ((P.ks.sub_left ps).sub_right es).symm
  · rw [hN, hS]; exact P.ns.sub_right rss
  · rw [hE, hS]; exact P.es.sub_right rss
  · rw [hI, hS]; exact P.cts.sub_right rss
  · rw [hP, hS]; exact P.ps.sub_right rss
  · rw [hQ, hS]; exact P.qs.sub_right rss
  · rw [hDP, hS]; exact P.dps.sub_right rss
  · rw [hDQ, hS]; exact P.dqs.sub_right rss
  · rw [hQI, hS]; exact P.qis.sub_right rss
  · rw [hS, hA]; exact ((P.ks.sub_left ps).sub_right rss).symm
  · rw [hK, hO]; exact (P.ks.sub_left kD').sub_right es
  · rw [hK, hN]; exact P.kn.sub_left kD'
  · rw [hK, hE]; exact P.ke.sub_left kD'
  · rw [hK, hI]; exact P.kct.sub_left kD'
  · rw [hK, hP]; exact P.kp.sub_left kD'
  · rw [hK, hQ]; exact P.kq.sub_left kD'
  · rw [hK, hDP]; exact P.kdp.sub_left kD'
  · rw [hK, hDQ]; exact P.kdq.sub_left kD'
  · rw [hK, hQI]; exact P.kqi.sub_left kD'
  · rw [hK, hS]; exact (P.ks.sub_left kD').sub_right rss
  · rw [hK, hA]; exact ka
  · rw [g3, g4]; show (stackArg s 13).toNat + _ ≤ _; have := P.wsc; have := scLen P; unfold oRsa at *; omega_using [hk, wS]
  · rw [g5, g6]; exact P.wn
  · rw [g7, g8]; exact P.we
  · rw [g9, g10, ← P.oc]; exact P.wct
  · rw [sa 0 (by decide), s1]; exact P.wp
  · rw [sa 2 (by decide), s3]; exact P.wq
  · rw [sa 4 (by decide), s5]; exact P.wdp
  · rw [sa 6 (by decide), s7]; exact P.wdq
  · rw [sa 8 (by decide), s9]; exact P.wqi
  · rw [sa 10 (by decide), s11, w11]; simp only [psa]; rw [wS]; have := P.wsc; unfold oRsa; omega_using [hl, this]
  · rw [g6]; exact hk1
  · rw [g6]; exact hk
  · rw [g4, g6]
  · rw [g10, g6]
  · rw [g8]; exact P.e1
  · rw [g8, g6]; exact P.e2
  · rw [s1]; exact P.p1
  · rw [s1, g6]; exact P.p2
  · rw [s3]; exact P.q1
  · rw [s3, g6]; exact P.q2
  · rw [s5, s1]; exact P.h4
  · rw [s9, s1]; exact P.h8
  · rw [s7, s3]; exact P.h6
  · rw [g6, s11, w11]; have := P.hs; unfold Spec.RsaPss.scratchWords at this; omega_using [this]

end

end VG.Proof.RsaOaep.PPC64LE.Dec

end

end


/-!
# RSAES-OAEP decryption on PPC64LE: the private operation

Untrusted: everything here is checked by Lean. `priv_ok`: the private
operation's frame, its arguments, the call of `vg_rsa_private_checked` and
its result zero-extended into `r20` leave `EM` (or zeros) at `scratch` and
the outcome's code (`rcOf`) in `r20`, and the state `Base` needs for the
decoding (`AfterPriv`), with memory from after the call as the entry's.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE.Dec

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE VG.Impl.RsaOaep.PPC64LE.Dec
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep wp_lsrw wp_nil)

/-- RSADP checked against `e`, of the entry's buffers. -/
def privO (s : State) : Spec.Rsa.Outcome :=
  Spec.Rsa.privateChecked (Spec.Rsa.bytesAt s.mem (s.gpr .r6) (kk s))
    (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat) (Spec.Rsa.bytesAt s.mem (stackArg s 11) (kk s))
    (Spec.Rsa.bytesAt s.mem (s.gpr .r10) (stackArg s 0).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 1) (stackArg s 2).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 3) (stackArg s 0).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 5) (stackArg s 2).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 7) (stackArg s 0).toNat)

/-- The result's code: 1, 0 or 2. -/
def rcOf : Spec.Rsa.Outcome → Nat
  | .ok _ => 1
  | .invalid => 0
  | .fault => 2

/-- What it writes to `EM`'s place. -/
def emOf (k : Nat) : Spec.Rsa.Outcome → List Byte
  | .ok y => y
  | _ => List.replicate k 0

/-- The entry state with memory `m`, as `Base` takes it for the decoding. -/
abbrev withMem (s : State) (m : Mem) : State := { s with mem := m }

/-- After the private operation. -/
structure AfterPriv (s v : State) : Prop where
  base : Base (SD s) (VD s (rcOf (privO s))) (withMem s v.mem) v
  mem : Frame [kD s, scR s] s.mem v.mem
  em : Spec.Rsa.bytesAt v.mem (Sd s) (kk s) = emOf (kk s) (privO s)

theorem rcOf_le (o : Spec.Rsa.Outcome) : rcOf o ≤ 2 := by cases o <;> simp [rcOf]

/-- The outcome, from `writtenOutcome`. -/
theorem of_written {m : Mem} {p : Addr} {k : Nat} {r : BitVec 32} {o : Spec.Rsa.Outcome}
    (h : Spec.Rsa.writtenOutcome m p k r o) : r = BitVec.ofNat 32 (rcOf o) ∧ Spec.Rsa.bytesAt m p k = emOf k o := by
  cases o with
  | ok y => exact ⟨h.1, h.2⟩
  | invalid => exact ⟨h.1, h.2⟩
  | fault => exact ⟨h.1, h.2⟩

theorem priv_sdepth : sdepth Impl.Rsa.PPC64LE.Priv.code = Impl.Rsa.PPC64LE.Priv.frameBytes := by decide +kernel
theorem privP_sdepth : sdepth Impl.Rsa.PPC64LE.Priv.codeP = Impl.Rsa.PPC64LE.Priv.frameBytes := by decide +kernel

section
variable {pc : Bool} {s : State} (P : PreD pc s)
include P

theorem cov_sc {d n : Nat} (h : d + n ≤ (stackArg s 14).toNat * 8) :
    Covers [⟨Sd s + BitVec.ofNat 64 d, n⟩] s.wr :=
  Covers.of_sub fun r hr => by
    rw [List.mem_singleton.mp hr, P.hwr]
    exact ⟨scR s, by simp, d, rfl, h⟩

theorem call_covers {t : State} (A : AtPriv pc s t) :
    Covers (callRd pc s ++ callWr s) (t.rd ++ t.wr) ∧ Covers (callWr s) t.wr := by
  obtain hl : 1024 ≤ (stackArg s 14).toNat := by
    have := P.hs; unfold Spec.RsaPss.scratchWords Spec.Rsa.scratchWords at this; omega_using [this]
  obtain hw : Covers (callWr s) t.wr := by
    rw [A.wr]
    refine Covers.pair ?_ ?_
    · have := cov_sc P (d := 0) (n := kk s) (by have := scLen P; have := P.k2; unfold kk oRsa at *; omega_using [hl, this])
      rw [BitVec.add_zero] at this
      exact fun a n hi => let ⟨r, hr, hc⟩ := this a n hi; ⟨r, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr), hc⟩
    · have := cov_sc P (d := oRsa) (n := ((stackArg s 14).toNat - 1024) * 8) (by unfold oRsa; omega_using [hl])
      exact fun a n hi => let ⟨r, hr, hc⟩ := this a n hi; ⟨r, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr), hc⟩
  refine ⟨Covers.append_left (Covers.of_forall fun r hr => ?_) (Covers.right hw), hw⟩
  rw [A.rd, A.wr, P.hrd]
  obtain hct : (⟨stackArg s 11, kk s⟩ : Region) = ctR s := by simp only [ctR, kk, P.oc]
  obtain hpsa : Covers [psaR pc s] (rdL pc s ++ ⟨pb s + BitVec.ofNat 64 32, 176⟩ :: fr s :: s.wr) :=
    Covers.right (Covers.of_sub fun r hr => by
      rw [List.mem_singleton.mp hr]
      refine ⟨⟨pb s + BitVec.ofNat 64 32, 176⟩, List.mem_cons_self .., 64, ?_, ?_⟩
      · show pb s + BitVec.ofNat 64 96 = pb s + BitVec.ofNat 64 32 + BitVec.ofNat 64 64
        rw [Offset.add_add]
      · show 64 + (if pc then 112 else 96) ≤ 176
        cases pc <;> decide)
  simp only [callRd, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with ((rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | hr) | rfl
  rotate_left 8
  · cases pc
    · simp at hr
    · simp only [↓reduceIte, List.mem_singleton] at hr
      subst hr
      exact Covers.left (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp)
  · exact hpsa
  · exact Covers.left (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp)
  · exact Covers.left (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp)
  · exact Covers.left (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr, hct]; simp)
  · exact Covers.left (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp)
  · exact Covers.left (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp)
  · exact Covers.left (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp)
  · exact Covers.left (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp)
  · exact Covers.left (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp)

omit P in
/-- The caller's buffers at the call are as on entry. -/
theorem bytes_at {t : State} (A : AtPriv pc s t) {R : Region} (hd : (kD s).Disjoint R) (hl : R.len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt t.mem R.base R.len = Spec.Rsa.bytesAt s.mem R.base R.len := by
  simp only [Spec.Rsa.bytesAt]
  exact List.map_congr_left fun i hi => A.mem.bytes (R := R) (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact hd.symm) hl (List.mem_range.mp hi)

omit P in
theorem fb_base (s : State) : fb s = (s.sp - BitVec.ofNat 64 stackBytes) + BitVec.ofNat 64 (stackBytes - frameBytes) := by
  rw [← Offset.sub_sub_eq, Offset.ofNat_sub_ofNat (by decide)]; rfl

/-- The slots of our frame and what the call writes. -/
theorem slot_dis {d : Nat} (hd : d + 8 ≤ frameBytes) :
    ∀ r ∈ callWr s ++ [below (pb s) Impl.Rsa.PPC64LE.Priv.frameBytes],
      Region.Disjoint ⟨fb s + BitVec.ofNat 64 d, 8⟩ r := by
  obtain hk : Region.Sub ⟨fb s + BitVec.ofNat 64 d, 8⟩ (kD s) := by
    rw [fb_base, Offset.add_add]; exact Offset.sub_base _ (by unfold stackBytes frameBytes at *; omega_using [hd])
  intro r hr
  simp only [callWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (P.ks.sub_left hk).sub_right (em_sub P)
  · exact (P.ks.sub_left hk).sub_right (rs_sub P)
  · have e : below (pb s) Impl.Rsa.PPC64LE.Priv.frameBytes =
        ⟨(s.sp - BitVec.ofNat 64 stackBytes) + BitVec.ofNat 64 0, Impl.Rsa.PPC64LE.Priv.frameBytes⟩ := by
      simp only [below, pb_base, BitVec.add_sub_cancel, BitVec.add_zero]
    rw [e, fb_base, Offset.add_add]
    exact Offset.disjoint _ (.inr (by unfold stackBytes frameBytes privBytes Impl.Rsa.PPC64LE.Priv.frameBytes; omega_using []))
      (by unfold stackBytes frameBytes privBytes Impl.Rsa.PPC64LE.Priv.frameBytes at *; omega_using [hd]) (by decide)

/-- With `pc`, the precondition `vg_rsa_private_checked_precomputed` adds. -/
theorem preX_at (X : PreXD s) {t : State} (A : AtPriv true s t) : Rsa.PPC64LE.Priv.PreX (callE true s t) := by
  obtain sa := fun i (hi : i < 14) => callE_stackArg A (i := i) hi
  have hsp : (callE true s t).sp = pb s := A.sp
  obtain hpbt := pb_toNat P
  have sp2 := P.sp2
  obtain hPre : Rsa.PPC64LE.Priv.preR (callE true s t) = preR s := by
    simp only [Rsa.PPC64LE.Priv.preR, sa 12 (by decide), sa 13 (by decide), psa]
  obtain hO : Rsa.PPC64LE.Priv.oR (callE true s t) = emR s := by
    simp only [Rsa.PPC64LE.Priv.oR, callE_gpr (pc := true) s t (r := .r3), callE_gpr (pc := true) s t (r := .r4),
      A.r3, A.r4, emR, kk]
  obtain hl : 1024 ≤ (stackArg s 14).toNat := by
    have := P.hs; unfold Spec.RsaPss.scratchWords Spec.Rsa.scratchWords at this; omega_using [this]
  obtain w11 : (BitVec.ofNat 64 ((stackArg s 14).toNat - 1024)).toNat = (stackArg s 14).toNat - 1024 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := (stackArg s 14).isLt; omega_using [])]
  obtain hS : Rsa.PPC64LE.Priv.sR (callE true s t) = rsR s := by
    simp only [Rsa.PPC64LE.Priv.sR, sa 10 (by decide), sa 11 (by decide), psa, w11]
  obtain hK : Rsa.PPC64LE.Priv.kR (callE true s t) = ⟨s.sp - BitVec.ofNat 64 stackBytes,
      Impl.Rsa.PPC64LE.Priv.frameBytes⟩ := by
    simp only [Rsa.PPC64LE.Priv.kR, Rsa.PPC64LE.Priv.fb, hsp, pb_base, BitVec.add_sub_cancel]
  obtain kD' : Region.Sub ⟨s.sp - BitVec.ofNat 64 stackBytes, Impl.Rsa.PPC64LE.Priv.frameBytes⟩ (kD s) := by
    have := Offset.sub_base (s.sp - BitVec.ofNat 64 stackBytes) (d := 0) (n := Impl.Rsa.PPC64LE.Priv.frameBytes)
      (k := stackBytes) (by decide)
    rwa [BitVec.add_zero] at this
  refine ⟨by rw [hO, hPre]; exact X.sP.sub_left (em_sub P), by rw [hS, hPre]; exact X.sP.sub_left (rs_sub P),
    by rw [hK, hPre]; exact X.kP.sub_left kD', ?_, ?_, ?_, ?_⟩
  · rw [sa 12 (by decide), sa 13 (by decide)]; exact X.wP
  · rw [sa 13 (by decide), sa 1 (by decide), sa 3 (by decide), callE_gpr (pc := true) s t (r := .r6), A.r6]
    exact X.pl
  · rw [hsp, hpbt]; omega_using []
  · have hb := fun {p : Addr} {len : Nat} (hd : (kD s).Disjoint ⟨p, len⟩) (hl : len ≤ 2 ^ 64) =>
      bytes_at A (R := ⟨p, len⟩) hd hl
    obtain hw := VG.Proof.Rsa.PPC64LE.Priv.words_of_frame A.mem (p := stackArg s 17) (n := (stackArg s 18).toNat)
      (fun r hr => by rw [List.mem_singleton.mp hr, Nat.mul_comm]; exact X.kP.symm) (by have := X.wP; omega_using [this])
    simp only [Rsa.PPC64LE.Priv.PreHyp, State.withRegions_mem, State.callEntry_mem,
      callE_gpr (pc := true) s t (r := .r5), callE_gpr (pc := true) s t (r := .r6), A.r5, A.r6, sa 0 (by decide),
      sa 1 (by decide), sa 2 (by decide), sa 3 (by decide), sa 12 (by decide), sa 13 (by decide), psa, hw]
    rw [hb P.kn (by have := P.wn; omega_using []), hb P.kp (by have := P.wp; omega_using []), hb P.kq (by have := P.wq; omega_using [])]
    exact X.hyp

/-- The call of `vg_rsa_private_checked`, or with `pc` of
`vg_rsa_private_checked_precomputed`. -/
theorem call_priv (X : pc = true → PreXD s) {u : State} (A : AtPriv pc s u) :
    WP isa (privCall pc) u fun v => v.rd = u.rd ∧ v.wr = u.wr ∧ v.sp = u.sp ∧
      Frame (callWr s ++ [below (pb s) Impl.Rsa.PPC64LE.Priv.frameBytes]) u.mem v.mem ∧
      (∀ r ∈ preserved, v.gpr r = u.gpr r) ∧
      Rsa.PPC64LE.Priv.fnPost (callE pc s u) (v.withRegions (callRd pc s) (callWr s)) := by
  obtain ⟨hc, hw⟩ := call_covers P A
  cases pc with
  | false =>
    refine WP.callAny (k := Rsa.PPC64LE.Priv.fnContract) Rsa.PPC64LE.Priv.code_correct
      (Rsa.PPC64LE.Priv.pre_of_preP (preP_at P A)) hc hw (fun v hrd hwr hsp hf hpres hpost => ?_)
      (by rw [priv_sdepth]; decide)
    rw [priv_sdepth, A.sp] at hf
    exact ⟨hrd, hwr, hsp, hf, hpres, hpost⟩
  | true =>
    refine WP.callAny (k := Rsa.PPC64LE.Priv.fnContractP) Rsa.PPC64LE.Priv.codeP_correct
      (Rsa.PPC64LE.Priv.pre_of_prePX (preP_at P A) (preX_at P (X rfl) A)) hc hw
      (fun v hrd hwr hsp hf hpres hpost => ?_) (by rw [privP_sdepth]; decide)
    rw [privP_sdepth, A.sp] at hf
    exact ⟨hrd, hwr, hsp, hf, hpres, hpost⟩

/-- The private operation's frame, with the stack pointer after it. -/
theorem privF_ok (X : pc = true → PreXD s) {t : State} (E : Entered s t) :
    WP isa (.frame (.alloc privBytes) (.seq (.block (privArgs ++ preArgs pc)) (privCall pc)) (.free privBytes)) t
      fun w => w.sp = fb s ∧ WP isa (.block [.lsr .w .r20 .r3 0]) w (AfterPriv s) := by
  have hsp : t.sp = fb s := E.sv.sp
  have hk := P.k2
  refine WP.alloc ⟨by decide, by decide, by decide⟩ (by
    rw [hsp]; have := P.sp1
    rw [fb, Offset.toNat_sub_ofNat, Nat.mod_eq_of_lt (a := frameBytes) (by decide)]
    rw [stackBytes_eq] at this; unfold frameBytes privBytes; omega_using [this]) ?_
  refine WP.seq (WP.mono (privArgsG_ok P E) fun u A => ?_)
  refine WP.mono (call_priv P X A) fun v ⟨hrd, hwr, hsp', hf, hpres, hpost⟩ mL _ fl => ?_
  -- Whatever the released frame's bytes hold: the saved slots, the scratch and the stack's other
  -- bytes lie apart from it.
  obtain fl' : Frame [PB s] v.mem mL := by rw [hsp] at fl; exact fl
  obtain pbSub : Region.Sub (PB s) (kD s) := by
    show Region.Sub ⟨pb s, privBytes⟩ _
    rw [pb_base]
    exact Offset.sub_base _ (by unfold stackBytes; omega_using [])
  obtain slotPB : ∀ {d : Nat}, d + 8 ≤ frameBytes →
      ∀ r ∈ [PB s], Region.Disjoint ⟨fb s + BitVec.ofNat 64 d, 8⟩ r := fun {d} hd r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    show Region.Disjoint _ ⟨pb s, privBytes⟩
    rw [pb_base, fb_base, Offset.add_add]
    exact Offset.disjoint _ (.inr (by unfold stackBytes; unfold frameBytes privBytes Impl.Rsa.PPC64LE.Priv.frameBytes at *; omega_using []))
      (by unfold stackBytes; unfold frameBytes privBytes Impl.Rsa.PPC64LE.Priv.frameBytes at *; omega_using [hd])
      (by unfold privBytes Impl.Rsa.PPC64LE.Priv.frameBytes; omega_using [])
  obtain fsp : (freed privBytes v).sp = fb s := by
    show v.sp + BitVec.ofNat 64 privBytes = fb s
    rw [hsp', A.sp, BitVec.sub_add_cancel]
  refine ⟨fsp, wp_lsrw fun w ow ew => wp_nil ?_⟩
  -- The outcome.
  obtain sa := fun i (hi : i < 12) => callE_stackArg A (i := i) (lt_nCall hi)
  simp only [Rsa.PPC64LE.Priv.fnPost, State.withRegions_mem, State.withRegions_gpr,
    State.callEntry_mem, callE_gpr (pc := pc) s u (r := .r3), callE_gpr (pc := pc) s u (r := .r5),
    callE_gpr (pc := pc) s u (r := .r6), callE_gpr (pc := pc) s u (r := .r7), callE_gpr (pc := pc) s u (r := .r8),
    callE_gpr (pc := pc) s u (r := .r9), A.r3, A.r5, A.r6, A.r7, A.r8,
    A.r9, sa 0 (by decide), sa 1 (by decide), sa 2 (by decide), sa 3 (by decide), sa 4 (by decide),
    sa 6 (by decide), sa 8 (by decide), psa] at hpost
  obtain hb := fun {p : Addr} {len : Nat} (hd : (kD s).Disjoint ⟨p, len⟩) (hl : len ≤ 2 ^ 64) =>
    bytes_at A (R := ⟨p, len⟩) hd hl
  rw [hb P.kn (by have := P.wn; omega_using []), hb P.ke (by have := P.we; omega_using []),
    hb (by have := P.kct; simp only [ctR, P.oc] at this; exact this) (by omega_using []),
    hb P.kp (by have := P.wp; omega_using []), hb P.kq (by have := P.wq; omega_using []),
    hb (by have := P.kdp; simp only [dpR, P.h4] at this; exact this) (by have := P.wdp; omega_using []),
    hb (by have := P.kdq; simp only [dqR, P.h6] at this; exact this) (by have := P.wdq; omega_using []),
    hb (by have := P.kqi; simp only [qiR, P.h8] at this; exact this) (by have := P.wqi; omega_using [])] at hpost
  change Spec.Rsa.writtenOutcome _ _ _ _ (privO s) at hpost
  obtain ⟨hr, hem⟩ := of_written hpost
  -- The state after the frame's release.
  obtain fwr : (freed privBytes v).wr = fr s :: s.wr := by
    show v.wr.tail = _; rw [hwr, A.wr]; rfl
  obtain wsp : w.sp = fb s := by rw [ow.sp]; exact fsp
  obtain wg : ∀ r, r ≠ .r20 → w.gpr r = v.gpr r := fun r hr' => ow.gpr r (by simpa using hr')
  have wm : w.mem = mL := ow.mem
  obtain pv : ∀ r ∈ preserved, r ≠ .r20 → w.gpr r = u.gpr r := fun r hr' h20 => (wg r h20).trans (hpres r hr')
  obtain r20 : w.gpr .r20 = BitVec.ofNat 64 (rcOf (privO s)) := by
    rw [ew]; show ((v.gpr .r3).setWidth 32 >>> 0).setWidth 64 = _
    rw [hr, BitVec.ushiftRight_zero]
    apply BitVec.eq_of_toNat_eq
    have := rcOf_le (privO s)
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (a := rcOf _) (by omega_using [this]), Nat.mod_eq_of_lt (a := rcOf _) (by omega_using [this])]
  obtain fm : Frame [kD s, scR s] s.mem w.mem := by
    rw [wm]
    refine Frame.trans ?_ (fl'.sub fun r hr => ⟨kD s, by simp, by simp only [List.mem_singleton] at hr; subst hr; exact pbSub⟩)
    refine (A.mem.mono fun r hr => by simp at hr ⊢; exact .inl hr).trans (hf.sub fun r hr => ?_)
    simp only [callWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨scR s, by simp, em_sub P⟩
    · exact ⟨scR s, by simp, rs_sub P⟩
    · refine ⟨kD s, by simp, ?_⟩
      have := Offset.sub_base (s.sp - BitVec.ofNat 64 stackBytes) (d := 0) (n := Impl.Rsa.PPC64LE.Priv.frameBytes)
        (k := stackBytes) (by decide)
      rw [BitVec.add_zero] at this
      simpa only [below, pb_base, BitVec.add_sub_cancel] using this
  obtain svs : Spill.Saved (fb s) s.gpr saved w.mem := by
    rw [wm]; exact (A.sv.frame hf fun p hp r hr =>
      slot_dis P (by have := saved_offs p hp; unfold oLr frameBytes at *; omega_using [this]) r hr).frame fl'
      fun p hp r hr => slotPB (by have := saved_offs p hp; unfold oLr frameBytes at *; omega_using [this]) r hr
  obtain lss : w.mem.readW (fb s + BitVec.ofNat 64 oLr) 64 = s.lr := by
    rw [wm, fl'.readW (Region.contains_self _ _) (slotPB (by decide)) (by decide),
      hf.readW (Region.contains_self _ _) (slot_dis P (by decide)) (by decide)]; exact A.ls
  refine ⟨⟨⟨wsp, by rw [ow.wr]; exact fwr, fun r hr => ?_, svs, lss⟩, by rw [ow.rd]; exact hrd.trans A.rd, ?_, ?_,
    Frame.refl _ _⟩, fm, by
      rw [wm, ← hem]
      exact List.map_congr_left fun i hi => lost_byte fl' (R := emR s)
        ((P.ks.sub_right (em_sub P)).symm.sub_right pbSub) (List.mem_range.mp hi)⟩
  · rw [pv r (by revert r; decide) (by revert r; decide)]; exact A.hi r hr
  · rw [pv .r14 (by decide) (by decide)]; exact A.r14
  · intro r hr
    simp only [fx, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [pv _ (by decide) (by decide)]; exact A.r15
    · rw [pv _ (by decide) (by decide)]; exact A.r16
    · rw [pv _ (by decide) (by decide)]; exact A.r17
    · rw [pv _ (by decide) (by decide)]; exact A.r18
    · rw [pv _ (by decide) (by decide)]; exact A.r19
    · exact r20
    · rw [pv _ (by decide) (by decide)]; exact A.keep _ (by decide)
    · rw [pv _ (by decide) (by decide)]; exact A.keep _ (by decide)
    · rw [pv _ (by decide) (by decide)]; exact A.keep _ (by decide)

theorem priv_ok (X : pc = true → PreXD s) {t : State} (E : Entered s t) : WP isa (priv pc) t (AfterPriv s) :=
  WP.seq (WP.mono (privF_ok P X E) fun _ h => h.2)

end

end VG.Proof.RsaOaep.PPC64LE.Dec
