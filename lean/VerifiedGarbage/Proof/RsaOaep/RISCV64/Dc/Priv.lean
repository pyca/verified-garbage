module

public import VerifiedGarbage.Proof.Rsa.RISCV64.PrivCall
public import VerifiedGarbage.Proof.Rsa.RISCV64.PrivPreCopy
public import VerifiedGarbage.Proof.Rsa.RISCV64.PrivPCT
public import VerifiedGarbage.Proof.Framework.RISCV64.Alloc
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
public import VerifiedGarbage.Proof.Rsa.RISCV64.PrivVerified
public import VerifiedGarbage.Proof.Framework.RISCV64.CallAny
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Spec.RsaOaep.Contract
public import VerifiedGarbage.Spec.RsaOaep.MdTables
public import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.RsaOaep.RISCV64.Base
public import VerifiedGarbage.Impl.RsaOaep.RISCV64.Decrypt

/-!
# RSAES-OAEP decryption on RISC-V: the private operation

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaOaep/PPC64LE/Dc/PrivArgs.lean`, `Dc/PrivPre.lean`,
`Dc/PrivCall.lean`), with the call as in RSASSA-PKCS1-v1_5 signing
(`Proof/RsaPkcs1Sig/RISCV64/Sign/Call.lean`). In the frame of `privBytes`
bytes below ours (`pb`), `privArgs` writes `vg_rsa_private_checked`'s
twelve stack arguments at its stack pointer (`psa`: `p`, our stack
arguments 0 to 8, the rest of `scratch` and its length in words) and sets
its registers (`AtPriv`); the call is narrowed to `n`, `e`, the ciphertext,
the private key and its stack arguments (`callRd`), and `EM`'s place and the
rest of `scratch` (`callWr`), where its precondition holds (`preP_at`);
`privF_ok`: it leaves `EM` (or zeros) at `scratch` and the outcome's code
(`rcOf`) in `s4`, and the state `Base` needs for the decoding
(`AfterPriv`), with memory from after the call as the entry's.
-/

@[expose] public section

/-!
## RSAES-OAEP decryption on RISC-V: the precondition and the entry

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaOaep/PPC64LE/Dc/Pre.lean`, `Dc/Entry.lean`): `PreD s`, the
contract's precondition (`Spec.RsaOaep.decryptMdTablesContract`, with the stack
of the frames and of `vg_rsa_private_checked`, `stackBytes`), by name
(`preD_of`), and what it says of the tables (`spec_tabD`); the working space `Sd s` and the values the decoding keeps in
`s1`–`s4` (`vD s rc`, with the private operation's result `rc` in `s4`),
both functions of the entry state `s` alone, as `Base` takes them; `fits`,
`Fits` for any state with `s`'s stack pointer and regions; and `entry_ok`:
the saves and the prologue leave our caller's registers and return address
in their slots and `s0`–`s3` holding `scratch`, `k`, `out` and `msg_len`
(`Entered`).
-/
namespace VG.Proof.RsaOaep.RISCV64.Dec

open VG VG.RISCV64
open VG.Impl.RsaOaep.RISCV64 (frameBytes oRsa save)
open VG.Impl.RsaOaep.RISCV64.Dec (privBytes prologue)
open VG.Proof.RsaOaep.RISCV64 (Base Fits SC off fx kR fb fr save_ok Saves fb_al stackArgAddr_eq)
open VG.Proof.RsaPkcs1Sig.RISCV64 (Only wp_ld wp_mov wp_addSp wp_nil)

theorem stackArgs_seventeen (s : State) :
    List.map (stackArg s) (List.range 17) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9, stackArg s 10,
      stackArg s 11, stackArg s 12, stackArg s 13, stackArg s 14, stackArg s 15, stackArg s 16] := rfl

/-- The stack the function uses: its frame (`frameBytes`), the private
operation's (`privBytes`) and that function's own. -/
def stackBytes (pc : Bool) : Nat := frameBytes + privBytes pc + Impl.Rsa.RISCV64.Priv.frameBytes

theorem stackBytes_eq : stackBytes false = 3472 := rfl
theorem stackBytes_true : stackBytes true = 3488 := rfl

theorem stackBytes_ge (pc : Bool) : 3472 ≤ stackBytes pc ∧ stackBytes pc ≤ 3488 := by cases pc <;> decide

/-! ## The buffers -/

abbrev oR (s : State) : Region := ⟨s.gpr .a0, (s.gpr .a1).toNat⟩
abbrev mlR (s : State) : Region := ⟨s.gpr .a2, 8⟩
abbrev nR (s : State) : Region := ⟨s.gpr .a3, (s.gpr .a4).toNat⟩
abbrev eR (s : State) : Region := ⟨s.gpr .a5, (s.gpr .a6).toNat⟩
abbrev pR (s : State) : Region := ⟨s.gpr .a7, (stackArg s 0).toNat⟩
abbrev qR (s : State) : Region := ⟨stackArg s 1, (stackArg s 2).toNat⟩
abbrev dpR (s : State) : Region := ⟨stackArg s 3, (stackArg s 4).toNat⟩
abbrev dqR (s : State) : Region := ⟨stackArg s 5, (stackArg s 6).toNat⟩
abbrev qiR (s : State) : Region := ⟨stackArg s 7, (stackArg s 8).toNat⟩
abbrev lR (s : State) : Region := ⟨stackArg s 9, (stackArg s 10).toNat⟩
abbrev ctR (s : State) : Region := ⟨stackArg s 11, (stackArg s 12).toNat⟩
abbrev scR (s : State) : Region := ⟨stackArg s 13, (stackArg s 14).toNat * 8⟩
abbrev tLR (s : State) : Region := Sig.tableRegion 64 (stackArg s 15) 11
abbrev tR (s : State) : Region := Sig.tableRegion 64 (stackArg s 16) 11
/-- The stack arguments: 17, or with `pc` (`vg_rsa_oaep_decrypt_precomputed`) 19. -/
abbrev aR (pc : Bool) (s : State) : Region := ⟨stackArgAddr s 0, if pc then 152 else 136⟩
/-- With `pc`, the key's precomputed values, `pre_len` words. -/
abbrev preR (s : State) : Region := ⟨stackArg s 17, (stackArg s 18).toNat * 8⟩

/-- The buffers the function reads. -/
abbrev rdD (pc : Bool) (s : State) : List Region :=
  [nR s, eR s, pR s, qR s, dpR s, dqR s, qiR s, lR s, ctR s] ++ (if pc then [preR s] else []) ++
    [tLR s, tR s, aR pc s]

/-- The stack the function uses. -/
abbrev kD (pc : Bool) (s : State) : Region := ⟨s.sp - BitVec.ofNat 64 (stackBytes pc), stackBytes pc⟩

/-- With `pc`, `pre` holds the key's precomputed values. -/
abbrev HypD (pc : Bool) (s : State) : Prop :=
  pc = true → Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .a3) (s.gpr .a4).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .a7) (stackArg s 0).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 1) (stackArg s 2).toNat) =
    some (Spec.Rsa.wordsAt s.mem (stackArg s 17) (stackArg s 18).toNat)

/-- What `vg_rsa_oaep_decrypt_precomputed`'s precondition adds: `pre`'s facts. -/
structure PreXD (s : State) : Prop where
  sP : (scR s).Disjoint (preR s)
  kP : (kD true s).Disjoint (preR s)
  wP : (stackArg s 17).toNat + (stackArg s 18).toNat * 8 ≤ 2 ^ 64
  pl : (stackArg s 18).toNat =
    Spec.Rsa.privatePrecomputedWords (s.gpr .a4).toNat (stackArg s 0).toNat (stackArg s 2).toNat
  alP : (stackArg s 17).toNat % 8 = 0
  hyp : HypD true s

/-- What the code needs of `decryptMdTablesContract.pre` (or with `pc`
`decryptPrecomputedMdTablesContract.pre`), by name. -/
structure PreD (pc : Bool) (s : State) : Prop where
  spal : s.sp.toNat % 16 = 0
  sp1 : stackBytes pc ≤ s.sp.toNat
  sp2 : s.sp.toNat + (if pc then 152 else 136) ≤ 2 ^ 64
  hrd : s.rd = rdD pc s
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
  ko : (kD pc s).Disjoint (oR s)
  kml : (kD pc s).Disjoint (mlR s)
  kn : (kD pc s).Disjoint (nR s)
  ke : (kD pc s).Disjoint (eR s)
  kp : (kD pc s).Disjoint (pR s)
  kq : (kD pc s).Disjoint (qR s)
  kdp : (kD pc s).Disjoint (dpR s)
  kdq : (kD pc s).Disjoint (dqR s)
  kqi : (kD pc s).Disjoint (qiR s)
  kl : (kD pc s).Disjoint (lR s)
  kct : (kD pc s).Disjoint (ctR s)
  ks : (kD pc s).Disjoint (scR s)
  ktl : (kD pc s).Disjoint (tLR s)
  kt : (kD pc s).Disjoint (tR s)
  ka : (kD pc s).Disjoint (aR pc s)
  wo : (s.gpr .a0).toNat + (s.gpr .a1).toNat ≤ 2 ^ 64
  wml : (s.gpr .a2).toNat + 8 ≤ 2 ^ 64
  wn : (s.gpr .a3).toNat + (s.gpr .a4).toNat ≤ 2 ^ 64
  we : (s.gpr .a5).toNat + (s.gpr .a6).toNat ≤ 2 ^ 64
  wp : (s.gpr .a7).toNat + (stackArg s 0).toNat ≤ 2 ^ 64
  wq : (stackArg s 1).toNat + (stackArg s 2).toNat ≤ 2 ^ 64
  wdp : (stackArg s 3).toNat + (stackArg s 4).toNat ≤ 2 ^ 64
  wdq : (stackArg s 5).toNat + (stackArg s 6).toNat ≤ 2 ^ 64
  wqi : (stackArg s 7).toNat + (stackArg s 8).toNat ≤ 2 ^ 64
  wl : (stackArg s 9).toNat + (stackArg s 10).toNat ≤ 2 ^ 64
  wct : (stackArg s 11).toNat + (stackArg s 12).toNat ≤ 2 ^ 64
  wsc : (stackArg s 13).toNat + (stackArg s 14).toNat * 8 ≤ 2 ^ 64
  wtl : (stackArg s 15).toNat + 88 ≤ 2 ^ 64
  wt : (stackArg s 16).toNat + 88 ≤ 2 ^ 64
  k1 : 64 ≤ (s.gpr .a4).toNat
  k2 : (s.gpr .a4).toNat ≤ 1024
  ok : (s.gpr .a1).toNat = (s.gpr .a4).toNat
  oc : (stackArg s 12).toNat = (s.gpr .a4).toNat
  e1 : 1 ≤ (s.gpr .a6).toNat
  e2 : (s.gpr .a6).toNat ≤ (s.gpr .a4).toNat
  p1 : 1 ≤ (stackArg s 0).toNat
  p2 : (stackArg s 0).toNat < (s.gpr .a4).toNat
  q1 : 1 ≤ (stackArg s 2).toNat
  q2 : (stackArg s 2).toNat < (s.gpr .a4).toNat
  h4 : (stackArg s 4).toNat = (stackArg s 0).toNat
  h8 : (stackArg s 8).toNat = (stackArg s 0).toNat
  h6 : (stackArg s 6).toNat = (stackArg s 2).toNat
  hs : Spec.RsaPss.scratchWords (s.gpr .a4).toNat ≤ (stackArg s 14).toNat
  alm : (s.gpr .a2).toNat % 8 = 0
  als : (stackArg s 13).toNat % 8 = 0
  altl : (stackArg s 15).toNat % 8 = 0
  alt : (stackArg s 16).toNat % 8 = 0
  /-- With `pc`, `pre`'s facts. -/
  px : pc = true → PreXD s

/-- The contract, with both hash functions each one of the tables `ts`, and
the stack of the frames and of `vg_rsa_private_checked`. -/
abbrev decSpec (ts : List FnTable) : Contract isa :=
  Spec.RsaOaep.decryptMdTablesContract (abi.withTables Spec.RsaOaep.decryptMdTablesSig [("hash", ts), ("mgf1", ts)])
    (stackBytes false)

/-- Unfolds the precondition at `h`. -/
macro "dec_pre" " at " h:ident : tactic => `(tactic| (
  have e : stackBytes false = 3471 + 1 := rfl
  unfold decSpec at $h:ident
  rw [e] at $h:ident
  sig_pre [Spec.RsaOaep.decryptMdTablesContract, Spec.RsaOaep.decryptMdTablesSig, Spec.RsaOaep.decryptSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Abi.withTables, Sig.wordIndex, abi, argRegs,
    stackArgs_seventeen, List.append_eq, List.range, List.range.loop, Spec.Rsa.lenValid] at $h:ident
  sig_pre [Spec.RsaOaep.decryptMdTablesContract, Spec.RsaOaep.decryptMdTablesSig, Spec.RsaOaep.decryptSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Abi.withTables, Sig.wordIndex, abi, argRegs,
    stackArgs_seventeen, List.append_eq, List.range, List.range.loop, Spec.Rsa.lenValid] at $h:ident
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left', Sig.pairFacts, List.filterMap_cons, List.filterMap_nil,
    Bool.cond_true, Bool.cond_false, Bool.true_or, Bool.false_or, List.cons_append, List.nil_append, Sig.conj,
    List.append_nil] at $h:ident))

theorem preD_of {ts : List FnTable} {s : State} (h : (decSpec ts).pre s) : PreD false s := by
  dec_pre at h
  obtain ⟨spal, sp1, sp2, -, -, -, hrd, hwr, oml, on, oe, op, oq, odp, odq, oqi, ol, oct, os, otl, ot, oa, mln, mle,
    mlp, mlq, mldp, mldq, mlqi, mll, mlct, mls, mltl, mlt, mla, ns, es, ps, qs, dps, dqs, qis, ls, cts, stl, st, sa,
    ko, kml, kn, ke, kp, kq, kdp, kdq, kqi, kl, kct, ks, ktl, kt, ka, wo, wml, wn, we, wp, wq, wdp, wdq, wqi, wl, wct,
    wsc, wtl, wt, k1, k2, ok, oc, e1, e2, p1, p2, q1, q2, h4, h8, h6, hs, alm, als, altl, alt⟩ := h
  exact ⟨spal, sp1, by show s.sp.toNat + 136 ≤ 2 ^ 64; omega_using [sp2], hrd, hwr, oml, on, oe, op, oq, odp, odq, oqi, ol, oct, os, otl, ot, oa, mln, mle, mlp,
    mlq, mldp, mldq, mlqi, mll, mlct, mls, mltl, mlt, mla, ns, es, ps, qs, dps, dqs, qis, ls, cts, stl, st, sa, ko, kml,
    kn, ke, kp, kq, kdp, kdq, kqi, kl, kct, ks, ktl, kt, ka, wo, wml, wn, we, wp, wq, wdp, wdq, wqi, wl, wct, wsc, wtl,
    wt, k1, k2, ok, oc, e1, e2, p1, p2, q1, q2, h4, h8, h6, hs, alm, als, altl, alt, nofun⟩

/-- The tables, as the contract gives them: each one of `ts`, the label's
hash function's at the stack argument 15 and MGF1's at 16, with the
functions of distinct names at distinct addresses. -/
theorem spec_tabD {ts : List FnTable} {s : State} (h : (decSpec ts).pre s) :
    (∃ T ∈ ts, Abi.tableHeld 64 s.mem (stackArg s 15) (FnTable.words isa s T)) ∧
      (∃ T ∈ ts, Abi.tableHeld 64 s.mem (stackArg s 16) (FnTable.words isa s T)) ∧
      ((ts.map (fun T : FnTable => T.fns)).flatten ++ (ts.map (fun T : FnTable => T.fns)).flatten).Pairwise
        (fun f g => f ≠ g → s.syms f ≠ s.syms g) := by
  dec_pre at h
  exact ⟨h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩

/-! ## The working space and the registers the decoding keeps -/

/-- The working space. -/
abbrev Sd (s : State) : Addr := stackArg s 13

/-- `k`. -/
abbrev kk (s : State) : Nat := (s.gpr .a4).toNat

/-- The values `Base` fixes in `s1`–`s4` once the private operation has
returned `rc`: `k`, `out`, `msg_len` and `rc`. -/
def vD (s : State) (rc : Nat) : Reg → BitVec 64
  | .s1 => s.gpr .a4
  | .s2 => s.gpr .a0
  | .s3 => s.gpr .a2
  | .s4 => BitVec.ofNat 64 rc
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
theorem kR_sub : Region.Sub (kR s) (kD pc s) :=
  below_sub (by have := stackBytes_ge pc; unfold Proof.RsaOaep.RISCV64.stackBytes; omega_using [this])
    (by have := stackBytes_ge pc; omega_using [this])

/-- `Fits` for any state with the entry's stack pointer and regions. -/
theorem fits {s' : State} (hsp : s'.sp = s.sp) (hwr : s'.wr = s.wr) : Fits (SD s) s' where
  sp1 := by rw [hsp]; have := P.sp1; have := stackBytes_ge pc; unfold Proof.RsaOaep.RISCV64.stackBytes; omega_arith
  sp16 := by rw [hsp]; exact P.spal
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

theorem Base.dk : t.gpr .s1 = s.gpr .a4 := h.vs .s1 (by decide)
theorem Base.dout : t.gpr .s2 = s.gpr .a0 := h.vs .s2 (by decide)
theorem Base.dml : t.gpr .s3 = s.gpr .a2 := h.vs .s3 (by decide)
theorem Base.drc : t.gpr .s4 = BitVec.ofNat 64 rc := h.vs .s4 (by decide)

end

/-! ## The entry -/

/-- The stack arguments are in `aR`. -/
theorem in_aR {pc : Bool} {s : State} {j : Nat} (hj : j < 17) : (aR pc s).Contains (stackArgAddr s j) 8 := by
  rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by split <;> omega_using [hj]) (by omega_using [hj])

/-- With `pc`, the stack arguments 17 and 18 too. -/
theorem in_aR19 {s : State} {j : Nat} (hj : j < 19) : (aR true s).Contains (stackArgAddr s j) 8 := by
  rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by simp only [↓reduceIte]; omega_using [hj]) (by omega_using [hj])

/-- After the saves and the prologue: our caller's registers and return
address in their slots, `s0`–`s3` holding `scratch`, `k`, `out` and
`msg_len`, and `a3`, `a5`–`a7` the entry's `n`, `e`, `e_len` and `p`. -/
structure Entered (s t : State) : Prop where
  sv : Saves s t
  rd : t.rd = s.rd
  s0 : t.gpr .s0 = Sd s
  s1 : t.gpr .s1 = s.gpr .a4
  s2 : t.gpr .s2 = s.gpr .a0
  s3 : t.gpr .s3 = s.gpr .a2
  args : ∀ r ∈ [Reg.a3, .a5, .a6, .a7], t.gpr r = s.gpr r
  mem : Frame [kR s] s.mem t.mem

section
variable {pc : Bool} {s : State} (P : PreD pc s)
include P

theorem arg_al {j : Nat} (hj : j < 17) : (stackArgAddr s j).toNat % 8 = 0 := by
  have := P.spal; have : s.sp.toNat + 136 ≤ 2 ^ 64 := by have := P.sp2; split at this <;> omega_using [this]
  have e : (stackArgAddr s j).toNat = s.sp.toNat + 8 * j := by
    simp only [stackArgAddr, BitVec.toNat_add, BitVec.toNat_ofNat]; omega_using [hj, this]
  rw [e]; omega_arith

omit P in
/-- With `pc`, the stack arguments 17 and 18 too. -/
theorem arg_al19 (P : PreD true s) {j : Nat} (hj : j < 19) : (stackArgAddr s j).toNat % 8 = 0 := by
  have := P.spal; have : s.sp.toNat + 152 ≤ 2 ^ 64 := P.sp2
  have e : (stackArgAddr s j).toNat = s.sp.toNat + 8 * j := by
    simp only [stackArgAddr, BitVec.toNat_add, BitVec.toNat_ofNat]; omega_using [hj, this]
  rw [e]; omega_arith

theorem fb_al8 : (fb s).toNat % 8 = 0 := by
  have := fb_al (fits P (s' := s) rfl rfl); omega_using [this]

/-- A load of our stack argument `j` through `t6`, the entry stack pointer,
with memory changed only in the stack and our part of the working space. -/
theorem wp_arg {t : State} {r : Reg} {j : Nat} {is : List Instr} {Q : State → Prop} (hj : j < 17)
    (h6 : t.gpr .t6 = s.sp) (hrd : t.rd = s.rd) (hm : Frame [kR s, SC (SD s) s] s.mem t.mem)
    (k : ∀ t', Only [r] t t' → t'.gpr r = stackArg s j → WP isa (.block is) t' Q)
    (ho : 8 * j < 2048 := by decide) :
    WP isa (.block (.load .d r .t6 (8 * j) :: is)) t Q := by
  refine wp_ld (a := stackArgAddr s j) (by rw [h6]; rfl) (arg_al P hj) ?_ (fun t' o e => k t' o ?_) ho
  · rw [hrd, P.hrd]; exact ⟨aR pc s, by cases pc <;> simp, in_aR hj⟩
  · rw [e, stackArg, hm.readW (in_aR hj) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (P.ka.sub_left kR_sub).symm
      · exact (P.sa.sub_left (sc_sub P)).symm) (by decide)]

theorem entry_ok : WP isa (.block (save ++ prologue)) (allocd frameBytes s) (Entered s) := by
  refine save_ok (u := allocd frameBytes s) rfl rfl (fb_al8 P) (Frame.refl _ _) (fun r _ => rfl)
    fun v kv h0 hm hsv => ?_
  have hrd : v.rd = s.rd := kv.rd
  have hsp : v.sp = fb s := kv.sp
  have hm2 : Frame [kR s, SC (SD s) s] s.mem v.mem := hm.mono fun r hr => by rw [List.mem_singleton.mp hr]; simp
  have gs : ∀ r ∈ [Reg.a0, .a2, .a3, .a4, .a5, .a6, .a7], v.gpr r = s.gpr r := fun r hr => by
    rw [kv.gpr r (by revert r; decide)]; rfl
  simp only [prologue, Impl.RsaOaep.RISCV64.argBase]
  refine wp_addSp fun v₁ o₁ e₁ => ?_
  have g6 : v₁.gpr .t6 = s.sp := by rw [e₁, hsp, BitVec.sub_add_cancel]
  refine wp_arg P (j := 13) (by decide) g6 (o₁.rd.trans hrd) (by rw [o₁.mem]; exact hm2) fun v₂ o₂ e₂ => ?_
  refine wp_mov fun v₃ o₃ e₃ => wp_mov fun v₄ o₄ e₄ => wp_mov fun w ow ew => wp_nil ?_
  have kw : Only [.t6, .s0, .s1, .s2, .s3] v w := (o₁.trans (o₂.trans (o₃.trans (o₄.trans ow)))).mono
  have a2 : ∀ r ∈ [Reg.a0, .a2, .a3, .a4, .a5, .a6, .a7], v₂.gpr r = s.gpr r := fun r hr => by
    rw [(o₁.trans o₂).get r (by revert r; decide), gs r hr]
  have a3 : ∀ r ∈ [Reg.a0, .a2, .a3, .a4, .a5, .a6, .a7], v₃.gpr r = s.gpr r := fun r hr => by
    rw [(o₁.trans (o₂.trans o₃)).get r (by revert r; decide), gs r hr]
  have a4 : ∀ r ∈ [Reg.a0, .a2, .a3, .a4, .a5, .a6, .a7], v₄.gpr r = s.gpr r := fun r hr => by
    rw [(o₁.trans (o₂.trans (o₃.trans o₄))).get r (by revert r; decide), gs r hr]
  refine ⟨⟨by rw [kw.sp, hsp], by rw [kw.wr, kv.wr]; rfl, by rw [kw.mem]; exact hsv⟩, by rw [kw.rd, hrd],
    by rw [ow.get .s0, o₄.get .s0, o₃.get .s0, e₂], ?_, ?_, ?_, fun r hr => ?_, ?_⟩
  · rw [ow.get .s1, o₄.get .s1, e₃, a2 .a4 (by decide)]
  · rw [ow.get .s2, e₄, a3 .a0 (by decide)]
  · rw [ew, a4 .a2 (by decide)]
  · rw [kw.gpr r (by revert r; decide), gs r (by revert r; decide)]
  · rw [kw.mem]; exact hm.mono fun r hr => by rw [List.mem_singleton.mp hr]; simp

end

end VG.Proof.RsaOaep.RISCV64.Dec


namespace VG.Proof.RsaOaep.RISCV64.Dec

open VG VG.RISCV64
open VG.Impl.RsaOaep.RISCV64 (frameBytes oRsa saved)
open VG.Impl.RsaOaep.RISCV64.Dec (privBytes privArgs privArgsM privTail copyArg privCall)
open VG.Proof.RsaOaep.RISCV64 (Base Fits SC off fx kR fb fr Saves stackArgAddr_eq)
open VG.Proof.RsaPkcs1Sig.RISCV64 (Only Kept MemTo wp_ld wp_sd wp_mov wp_li wp_add wp_addi wp_subi wp_sll wp_srl
  wp_addSp wp_nil)

/-! ## Addresses in the stack the function uses -/

/-- The base of the stack the function uses. -/
abbrev kb (pc : Bool) (s : State) : Addr := s.sp - BitVec.ofNat 64 (stackBytes pc)

/-- The base of the private operation's frame. -/
abbrev pb (pc : Bool) (s : State) : Addr := fb s - BitVec.ofNat 64 (privBytes pc)

/-- The private operation's frame. -/
abbrev PB (pc : Bool) (s : State) : Region := ⟨pb pc s, privBytes pc⟩

/-- Its stack argument `i`, as `privArgs` writes it (12 and 13, `pre` and
`pre_len`, only with `pc`). -/
def psa (s : State) : Nat → BitVec 64
  | 0 => s.gpr .a7
  | 10 => Sd s + BitVec.ofNat 64 oRsa
  | 11 => BitVec.ofNat 64 ((stackArg s 14).toNat - 1024)
  | 12 => stackArg s 17
  | 13 => stackArg s 18
  | i + 1 => stackArg s i

section
variable {pc : Bool} {s : State} (P : PreD pc s)
include P

theorem kb_add {d : Nat} (hd : d ≤ stackBytes pc) :
    kb pc s + BitVec.ofNat 64 d = s.sp - BitVec.ofNat 64 (stackBytes pc - d) := by
  have := P.sp1; have := stackBytes_ge pc
  apply BitVec.eq_of_toNat_eq
  simp only [kb, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat] at *
  omega_using [hd]

omit P in
theorem privBytes_rng (pc : Bool) : 96 ≤ privBytes pc ∧ privBytes pc ≤ 112 := by cases pc <;> decide

omit P in
theorem stackBytes_split (pc : Bool) :
    stackBytes pc = frameBytes + privBytes pc + Impl.Rsa.RISCV64.Priv.frameBytes := rfl

theorem fb_kb : fb s = kb pc s + BitVec.ofNat 64 (privBytes pc + Impl.Rsa.RISCV64.Priv.frameBytes) := by
  rw [kb_add P (by rw [stackBytes_split]; omega_using [])]
  have e : stackBytes pc - (privBytes pc + Impl.Rsa.RISCV64.Priv.frameBytes) = frameBytes := by
    rw [stackBytes_split]; omega_using []
  rw [e]

theorem pb_kb : pb pc s = kb pc s + BitVec.ofNat 64 3248 := by
  rw [kb_add P (by rw [stackBytes_split]; unfold Impl.Rsa.RISCV64.Priv.frameBytes; omega_using [])]
  have := P.sp1; have := privBytes_rng pc
  rw [stackBytes_split] at *
  apply BitVec.eq_of_toNat_eq
  simp only [pb, fb, BitVec.toNat_sub, BitVec.toNat_ofNat, frameBytes, Impl.Rsa.RISCV64.Priv.frameBytes] at *
  omega_using []

theorem kb_toNat : (kb pc s).toNat = s.sp.toNat - stackBytes pc := by
  have := P.sp1; have := stackBytes_ge pc
  simp only [kb, BitVec.toNat_sub, BitVec.toNat_ofNat] at *
  omega_arith

omit P in
/-- A range at `kb pc s + d` in the stack the function uses. -/
theorem kb_sub {d n : Nat} (h : d + n ≤ stackBytes pc) : Region.Sub ⟨kb pc s + BitVec.ofNat 64 d, n⟩ (kD pc s) :=
  Offset.sub_base _ h

omit P in theorem kb_contains {d n : Nat} (h : d + n ≤ stackBytes pc) :
    (kD pc s).Contains (kb pc s + BitVec.ofNat 64 d) n :=
  Offset.contains_base _ h (by have := stackBytes_ge pc; omega_using [h, this])

theorem pb_al : (pb pc s).toNat % 16 = 0 := by
  have := P.sp1; have := P.spal; have := privBytes_rng pc
  have h16 : privBytes pc % 16 = 0 := by cases pc <;> decide
  rw [stackBytes_split] at *
  simp only [pb, fb, BitVec.toNat_sub, BitVec.toNat_ofNat, frameBytes, Impl.Rsa.RISCV64.Priv.frameBytes] at *
  omega_arith

theorem pb_off_al {d : Nat} (hd : d % 8 = 0) : (pb pc s + BitVec.ofNat 64 d).toNat % 8 = 0 := by
  have := pb_al P; have := s.sp.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at *
  omega_arith

/-- A range of the private operation's frame, in the stack the function uses. -/
theorem pb_sub {d n : Nat} (h : d + n ≤ privBytes pc) :
    Region.Sub ⟨pb pc s + BitVec.ofNat 64 d, n⟩ (kD pc s) := by
  rw [pb_kb P, Offset.add_add]
  exact kb_sub (by rw [stackBytes_split]; unfold frameBytes Impl.Rsa.RISCV64.Priv.frameBytes; omega_using [h])

theorem PB_sub : Region.Sub (PB pc s) (kD pc s) := by
  have := pb_sub P (d := 0) (n := privBytes pc) (by omega_using []); rwa [BitVec.add_zero] at this

omit P in theorem kR_subD : Region.Sub (kR s) (kD pc s) := kR_sub

end

/-! ## The arguments -/

/-- In the private operation's frame, after `privArgsM`. -/
structure AtPrivM (pc : Bool) (s t : State) : Prop where
  sp : t.sp = pb pc s
  rd : t.rd = s.rd
  wr : t.wr = PB pc s :: fr s :: s.wr
  mem : Frame [kD pc s] s.mem t.mem
  sv : Spill.Saved (fb s) s.gpr saved t.mem
  s0 : t.gpr .s0 = Sd s
  s1 : t.gpr .s1 = s.gpr .a4
  s2 : t.gpr .s2 = s.gpr .a0
  s3 : t.gpr .s3 = s.gpr .a2
  a0 : t.gpr .a0 = Sd s
  a1 : t.gpr .a1 = s.gpr .a4
  a2 : t.gpr .a2 = s.gpr .a3
  a3 : t.gpr .a3 = s.gpr .a4
  a4 : t.gpr .a4 = s.gpr .a5
  a5 : t.gpr .a5 = s.gpr .a6
  a6 : t.gpr .a6 = stackArg s 11
  a7 : t.gpr .a7 = s.gpr .a4
  psa : ∀ i < 12, t.mem.readW (pb pc s + BitVec.ofNat 64 (8 * i)) 64 = psa s i
  t6 : t.gpr .t6 = s.sp
  t0 : t.gpr .t0 = pb pc s

/-- At the call: with `pc`, `pre` and `pre_len` in its stack arguments 12 and
13 too. -/
structure AtPriv (pc : Bool) (s t : State) : Prop extends AtPrivM pc s t where
  psx : pc = true → ∀ i, 12 ≤ i → i < 14 →
    t.mem.readW (pb pc s + BitVec.ofNat 64 (8 * i)) 64 = VG.Proof.RsaOaep.RISCV64.Dec.psa s i

/-- After the first `n` copies of our stack arguments, from `w`. -/
structure Cp (pc : Bool) (s w : State) (n : Nat) (t : State) : Prop where
  keep : Kept [.t1] w t
  mem : Frame [PB pc s] w.mem t.mem
  z : t.mem.readW (pb pc s + BitVec.ofNat 64 0) 64 = w.mem.readW (pb pc s + BitVec.ofNat 64 0) 64
  got : ∀ j < n, t.mem.readW (pb pc s + BitVec.ofNat 64 (8 * (j + 1))) 64 = stackArg s j

section
variable {pc : Bool} {s : State} (P : PreD pc s)
include P

/-- A load of our stack argument `j` through `t6`, with memory changed only
in the stack the function uses. -/
theorem wp_argD {t : State} {r : Reg} {j : Nat} {is : List Instr} {Q : State → Prop} (hj : j < 17)
    (h6 : t.gpr .t6 = s.sp) (hrd : t.rd = s.rd) (hm : Frame [kD pc s] s.mem t.mem)
    (k : ∀ t', Only [r] t t' → t'.gpr r = stackArg s j → WP isa (.block is) t' Q)
    (ho : 8 * j < 2048 := by decide) :
    WP isa (.block (.load .d r .t6 (8 * j) :: is)) t Q := by
  refine wp_ld (a := stackArgAddr s j) (by rw [h6]; rfl) (arg_al P hj) ?_ (fun t' o e => k t' o ?_) ho
  · rw [hrd, P.hrd]; exact ⟨aR pc s, by cases pc <;> simp, in_aR hj⟩
  · rw [e, stackArg, hm.readW (in_aR hj) (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact P.ka.symm) (by decide)]

omit P in theorem pb_in {d : Nat} (h : d + 8 ≤ privBytes pc) {rs : List Region} :
    InRegions (PB pc s :: rs) (pb pc s + BitVec.ofNat 64 d) 8 :=
  ⟨_, List.mem_cons_self .., Offset.contains_base _ h (by have := privBytes_rng pc; omega_using [h, this])⟩

theorem copy_step {w : State} (hw0 : w.gpr .t0 = pb pc s) (hw6 : w.gpr .t6 = s.sp) (hrd : w.rd = s.rd)
    (hwr : w.wr = PB pc s :: fr s :: s.wr) (hm : Frame [kD pc s] s.mem w.mem) {n : Nat} (hn : n < 9) {t : State}
    (hc : Cp pc s w n t) : WP isa (.block (copyArg n)) t (Cp pc s w (n + 1)) := by
  have hmt : Frame [kD pc s] s.mem t.mem := hm.trans (hc.mem.sub fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_singleton_self _, PB_sub P⟩)
  unfold copyArg
  refine wp_argD P (j := n) (by omega_using [hn]) (by rw [hc.keep.get .t6, hw6]) (hc.keep.rd.trans hrd) hmt
    (fun t₁ o₁ e₁ => ?_) (by omega_using [hn])
  refine wp_sd (a := pb pc s + BitVec.ofNat 64 (8 * (n + 1))) (by rw [o₁.get .t0, hc.keep.get .t0, hw0])
    (pb_off_al P (by omega_using []))
    (by rw [o₁.wr, hc.keep.wr, hwr]; exact pb_in (by have := privBytes_rng pc; omega_using [hn, this])) (fun t₂ m₂ => wp_nil ?_)
    (by omega_using [hn])
  rw [e₁] at m₂
  refine ⟨(hc.keep.trans (o₁.keep.trans m₂.keep)).mono, ?_, ?_, fun j hj => ?_⟩
  · rw [m₂.mem, o₁.mem]
    exact hc.mem.writeW (List.mem_singleton_self _) _ (Offset.contains_base (pb pc s) (d := 8 * (n + 1)) (n := 8)
      (k := privBytes pc) (by have := privBytes_rng pc; omega_using [hn, this]) (by omega_using [hn]))
  · rw [m₂.mem, o₁.mem, Mem.readW_writeW_sep (Offset.sep _ (.inl (by omega_using [])) (by omega_using []) (by omega_using [hn])) (by decide)]
    exact hc.z
  · rw [m₂.mem, o₁.mem]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [Mem.readW_writeW_sep (Offset.sep _ (.inl (by omega_using [hj])) (by omega_arith) (by omega_using [hn])) (by decide)]
      exact hc.got j hj
    · rw [Mem.readW_writeW_self64]

theorem copies_ok {w : State} (hw0 : w.gpr .t0 = pb pc s) (hw6 : w.gpr .t6 = s.sp) (hrd : w.rd = s.rd)
    (hwr : w.wr = PB pc s :: fr s :: s.wr) (hm : Frame [kD pc s] s.mem w.mem) :
    WP isa (.block ((List.range 9).flatMap copyArg)) w (Cp pc s w 9) :=
  wp_range_flatMap (M := isa) (Cp pc s w) (fun _ _ hn hc => copy_step P hw0 hw6 hrd hwr hm hn hc) 9
    (Nat.le_refl _) w ⟨Kept.refl _ _, Frame.refl _ _, rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩


/-- Our stack arguments' base, from the private operation's frame. -/
theorem pb_top : pb pc s + BitVec.ofNat 64 (privBytes pc + frameBytes) = s.sp := by
  have := P.sp1; have := privBytes_rng pc
  rw [stackBytes_split] at *
  apply BitVec.eq_of_toNat_eq
  simp only [pb, fb, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, frameBytes,
    Impl.Rsa.RISCV64.Priv.frameBytes] at *
  omega_using []

/-- The private operation's part of `scratch`, in words. -/
theorem sl_sub : stackArg s 14 - BitVec.ofNat 64 1024 = BitVec.ofNat 64 ((stackArg s 14).toNat - 1024) := by
  have := scLen P; unfold oRsa at this
  have := (stackArg s 14).isLt
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega_arith

/-- Our frame's slots, apart from the private operation's frame. -/
theorem slots_PB : Region.Disjoint ⟨fb s + BitVec.ofNat 64 Proof.RsaOaep.RISCV64.oSv, frameBytes -
    Proof.RsaOaep.RISCV64.oSv⟩ (PB pc s) := by
  show Region.Disjoint _ ⟨pb pc s, privBytes pc⟩
  have := privBytes_rng pc
  rw [fb_kb P, Offset.add_add, pb_kb P]
  exact Offset.disjoint _ (.inr (by unfold Impl.Rsa.RISCV64.Priv.frameBytes; omega_using []))
    (by unfold frameBytes Impl.Rsa.RISCV64.Priv.frameBytes Proof.RsaOaep.RISCV64.oSv; omega_using [this]) (by omega_using [this])

theorem privArgsM_ok {t : State} (E : Entered s t) :
    WP isa (.block (privArgsM pc)) (allocd (privBytes pc) t) (AtPrivM pc s) := by
  have hsp : t.sp = fb s := E.sv.sp
  have usp : (allocd (privBytes pc) t).sp = pb pc s := by show t.sp - _ = _; rw [hsp]
  have uwr : (allocd (privBytes pc) t).wr = PB pc s :: fr s :: s.wr := by
    show (⟨t.sp - _, _⟩ : Region) :: t.wr = _; rw [hsp, E.sv.wr]
  have urd : (allocd (privBytes pc) t).rd = s.rd := E.rd
  have hmD : Frame [kD pc s] s.mem t.mem := E.mem.sub fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_singleton_self _, kR_subD⟩
  have pr := privBytes_rng pc
  have inD : ∀ {d : Nat}, d + 8 ≤ privBytes pc → (kD pc s).Contains (pb pc s + BitVec.ofNat 64 d) 8 :=
    fun {d} hd => by
      rw [pb_kb P, Offset.add_add]
      exact kb_contains (by rw [stackBytes_split]; unfold frameBytes Impl.Rsa.RISCV64.Priv.frameBytes; omega_using [hd])
  have inPB : ∀ {d : Nat}, d + 8 ≤ privBytes pc → (PB pc s).Contains (pb pc s + BitVec.ofNat 64 d) 8 :=
    fun {d} hd => Offset.contains_base _ hd (by omega_using [pr, hd])
  unfold privArgsM
  simp only [List.cons_append, List.nil_append]
  refine wp_addSp (imm := 0) (fun w₁ o₁ e₁ => wp_addSp (imm := privBytes pc + frameBytes) (fun w₂ o₂ e₂ => ?_)
    (by cases pc <;> decide)) (by decide)
  rw [usp] at e₁
  have O₂ : Only [.t0, .t6] (allocd (privBytes pc) t) w₂ := o₁.trans o₂
  have g0 : w₂.gpr .t0 = pb pc s := by rw [o₂.get .t0, e₁, BitVec.add_zero]
  have g6 : w₂.gpr .t6 = s.sp := by rw [e₂, o₁.sp, usp, pb_top P]
  refine wp_sd (a := pb pc s + BitVec.ofNat 64 0) (by rw [g0]) (pb_off_al P (by decide))
    (by rw [O₂.wr, uwr]; exact pb_in (by omega_using [pr])) (fun w₃ m₃ => ?_) (by decide)
  have hw0 : w₃.gpr .t0 = pb pc s := by rw [m₃.gpr]; exact g0
  have hw6 : w₃.gpr .t6 = s.sp := by rw [m₃.gpr]; exact g6
  have hrd : w₃.rd = s.rd := m₃.rd.trans (O₂.rd.trans urd)
  have hwr : w₃.wr = PB pc s :: fr s :: s.wr := m₃.wr.trans (O₂.wr.trans uwr)
  have hm₃ : Frame [kD pc s] s.mem w₃.mem := by
    rw [m₃.mem, O₂.mem]; exact hmD.writeW (List.mem_singleton_self _) _ (inD (by omega_using [pr]))
  have pb₃ : Frame [PB pc s] t.mem w₃.mem := by
    rw [m₃.mem, O₂.mem]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (inPB (by omega_using [pr]))
  rw [WP.block_append_iff]
  refine WP.mono (copies_ok P hw0 hw6 hrd hwr hm₃) fun v hc => ?_
  have v0 : v.gpr .t0 = pb pc s := by rw [hc.keep.get .t0, hw0]
  have v6 : v.gpr .t6 = s.sp := by rw [hc.keep.get .t6, hw6]
  have vrd : v.rd = s.rd := hc.keep.rd.trans hrd
  have vwr : v.wr = PB pc s :: fr s :: s.wr := hc.keep.wr.trans hwr
  have hmv : Frame [kD pc s] s.mem v.mem := hm₃.trans (hc.mem.sub fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_singleton_self _, PB_sub P⟩)
  have gv : ∀ r ∈ [Reg.s0, .s1, .s2, .s3, .a3, .a5, .a6, .a7], v.gpr r = t.gpr r := fun r hr => by
    rw [hc.keep.gpr r (by revert r; decide), m₃.gpr, O₂.gpr r (by revert r; decide)]; rfl
  refine wp_li (imm := 1024) (by decide) fun x₁ o₁ e₁ => wp_sll (sh := 3) (fun x₂ o₂ e₂ =>
    wp_add fun x₃ o₃ e₃ => ?_) (by decide)
  have O₃ : Only [.t1] v x₃ := (o₁.trans (o₂.trans o₃)).mono
  refine wp_sd (a := pb pc s + BitVec.ofNat 64 80) (by rw [O₃.get .t0, v0]) (pb_off_al P (by decide))
    (by rw [O₃.wr, vwr]; exact pb_in (by omega_using [pr])) (fun x₄ m₄ => ?_) (by decide)
  have hm₄ : Frame [kD pc s] s.mem x₄.mem := by
    rw [m₄.mem, O₃.mem]; exact hmv.writeW (List.mem_singleton_self _) _ (inD (by omega_using [pr]))
  refine wp_argD P (j := 14) (by decide) (by rw [m₄.gpr, O₃.get .t6, v6]) (m₄.rd.trans (O₃.rd.trans vrd)) hm₄
    (fun x₅ o₅ e₅ => wp_subi (imm := 1024) (fun x₆ o₆ e₆ => ?_) (by decide))
  have K₆ : Kept [.t1] v x₆ := (O₃.keep.trans (m₄.keep.trans (o₅.keep.trans o₆.keep))).mono
  refine wp_sd (a := pb pc s + BitVec.ofNat 64 88) (by rw [K₆.get .t0, v0]) (pb_off_al P (by decide))
    (by rw [K₆.wr, vwr]; exact pb_in (by omega_using [pr])) (fun x₇ m₇ => ?_) (by decide)
  have K₇ : Kept [.t1] v x₇ := (K₆.trans m₇.keep).mono
  have hm₇ : Frame [kD pc s] s.mem x₇.mem := by
    rw [m₇.mem, (o₅.trans o₆).mem]; exact hm₄.writeW (List.mem_singleton_self _) _ (inD (by omega_using [pr]))
  refine wp_mov fun x₈ o₈ e₈ => wp_mov fun x₉ o₉ e₉ => wp_mov fun x₁₀ o₁₀ e₁₀ => wp_mov fun x₁₁ o₁₁ e₁₁ => ?_
  have O₁₁ : Only [.a2, .a3, .a4, .a5] x₇ x₁₁ := (o₈.trans (o₉.trans (o₁₀.trans o₁₁))).mono
  refine wp_argD P (j := 11) (by decide) (by rw [O₁₁.get .t6, K₇.get .t6, v6])
    (O₁₁.rd.trans (K₇.rd.trans vrd)) (by rw [O₁₁.mem]; exact hm₇) fun x₁₂ o₁₂ e₁₂ => ?_
  refine wp_mov fun x₁₃ o₁₃ e₁₃ => wp_addi (imm := Impl.RsaOaep.RISCV64.oEm) (fun x₁₄ o₁₄ e₁₄ =>
    wp_mov fun x₁₅ o₁₅ e₁₅ => wp_nil ?_) (by decide)
  have T : Only [.a2, .a3, .a4, .a5, .a6, .a7, .a0, .a1] x₇ x₁₅ :=
    (O₁₁.trans (o₁₂.trans (o₁₃.trans (o₁₄.trans o₁₅)))).mono
  have K : Kept [.t1, .a2, .a3, .a4, .a5, .a6, .a7, .a0, .a1] v x₁₅ := (K₇.trans T.keep).mono
  have ks : ∀ r ∈ [Reg.s0, .s1, .s2, .s3], x₁₅.gpr r = t.gpr r := fun r hr => by
    rw [K.gpr r (by revert r; decide), gv r (by revert r; decide)]
  have hpb : Frame [PB pc s] t.mem x₁₅.mem := by
    rw [T.mem, m₇.mem, (o₅.trans o₆).mem, m₄.mem, O₃.mem]
    exact ((pb₃.trans hc.mem).writeW (List.mem_singleton_self _) _ (inPB (by omega_using [pr]))).writeW
      (List.mem_singleton_self _) _ (inPB (by omega_using [pr]))
  have hfm : x₁₅.mem = (v.mem.writeW (pb pc s + BitVec.ofNat 64 80) (x₃.gpr .t1)).writeW
      (pb pc s + BitVec.ofNat 64 88) (x₆.gpr .t1) := by
    rw [T.mem, m₇.mem, (o₅.trans o₆).mem, m₄.mem, O₃.mem]
  have t80 : x₃.gpr .t1 = psa s 10 := by
    rw [e₃, o₂.get .s0, o₁.get .s0, e₂, e₁, gv .s0 (by decide), E.s0]
    show _ = Sd s + BitVec.ofNat 64 8192
    congr 1
  have t88 : x₆.gpr .t1 = psa s 11 := by rw [e₆, e₅]; exact sl_sub P
  have r2 : ∀ d, d + 8 ≤ 80 → ((v.mem.writeW (pb pc s + BitVec.ofNat 64 80) (x₃.gpr .t1)).writeW
      (pb pc s + BitVec.ofNat 64 88) (x₆.gpr .t1)).readW (pb pc s + BitVec.ofNat 64 d) 64 =
      v.mem.readW (pb pc s + BitVec.ofNat 64 d) 64 := fun d hd => by
    rw [Mem.readW_writeW_sep (Offset.sep _ (.inl (by omega_using [hd])) (by omega_using [hd]) (by omega_using [])) (by decide),
      Mem.readW_writeW_sep (Offset.sep _ (.inl (by omega_using [hd])) (by omega_using [hd]) (by omega_using [])) (by decide)]
  have z0 : v.mem.readW (pb pc s + BitVec.ofNat 64 0) 64 = psa s 0 := by
    rw [hc.z, m₃.mem, Mem.readW_writeW_self64, O₂.get .a7]; exact E.args .a7 (by decide)
  have hg := hc.got
  refine {
    sp := K.sp.trans (hc.keep.sp.trans (m₃.sp.trans (O₂.sp.trans usp)))
    rd := K.rd.trans vrd
    wr := K.wr.trans vwr
    mem := hmD.trans (hpb.sub fun r hr => by
      rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_singleton_self _, PB_sub P⟩)
    sv := E.sv.sv.frame_in (lo := Proof.RsaOaep.RISCV64.oSv) (n := frameBytes - Proof.RsaOaep.RISCV64.oSv)
        (fun p hp => by
          have := Proof.RsaOaep.RISCV64.saved_offs p hp; unfold frameBytes Proof.RsaOaep.RISCV64.oSv at *; omega_using [this])
        hpb
      fun r hr => by rw [List.mem_singleton.mp hr]; exact slots_PB P
    s0 := (ks .s0 (by decide)).trans E.s0
    s1 := (ks .s1 (by decide)).trans E.s1
    s2 := (ks .s2 (by decide)).trans E.s2
    s3 := (ks .s3 (by decide)).trans E.s3
    a0 := by
      rw [o₁₅.get .a0, e₁₄, o₁₃.get .s0, o₁₂.get .s0, O₁₁.get .s0, K₇.get .s0, gv .s0 (by decide), E.s0]
      exact BitVec.add_zero _
    a1 := by
      rw [e₁₅, o₁₄.get .s1, o₁₃.get .s1, o₁₂.get .s1, O₁₁.get .s1, K₇.get .s1, gv .s1 (by decide), E.s1]
    a2 := by
      rw [(o₉.trans (o₁₀.trans (o₁₁.trans (o₁₂.trans (o₁₃.trans (o₁₄.trans o₁₅)))))).get .a2, e₈,
        K₇.get .a3, gv .a3 (by decide)]
      exact E.args .a3 (by decide)
    a3 := by
      rw [(o₁₀.trans (o₁₁.trans (o₁₂.trans (o₁₃.trans (o₁₄.trans o₁₅))))).get .a3, e₉, o₈.get .s1, K₇.get .s1,
        gv .s1 (by decide), E.s1]
    a4 := by
      rw [(o₁₁.trans (o₁₂.trans (o₁₃.trans (o₁₄.trans o₁₅)))).get .a4, e₁₀, o₉.get .a5, o₈.get .a5,
        K₇.get .a5, gv .a5 (by decide)]
      exact E.args .a5 (by decide)
    a5 := by
      rw [(o₁₂.trans (o₁₃.trans (o₁₄.trans o₁₅))).get .a5, e₁₁, o₁₀.get .a6, o₉.get .a6, o₈.get .a6,
        K₇.get .a6, gv .a6 (by decide)]
      exact E.args .a6 (by decide)
    a6 := by rw [(o₁₃.trans (o₁₄.trans o₁₅)).get .a6, e₁₂]
    a7 := by
      rw [(o₁₄.trans o₁₅).get .a7, e₁₃, o₁₂.get .s1, O₁₁.get .s1, K₇.get .s1, gv .s1 (by decide), E.s1]
    psa := fun i hi => by
      rw [hfm]
      match i, hi with
      | 0, _ => exact (r2 _ (by decide)).trans z0
      | 1, _ => exact (r2 _ (by decide)).trans (hg 0 (by decide))
      | 2, _ => exact (r2 _ (by decide)).trans (hg 1 (by decide))
      | 3, _ => exact (r2 _ (by decide)).trans (hg 2 (by decide))
      | 4, _ => exact (r2 _ (by decide)).trans (hg 3 (by decide))
      | 5, _ => exact (r2 _ (by decide)).trans (hg 4 (by decide))
      | 6, _ => exact (r2 _ (by decide)).trans (hg 5 (by decide))
      | 7, _ => exact (r2 _ (by decide)).trans (hg 6 (by decide))
      | 8, _ => exact (r2 _ (by decide)).trans (hg 7 (by decide))
      | 9, _ => exact (r2 _ (by decide)).trans (hg 8 (by decide))
      | 10, _ =>
        show Mem.readW _ (pb pc s + BitVec.ofNat 64 80) 64 = _
        rw [Mem.readW_writeW_sep (Offset.sep _ (.inl (by omega_using [])) (by omega_using []) (by omega_using [])) (by decide),
          Mem.readW_writeW_self64]
        exact t80
      | 11, _ =>
        show Mem.readW _ (pb pc s + BitVec.ofNat 64 88) 64 = _
        rw [Mem.readW_writeW_self64]
        exact t88
    t6 := by rw [K.get .t6, v6]
    t0 := by rw [K.get .t0, v0] }

/-- With `pc`, `privTail` copies `pre` and `pre_len` (our stack arguments 17
and 18) to its stack arguments 12 and 13. -/
theorem privTail_ok {t : State} (A : AtPrivM pc s t) : WP isa (.block (privTail pc)) t (AtPriv pc s) := by
  cases pc with
  | false => exact wp_nil ⟨A, fun h => nomatch h⟩
  | true =>
  have inA : ∀ {j : Nat} {ws : List Region}, j < 19 → InRegions (s.rd ++ ws) (stackArgAddr s j) 8 :=
    fun hj => by rw [P.hrd]; exact ⟨aR true s, by simp, in_aR19 hj⟩
  have ld : ∀ {u : State} {j : Nat}, j < 19 → Frame [kD true s] s.mem u.mem →
      u.mem.readW (stackArgAddr s j) 64 = stackArg s j := fun {u j} hj hm =>
    hm.readW (in_aR19 hj) (fun r hr => by rw [List.mem_singleton.mp hr]; exact P.ka.symm) (by decide)
  simp only [privTail]
  refine wp_ld (a := stackArgAddr s 17) (by rw [A.t6]; rfl) (arg_al19 P (by decide))
    (by rw [A.rd]; exact inA (j := 17) (by decide)) (fun t₁ o₁ e₁ => ?_) (by decide)
  refine wp_sd (a := pb true s + BitVec.ofNat 64 96) (by rw [o₁.get .t0, A.t0]) (pb_off_al P (by decide))
    (by rw [o₁.wr, A.wr]; exact pb_in (by decide)) (fun t₂ m₂ => ?_) (by decide)
  have f₂ : Frame [PB true s] t.mem t₂.mem := by
    rw [m₂.mem, o₁.mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (d := 96) (by decide) (by decide))
  have hm₂ : Frame [kD true s] s.mem t₂.mem := A.mem.trans (f₂.sub fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_singleton_self _, PB_sub P⟩)
  refine wp_ld (a := stackArgAddr s 18) (by rw [m₂.gpr, o₁.get .t6, A.t6]; rfl) (arg_al19 P (by decide))
    (by rw [m₂.rd, o₁.rd, A.rd]; exact inA (j := 18) (by decide)) (fun t₃ o₃ e₃ => ?_) (by decide)
  refine wp_sd (a := pb true s + BitVec.ofNat 64 104) (by rw [o₃.get .t0, m₂.gpr, o₁.get .t0, A.t0])
    (pb_off_al P (by decide)) (by rw [o₃.wr, m₂.wr, o₁.wr, A.wr]; exact pb_in (by decide))
    (fun t₄ m₄ => wp_nil ?_) (by decide)
  have K : Kept [.t1] t t₄ := (o₁.keep.trans (m₂.keep.trans (o₃.keep.trans m₄.keep))).mono
  have f₄ : Frame [PB true s] t.mem t₄.mem := by
    rw [m₄.mem, o₃.mem]
    exact f₂.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (d := 104) (by decide) (by decide))
  have hm₄ : Frame [kD true s] s.mem t₄.mem := A.mem.trans (f₄.sub fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_singleton_self _, PB_sub P⟩)
  have hmem : t₄.mem = (t.mem.writeW (pb true s + BitVec.ofNat 64 96) (t₁.gpr .t1)).writeW
      (pb true s + BitVec.ofNat 64 104) (t₃.gpr .t1) := by
    rw [m₄.mem, o₃.mem, m₂.mem, o₁.mem]
  have r12 : ∀ d, d + 8 ≤ 96 → t₄.mem.readW (pb true s + BitVec.ofNat 64 d) 64 =
      t.mem.readW (pb true s + BitVec.ofNat 64 d) 64 := fun d hd => by
    rw [hmem, Mem.readW_writeW_sep (Offset.sep _ (.inl (by omega_using [hd])) (by omega_using [hd]) (by omega_using [])) (by decide),
      Mem.readW_writeW_sep (Offset.sep _ (.inl (by omega_using [hd])) (by omega_using [hd]) (by omega_using [])) (by decide)]
  refine ⟨{
    sp := K.sp.trans A.sp
    rd := K.rd.trans A.rd
    wr := K.wr.trans A.wr
    mem := hm₄
    sv := A.sv.frame_in (lo := Proof.RsaOaep.RISCV64.oSv) (n := frameBytes - Proof.RsaOaep.RISCV64.oSv)
        (fun p hp => by
          have := Proof.RsaOaep.RISCV64.saved_offs p hp; unfold frameBytes Proof.RsaOaep.RISCV64.oSv at *; omega_using [this])
        f₄ fun r hr => by rw [List.mem_singleton.mp hr]; exact slots_PB P
    s0 := by rw [K.get .s0]; exact A.s0
    s1 := by rw [K.get .s1]; exact A.s1
    s2 := by rw [K.get .s2]; exact A.s2
    s3 := by rw [K.get .s3]; exact A.s3
    a0 := by rw [K.get .a0]; exact A.a0
    a1 := by rw [K.get .a1]; exact A.a1
    a2 := by rw [K.get .a2]; exact A.a2
    a3 := by rw [K.get .a3]; exact A.a3
    a4 := by rw [K.get .a4]; exact A.a4
    a5 := by rw [K.get .a5]; exact A.a5
    a6 := by rw [K.get .a6]; exact A.a6
    a7 := by rw [K.get .a7]; exact A.a7
    psa := fun i (hi : i < 12) => (r12 (8 * i) (by omega_using [hi])).trans (A.psa i hi)
    t6 := by rw [K.get .t6]; exact A.t6
    t0 := by rw [K.get .t0]; exact A.t0 }, fun _ i h1 h2 => ?_⟩
  have e₁' : t₁.gpr .t1 = stackArg s 17 := by rw [e₁]; exact ld (by decide) A.mem
  have e₃' : t₃.gpr .t1 = stackArg s 18 := by rw [e₃]; exact ld (by decide) hm₂
  match i, h1, h2 with
  | 12, _, _ =>
    show t₄.mem.readW (pb true s + BitVec.ofNat 64 96) 64 = _
    rw [hmem, Mem.readW_writeW_sep (Offset.sep _ (.inl (by omega_using [])) (by omega_using []) (by omega_using [])) (by decide),
      Mem.readW_writeW_self64]
    exact e₁'
  | 13, _, _ =>
    show t₄.mem.readW (pb true s + BitVec.ofNat 64 104) 64 = _
    rw [hmem, Mem.readW_writeW_self64]
    exact e₃'

theorem privArgs_ok {t : State} (E : Entered s t) :
    WP isa (.block (privArgs pc)) (allocd (privBytes pc) t) (AtPriv pc s) := by
  unfold privArgs
  rw [WP.block_append_iff]
  exact WP.mono (privArgsM_ok P E) fun u A => privTail_ok P A

end


/-! ## The call -/

/-- `EM`'s place, the ciphertext as the call reads it, and the private
operation's part of `scratch`. -/
abbrev emR (s : State) : Region := ⟨Sd s, kk s⟩
abbrev iD (s : State) : Region := ⟨stackArg s 11, kk s⟩
abbrev rsR (s : State) : Region := ⟨Sd s + BitVec.ofNat 64 oRsa, ((stackArg s 14).toNat - 1024) * 8⟩

/-- The regions the call reads (with `pc`, `pre` too) and writes. -/
abbrev callRd (pc : Bool) (s : State) : List Region :=
  [nR s, eR s, iD s, pR s, qR s, dpR s, dqR s, qiR s] ++ (if pc then [preR s] else []) ++ [PB pc s]

abbrev callWr (s : State) : List Region := [emR s, rsR s]

/-- The call's narrowed entry state. -/
abbrev callE (pc : Bool) (s t : State) : State := t.callEntry.withRegions (callRd pc s) (callWr s)

theorem callE_gpr (pc : Bool) (s t : State) {r : Reg} (hr : r ∉ linkRegs := by decide) :
    (callE pc s t).gpr r = t.gpr r :=
  State.callEntry_gpr t hr

theorem callE_stackArg {pc : Bool} {s t : State} (A : AtPriv pc s t) {i : Nat}
    (hi : i < (if pc then 14 else 12)) : stackArg (callE pc s t) i = psa s i := by
  show t.mem.readW (stackArgAddr (callE pc s t) i) 64 = _
  rw [stackArgAddr, show (callE pc s t).sp = pb pc s from A.sp]
  by_cases h : i < 12
  · exact A.psa i h
  · cases pc with
    | false => exact absurd hi (by simp only [Bool.false_eq_true, ↓reduceIte]; omega_using [h])
    | true => exact A.psx rfl i (by omega_using [h]) (by simpa using hi)

/-- The private operation's frame, below its stack arguments. -/
abbrev pkR (pc : Bool) (s : State) : Region := ⟨kb pc s, Impl.Rsa.RISCV64.Priv.frameBytes⟩

section
variable {pc : Bool} {s : State} (P : PreD pc s)
include P

theorem em_sub : Region.Sub (emR s) (scR s) := by
  have := P.hs; have := P.k2; unfold Spec.RsaPss.scratchWords Spec.Rsa.scratchWords at *
  exact Region.sub_prefix (by unfold kk; omega_arith)

theorem rs_sub : Region.Sub (rsR s) (scR s) := by
  have := scLen P
  exact Offset.sub_base _ (by unfold oRsa at *; omega_using [this])

theorem i_sub : Region.Sub (iD s) (ctR s) := by
  have := P.oc
  exact Region.sub_prefix (by unfold kk; omega_using [this])

omit P in
theorem pk_sub : Region.Sub (pkR pc s) (kD pc s) := by
  have := Offset.sub_base (kb pc s) (d := 0) (n := Impl.Rsa.RISCV64.Priv.frameBytes) (k := stackBytes pc)
    (by have := stackBytes_ge pc; unfold Impl.Rsa.RISCV64.Priv.frameBytes; omega_using [this])
  rwa [BitVec.add_zero] at this

theorem em_rs : (emR s).Disjoint (rsR s) := by
  have := P.wsc; have := P.k2; have := scLen P
  exact Offset.base_disjoint _ (by unfold kk oRsa at *; omega_arith) (by unfold oRsa at *; omega_arith)

theorem pk_PB : (pkR pc s).Disjoint (PB pc s) := by
  show Region.Disjoint _ ⟨pb pc s, privBytes pc⟩
  have := privBytes_rng pc
  rw [pb_kb P]
  exact Offset.base_disjoint _ (by decide) (by omega_using [this])

theorem preP_at {t : State} (A : AtPriv pc s t) : Rsa.RISCV64.Priv.PreP pc (callE pc s t) := by
  have hk := P.k2
  have sa := fun i (hi : i < 12) => callE_stackArg A (i := i) (Nat.lt_of_lt_of_le hi (by cases pc <;> decide))
  have hsp : (callE pc s t).sp = pb pc s := A.sp
  have g0 : (callE pc s t).gpr .a0 = Sd s := (callE_gpr pc s t).trans A.a0
  have g1 : (callE pc s t).gpr .a1 = s.gpr .a4 := (callE_gpr pc s t).trans A.a1
  have g2 : (callE pc s t).gpr .a2 = s.gpr .a3 := (callE_gpr pc s t).trans A.a2
  have g3 : (callE pc s t).gpr .a3 = s.gpr .a4 := (callE_gpr pc s t).trans A.a3
  have g4 : (callE pc s t).gpr .a4 = s.gpr .a5 := (callE_gpr pc s t).trans A.a4
  have g5 : (callE pc s t).gpr .a5 = s.gpr .a6 := (callE_gpr pc s t).trans A.a5
  have g6 : (callE pc s t).gpr .a6 = stackArg s 11 := (callE_gpr pc s t).trans A.a6
  have g7 : (callE pc s t).gpr .a7 = s.gpr .a4 := (callE_gpr pc s t).trans A.a7
  have s0 : stackArg (callE pc s t) 0 = s.gpr .a7 := sa 0 (by decide)
  have s1 : stackArg (callE pc s t) 1 = stackArg s 0 := sa 1 (by decide)
  have s2 : stackArg (callE pc s t) 2 = stackArg s 1 := sa 2 (by decide)
  have s3 : stackArg (callE pc s t) 3 = stackArg s 2 := sa 3 (by decide)
  have s4 : stackArg (callE pc s t) 4 = stackArg s 3 := sa 4 (by decide)
  have s5 : stackArg (callE pc s t) 5 = stackArg s 4 := sa 5 (by decide)
  have s6 : stackArg (callE pc s t) 6 = stackArg s 5 := sa 6 (by decide)
  have s7 : stackArg (callE pc s t) 7 = stackArg s 6 := sa 7 (by decide)
  have s8 : stackArg (callE pc s t) 8 = stackArg s 7 := sa 8 (by decide)
  have s9 : stackArg (callE pc s t) 9 = stackArg s 8 := sa 9 (by decide)
  have s10 : stackArg (callE pc s t) 10 = Sd s + BitVec.ofNat 64 oRsa := sa 10 (by decide)
  have s11 : stackArg (callE pc s t) 11 = BitVec.ofNat 64 ((stackArg s 14).toNat - 1024) := sa 11 (by decide)
  have hl : 1024 ≤ (stackArg s 14).toNat := by have := scLen P; unfold oRsa at this; omega_using [this]
  have l11 : (stackArg (callE pc s t) 11).toNat = (stackArg s 14).toNat - 1024 := by
    rw [s11, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := (stackArg s 14).isLt; omega_using [])
  have hO : Rsa.RISCV64.Priv.oR (callE pc s t) = emR s := by simp only [Rsa.RISCV64.Priv.oR, g0, g1]
  have hN : Rsa.RISCV64.Priv.nR (callE pc s t) = nR s := by simp only [Rsa.RISCV64.Priv.nR, g2, g3]
  have hE : Rsa.RISCV64.Priv.eR (callE pc s t) = eR s := by simp only [Rsa.RISCV64.Priv.eR, g4, g5]
  have hI : Rsa.RISCV64.Priv.iR (callE pc s t) = iD s := by simp only [Rsa.RISCV64.Priv.iR, g6, g7]
  have hP : Rsa.RISCV64.Priv.pR (callE pc s t) = pR s := by simp only [Rsa.RISCV64.Priv.pR, s0, s1]
  have hQ : Rsa.RISCV64.Priv.qR (callE pc s t) = qR s := by simp only [Rsa.RISCV64.Priv.qR, s2, s3]
  have hDP : Rsa.RISCV64.Priv.dpR (callE pc s t) = dpR s := by simp only [Rsa.RISCV64.Priv.dpR, s4, s5]
  have hDQ : Rsa.RISCV64.Priv.dqR (callE pc s t) = dqR s := by simp only [Rsa.RISCV64.Priv.dqR, s6, s7]
  have hQI : Rsa.RISCV64.Priv.qiR (callE pc s t) = qiR s := by simp only [Rsa.RISCV64.Priv.qiR, s8, s9]
  have hS : Rsa.RISCV64.Priv.sR (callE pc s t) = rsR s := by simp only [Rsa.RISCV64.Priv.sR, s10, l11]
  have hA : Rsa.RISCV64.Priv.aR pc (callE pc s t) = PB pc s := by
    simp only [Rsa.RISCV64.Priv.aR, stackArgAddr, hsp, Nat.mul_zero, BitVec.add_zero]; cases pc <;> rfl
  have hK : Rsa.RISCV64.Priv.kR (callE pc s t) = pkR pc s := by
    show Region.mk ((callE pc s t).sp - BitVec.ofNat 64 Impl.Rsa.RISCV64.Priv.frameBytes) _ = _
    rw [hsp, pb_kb P]; exact congrArg (Region.mk · _) (BitVec.add_sub_cancel _ _)
  have es := em_sub P
  have rs := rs_sub P
  have is := i_sub P
  have ks : Region.Sub (pkR pc s) (kD pc s) := pk_sub
  have pbs := PB_sub P
  have pt := kb_toNat P
  have spl := s.sp.isLt
  have st := P.sp1
  have pr := privBytes_rng pc
  rw [stackBytes_split] at pt st
  unfold frameBytes Impl.Rsa.RISCV64.Priv.frameBytes at pt st
  have pbt : (pb pc s).toNat = s.sp.toNat - (privBytes pc + 128) := by
    have := pb_kb P
    rw [this, Offset.toNat_add_ofNat, kb_toNat P, stackBytes_split]
    unfold frameBytes Impl.Rsa.RISCV64.Priv.frameBytes at *; omega_using [st]
  have e13 : (Sd s).toNat = (stackArg s 13).toNat := rfl
  have hsw := P.hs
  unfold Spec.RsaPss.scratchWords Spec.Rsa.scratchWords at hsw
  have sdt : (Sd s + BitVec.ofNat 64 oRsa).toNat = (Sd s).toNat + oRsa := by
    rw [Offset.toNat_add_ofNat]; have := P.wsc; unfold oRsa at *; omega_using [e13, hsw, this]
  exact {
    sp16 := by rw [hsp]; exact pb_al P
    sp1 := by rw [hsp, pbt]; unfold Impl.Rsa.RISCV64.Priv.frameBytes; omega_using [st]
    sp2 := by rw [hsp, pbt]; omega_using []
    hrd := by
      rw [Rsa.RISCV64.Priv.rdL, hN, hE, hI, hP, hQ, hDP, hDQ, hQI, hA]
      cases pc with
      | false => rfl
      | true =>
        have hPre : Rsa.RISCV64.Priv.preR (callE true s t) = preR s := by
          simp only [Rsa.RISCV64.Priv.preR, callE_stackArg A (i := 12) (by decide),
            callE_stackArg A (i := 13) (by decide), psa]
        simp only [↓reduceIte, hPre]; rfl
    hwr := by rw [hO, hS]; rfl
    on := by rw [hO, hN]; exact (P.ns.sub_right es).symm
    oe := by rw [hO, hE]; exact (P.es.sub_right es).symm
    oi := by rw [hO, hI]; exact (P.cts.sub_left is |>.sub_right es).symm
    op := by rw [hO, hP]; exact (P.ps.sub_right es).symm
    oq := by rw [hO, hQ]; exact (P.qs.sub_right es).symm
    odp := by rw [hO, hDP]; exact (P.dps.sub_right es).symm
    odq := by rw [hO, hDQ]; exact (P.dqs.sub_right es).symm
    oqi := by rw [hO, hQI]; exact (P.qis.sub_right es).symm
    os := by rw [hO, hS]; exact em_rs P
    oa := by rw [hO, hA]; exact (P.ks.sub_left pbs |>.sub_right es).symm
    ns := by rw [hN, hS]; exact P.ns.sub_right rs
    es := by rw [hE, hS]; exact P.es.sub_right rs
    is := by rw [hI, hS]; exact P.cts.sub_left is |>.sub_right rs
    ps := by rw [hP, hS]; exact P.ps.sub_right rs
    qs := by rw [hQ, hS]; exact P.qs.sub_right rs
    dps := by rw [hDP, hS]; exact P.dps.sub_right rs
    dqs := by rw [hDQ, hS]; exact P.dqs.sub_right rs
    qis := by rw [hQI, hS]; exact P.qis.sub_right rs
    sa := by rw [hS, hA]; exact (P.ks.sub_left pbs |>.sub_right rs).symm
    ko := by rw [hK, hO]; exact P.ks.sub_left ks |>.sub_right es
    kn := by rw [hK, hN]; exact P.kn.sub_left ks
    ke := by rw [hK, hE]; exact P.ke.sub_left ks
    ki := by rw [hK, hI]; exact P.kct.sub_left ks |>.sub_right is
    kp := by rw [hK, hP]; exact P.kp.sub_left ks
    kq := by rw [hK, hQ]; exact P.kq.sub_left ks
    kdp := by rw [hK, hDP]; exact P.kdp.sub_left ks
    kdq := by rw [hK, hDQ]; exact P.kdq.sub_left ks
    kqi := by rw [hK, hQI]; exact P.kqi.sub_left ks
    ks := by rw [hK, hS]; exact P.ks.sub_left ks |>.sub_right rs
    ka := by rw [hK, hA]; exact pk_PB P
    wo := by rw [g0, g1]; have := P.wsc; omega_using [hk, hl, e13, this]
    wn := by rw [g2, g3]; exact P.wn
    we := by rw [g4, g5]; exact P.we
    wi := by rw [g6, g7]; have := P.wct; have := P.oc; omega_arith
    wp := by rw [s0, s1]; exact P.wp
    wq := by rw [s2, s3]; exact P.wq
    wdp := by rw [s4, s5]; exact P.wdp
    wdq := by rw [s6, s7]; exact P.wdq
    wqi := by rw [s8, s9]; exact P.wqi
    ws := by rw [s10, l11, sdt]; have := P.wsc; unfold oRsa; omega_using [hl, e13, this]
    k1 := by rw [g3]; exact P.k1
    k2 := by rw [g3]; exact P.k2
    h1 := by rw [g1, g3]
    h7 := by rw [g7, g3]
    e1 := by rw [g5]; exact P.e1
    e2 := by rw [g5, g3]; exact P.e2
    p1 := by rw [s1]; exact P.p1
    p2 := by rw [s1, g3]; exact P.p2
    q1 := by rw [s3]; exact P.q1
    q2 := by rw [s3, g3]; exact P.q2
    h5 := by rw [s5, s1]; exact P.h4
    h9 := by rw [s9, s1]; exact P.h8
    h7' := by rw [s7, s3]; exact P.h6
    hs := by rw [g3, l11]; unfold Spec.Rsa.scratchWords; omega_using [hsw]
    al := by rw [s10, sdt]; have := P.als; unfold oRsa; omega_using [e13, this] }

end


/-! ## The outcome -/

/-- RSADP checked against `e`, of the entry's buffers. -/
def privO (s : State) : Spec.Rsa.Outcome :=
  Spec.Rsa.privateChecked (Spec.Rsa.bytesAt s.mem (s.gpr .a3) (kk s))
    (Spec.Rsa.bytesAt s.mem (s.gpr .a5) (s.gpr .a6).toNat) (Spec.Rsa.bytesAt s.mem (stackArg s 11) (kk s))
    (Spec.Rsa.bytesAt s.mem (s.gpr .a7) (stackArg s 0).toNat)
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
structure AfterPriv (pc : Bool) (s v : State) : Prop where
  base : Base (SD s) (VD s (rcOf (privO s))) (withMem s v.mem) v
  mem : Frame [kD pc s, scR s] s.mem v.mem
  em : Spec.Rsa.bytesAt v.mem (Sd s) (kk s) = emOf (kk s) (privO s)

theorem rcOf_le (o : Spec.Rsa.Outcome) : rcOf o ≤ 2 := by cases o <;> simp [rcOf]

/-- The outcome, from `writtenOutcome`. -/
theorem of_written {m : Mem} {p : Addr} {k : Nat} {r : BitVec 32} {o : Spec.Rsa.Outcome}
    (h : Spec.Rsa.writtenOutcome m p k r o) : r = BitVec.ofNat 32 (rcOf o) ∧ Spec.Rsa.bytesAt m p k = emOf k o := by
  cases o with
  | ok y => exact ⟨h.1, h.2⟩
  | invalid => exact ⟨h.1, h.2⟩
  | fault => exact ⟨h.1, h.2⟩

/-- `slli`, `srli` by 32: the low word, zero-extended. -/
theorem zext32 {x : BitVec 64} {r : Nat} (hr : x.setWidth 32 = BitVec.ofNat 32 r) (h : r ≤ 2) :
    (x <<< 32) >>> 32 = BitVec.ofNat 64 r := by
  have e := congrArg BitVec.toNat hr
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat] at e
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow]
  omega_using [h, e]

theorem priv_sdepth : sdepth Impl.Rsa.RISCV64.Priv.code = Impl.Rsa.RISCV64.Priv.frameBytes := by decide +kernel
theorem privP_sdepth : sdepth Impl.Rsa.RISCV64.Priv.codeP = Impl.Rsa.RISCV64.Priv.frameBytes := by decide +kernel

section
variable {pc : Bool} {s : State} (P : PreD pc s)
include P

theorem cov_sc {d n : Nat} (h : d + n ≤ (stackArg s 14).toNat * 8) {rs : List Region} :
    Covers [⟨Sd s + BitVec.ofNat 64 d, n⟩] (rs ++ s.wr) :=
  Covers.of_sub fun r hr => by
    rw [List.mem_singleton.mp hr, P.hwr]
    exact ⟨scR s, by simp, d, rfl, h⟩

theorem call_covers {t : State} (A : AtPriv pc s t) :
    Covers (callRd pc s ++ callWr s) (t.rd ++ t.wr) ∧ Covers (callWr s) t.wr := by
  have hsw := P.hs
  have := P.k2
  unfold Spec.RsaPss.scratchWords Spec.Rsa.scratchWords at hsw
  have hw : Covers (callWr s) t.wr := by
    rw [A.wr]
    refine Covers.pair ?_ ?_
    · have := cov_sc P (d := 0) (n := kk s) (rs := [PB pc s, fr s]) (by unfold kk; omega_using [hsw])
      rwa [BitVec.add_zero] at this
    · exact cov_sc P (d := oRsa) (rs := [PB pc s, fr s]) (by unfold oRsa; omega_using [hsw])
  refine ⟨Covers.append_left (Covers.of_forall fun r hr => ?_) (Covers.right hw), hw⟩
  rw [A.rd, A.wr, P.hrd]
  have hct : iD s = ctR s := by simp only [iD, ctR, kk, P.oc]
  have inRd : ∀ {r}, r ∈ rdD pc s → Covers [r] (rdD pc s ++ (PB pc s :: fr s :: s.wr)) := fun h =>
    Covers.left (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; exact h)
  simp only [callRd, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with ((rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | hp) | rfl
  · exact inRd (by simp)
  · exact inRd (by simp)
  · rw [hct]; exact inRd (by simp)
  · exact inRd (by simp)
  · exact inRd (by simp)
  · exact inRd (by simp)
  · exact inRd (by simp)
  · exact inRd (by simp)
  · cases pc with
    | false => simp at hp
    | true =>
      simp only [↓reduceIte, List.mem_singleton] at hp
      subst hp; exact inRd (by simp)
  · exact Covers.right (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp)

omit P in
/-- The caller's buffers at the call are as on entry. -/
theorem bytes_at {t : State} (A : AtPriv pc s t) {R : Region} (hd : (kD pc s).Disjoint R) (hl : R.len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt t.mem R.base R.len = Spec.Rsa.bytesAt s.mem R.base R.len := by
  simp only [Spec.Rsa.bytesAt]
  exact List.map_congr_left fun i hi => A.mem.bytes (R := R) (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact hd.symm) hl (List.mem_range.mp hi)

theorem below_pb : below (pb pc s) Impl.Rsa.RISCV64.Priv.frameBytes = pkR pc s := by
  show Region.mk (pb pc s - BitVec.ofNat 64 Impl.Rsa.RISCV64.Priv.frameBytes) _ = _
  rw [pb_kb P]; exact congrArg (Region.mk · _) (BitVec.add_sub_cancel _ _)

/-- Our frame's slots and what the call writes. -/
theorem slots_dis : ∀ r ∈ callWr s ++ [pkR pc s],
    Region.Disjoint ⟨fb s + BitVec.ofNat 64 Proof.RsaOaep.RISCV64.oSv, frameBytes - Proof.RsaOaep.RISCV64.oSv⟩ r := by
  have hk : Region.Sub ⟨fb s + BitVec.ofNat 64 Proof.RsaOaep.RISCV64.oSv,
      frameBytes - Proof.RsaOaep.RISCV64.oSv⟩ (kD pc s) := by
    rw [fb_kb P, Offset.add_add]
    exact kb_sub (by
      have := privBytes_rng pc
      rw [stackBytes_split]; unfold frameBytes Impl.Rsa.RISCV64.Priv.frameBytes Proof.RsaOaep.RISCV64.oSv; omega_using [])
  intro r hr
  simp only [callWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (P.ks.sub_left hk).sub_right (em_sub P)
  · exact (P.ks.sub_left hk).sub_right (rs_sub P)
  · have := privBytes_rng pc
    rw [fb_kb P, Offset.add_add]
    exact Offset.disjoint_base _ (by unfold Impl.Rsa.RISCV64.Priv.frameBytes; omega_using [])
      (by unfold frameBytes Proof.RsaOaep.RISCV64.oSv Impl.Rsa.RISCV64.Priv.frameBytes; omega_using [this])

omit P in
/-- With `pc`, the facts of `pre` at the call. -/
theorem preX_at {t : State} (P' : PreD true s) (X : PreXD s) (A : AtPriv true s t) :
    Rsa.RISCV64.Priv.PreX (callE true s t) := by
  have sa := fun i (hi : i < 14) => callE_stackArg A (i := i) (by simpa using hi)
  have hsp : (callE true s t).sp = pb true s := A.sp
  have hpbt : (pb true s).toNat = s.sp.toNat - 240 := by
    have := pb_kb P'
    have sp1 := P'.sp1
    rw [this, Offset.toNat_add_ofNat, kb_toNat P', stackBytes_true]
    rw [stackBytes_true] at sp1; omega_using [sp1]
  have hPre : Rsa.RISCV64.Priv.preR (callE true s t) = preR s := by
    simp only [Rsa.RISCV64.Priv.preR, sa 12 (by decide), sa 13 (by decide), psa]
  have hO : Rsa.RISCV64.Priv.oR (callE true s t) = emR s := by
    simp only [Rsa.RISCV64.Priv.oR, callE_gpr true s t (r := .a0), callE_gpr true s t (r := .a1), A.a0, A.a1]
  have hl : 1024 ≤ (stackArg s 14).toNat := by have := scLen P'; unfold oRsa at this; omega_using [this]
  have w11 : (BitVec.ofNat 64 ((stackArg s 14).toNat - 1024)).toNat = (stackArg s 14).toNat - 1024 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := (stackArg s 14).isLt; omega_using [])]
  have hS : Rsa.RISCV64.Priv.sR (callE true s t) = rsR s := by
    simp only [Rsa.RISCV64.Priv.sR, sa 10 (by decide), sa 11 (by decide), psa, w11]
  have hK : Rsa.RISCV64.Priv.kR (callE true s t) = pkR true s := by
    show Region.mk ((callE true s t).sp - BitVec.ofNat 64 Impl.Rsa.RISCV64.Priv.frameBytes) _ = _
    rw [hsp, pb_kb P']; exact congrArg (Region.mk · _) (BitVec.add_sub_cancel _ _)
  refine ⟨by rw [hO, hPre]; exact X.sP.sub_left (em_sub P'), by rw [hS, hPre]; exact X.sP.sub_left (rs_sub P'),
    by rw [hK, hPre]; exact X.kP.sub_left pk_sub, ?_, ?_, ?_, ?_, ?_⟩
  · rw [sa 12 (by decide), sa 13 (by decide)]; exact X.wP
  · rw [sa 13 (by decide), sa 1 (by decide), sa 3 (by decide), callE_gpr true s t (r := .a3), A.a3]; exact X.pl
  · rw [hsp, hpbt]; have := P'.sp1; rw [stackBytes_true] at this; omega_using []
  · -- `pre`'s values, as the caller's precondition gives them.
    have hb := fun {p : Addr} {len : Nat} (hd : (kD true s).Disjoint ⟨p, len⟩) (hl : len ≤ 2 ^ 64) =>
      bytes_at A (R := ⟨p, len⟩) hd hl
    have hw := VG.Proof.Rsa.RISCV64.Priv.words_of_frame A.mem (p := stackArg s 17) (n := (stackArg s 18).toNat)
      (fun r hr => by
        rw [List.mem_singleton.mp hr, Nat.mul_comm]; exact X.kP.symm) (by have := X.wP; omega_using [this])
    simp only [Rsa.RISCV64.Priv.PreHyp, State.withRegions_mem, State.callEntry_mem, callE_gpr true s t (r := .a2),
      callE_gpr true s t (r := .a3), A.a2, A.a3, sa 0 (by decide), sa 1 (by decide), sa 2 (by decide),
      sa 3 (by decide), sa 12 (by decide), sa 13 (by decide), psa, hw]
    rw [hb P'.kn (by have := P'.wn; omega_using []), hb P'.kp (by have := P'.wp; omega_using []),
      hb P'.kq (by have := P'.wq; omega_using [])]
    exact X.hyp rfl
  · rw [sa 12 (by decide)]; exact X.alP

/-- The call of `vg_rsa_private_checked`, or with `pc` of
`vg_rsa_private_checked_precomputed`. -/
theorem call_priv {u : State} (A : AtPriv pc s u) :
    WP isa (privCall pc) u fun v => v.rd = u.rd ∧ v.wr = u.wr ∧ v.sp = u.sp ∧
      Frame (callWr s ++ [pkR pc s]) u.mem v.mem ∧ (∀ r ∈ preserved, v.gpr r = u.gpr r) ∧
      Rsa.RISCV64.Priv.fnPost (callE pc s u) (v.withRegions (callRd pc s) (callWr s)) := by
  obtain ⟨hc, hw⟩ := call_covers P A
  cases pc with
  | false =>
    refine WP.callAny (k := Rsa.RISCV64.Priv.fnContract) Rsa.RISCV64.Priv.code_correct
      (Rsa.RISCV64.Priv.pre_of_preP (preP_at P A)) hc hw (fun v hrd hwr hsp' hf hpres hpost => ?_)
      (by rw [priv_sdepth]; decide)
    rw [priv_sdepth, A.sp, below_pb P] at hf
    exact ⟨hrd, hwr, hsp', hf, hpres, hpost⟩
  | true =>
    refine WP.callAny (k := Rsa.RISCV64.Priv.fnContractP) Rsa.RISCV64.Priv.codeP_correct
      (Rsa.RISCV64.Priv.pre_of_prePX (preP_at P A) (preX_at P (P.px rfl) A)) hc hw
      (fun v hrd hwr hsp' hf hpres hpost => ?_) (by rw [privP_sdepth]; decide)
    rw [privP_sdepth, A.sp, below_pb P] at hf
    exact ⟨hrd, hwr, hsp', hf, hpres, hpost⟩

/-- The private operation's frame, with the stack pointer after it. -/
theorem privF_ok {t : State} (E : Entered s t) :
    WP isa (.frame (.alloc (privBytes pc)) (.seq (.block (privArgs pc)) (privCall pc)) (.free (privBytes pc))) t
      fun w => w.sp = fb s ∧
        WP isa (.block [.shift .sll .d .s4 .a0 32, .shift .srl .d .s4 .s4 32]) w (AfterPriv pc s) := by
  have hsp : t.sp = fb s := E.sv.sp
  have pr := privBytes_rng pc
  refine WP.alloc (by cases pc <;> exact ⟨by decide, by decide, by decide⟩) (by
    rw [hsp]; have := P.sp1
    rw [stackBytes_split] at this
    simp only [fb, BitVec.toNat_sub, BitVec.toNat_ofNat, frameBytes, Impl.Rsa.RISCV64.Priv.frameBytes] at *
    omega_using [this]) ?_
  refine WP.seq (WP.mono (privArgs_ok P E) fun u A => ?_)
  refine WP.mono (call_priv P A) fun v ⟨hrd, hwr, hsp', hf, hpres, hpost⟩ => ?_
  have fsp : (freed (privBytes pc) v).sp = fb s := by
    show v.sp + BitVec.ofNat 64 (privBytes pc) = fb s
    rw [hsp', A.sp, BitVec.sub_add_cancel]
  refine ⟨fsp, wp_sll (fun w₁ o₁ e₁ => wp_srl (fun w ow ew => wp_nil ?_))⟩
  -- The outcome.
  have sa := fun i (hi : i < 12) => callE_stackArg A (i := i) (Nat.lt_of_lt_of_le hi (by cases pc <;> decide))
  have s0 : stackArg (callE pc s u) 0 = s.gpr .a7 := sa 0 (by decide)
  have s1 : stackArg (callE pc s u) 1 = stackArg s 0 := sa 1 (by decide)
  have s2 : stackArg (callE pc s u) 2 = stackArg s 1 := sa 2 (by decide)
  have s3 : stackArg (callE pc s u) 3 = stackArg s 2 := sa 3 (by decide)
  have s4 : stackArg (callE pc s u) 4 = stackArg s 3 := sa 4 (by decide)
  have s6 : stackArg (callE pc s u) 6 = stackArg s 5 := sa 6 (by decide)
  have s8 : stackArg (callE pc s u) 8 = stackArg s 7 := sa 8 (by decide)
  simp only [Rsa.RISCV64.Priv.fnPost, State.withRegions_mem, State.withRegions_gpr,
    State.callEntry_mem, callE_gpr pc s u (r := .a0), callE_gpr pc s u (r := .a2), callE_gpr pc s u (r := .a3),
    callE_gpr pc s u (r := .a4), callE_gpr pc s u (r := .a5), callE_gpr pc s u (r := .a6), A.a0, A.a2, A.a3, A.a4, A.a5,
    A.a6, s0, s1, s2, s3, s4, s6, s8] at hpost
  have hb := fun {p : Addr} {len : Nat} (hd : (kD pc s).Disjoint ⟨p, len⟩) (hl : len ≤ 2 ^ 64) =>
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
  have O : Only [.s4] (freed (privBytes pc) v) w := (o₁.trans ow).mono
  have fwr : (freed (privBytes pc) v).wr = fr s :: s.wr := by
    show v.wr.tail = _; rw [hwr, A.wr]; rfl
  have wm : w.mem = v.mem := O.mem
  have pv : ∀ r ∈ preserved, r ≠ .s4 → w.gpr r = u.gpr r := fun r hr' h4 =>
    (O.gpr r (by simpa using h4)).trans (hpres r hr')
  have r4 : w.gpr .s4 = BitVec.ofNat 64 (rcOf (privO s)) := by
    rw [ew, e₁]; exact zext32 hr (rcOf_le _)
  have fm : Frame [kD pc s, scR s] s.mem w.mem := by
    rw [wm]
    refine (A.mem.mono fun r hr => by simp at hr ⊢; exact .inl hr).trans (hf.sub fun r hr => ?_)
    simp only [callWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨scR s, by simp, em_sub P⟩
    · exact ⟨scR s, by simp, rs_sub P⟩
    · exact ⟨kD pc s, by simp, pk_sub⟩
  have svs : Spill.Saved (fb s) s.gpr Impl.RsaOaep.RISCV64.saved w.mem := by
    rw [wm]
    exact A.sv.frame_in (lo := Proof.RsaOaep.RISCV64.oSv) (n := frameBytes - Proof.RsaOaep.RISCV64.oSv)
      (fun p hp => by
        have := Proof.RsaOaep.RISCV64.saved_offs p hp; unfold frameBytes Proof.RsaOaep.RISCV64.oSv at *; omega_using [this])
      hf (slots_dis P)
  refine ⟨⟨⟨by rw [O.sp]; exact fsp, by rw [O.wr]; exact fwr, svs⟩, by rw [O.rd]; exact hrd.trans A.rd,
    by rw [pv .s0 (by decide) (by decide)]; exact A.s0, ?_, Frame.refl _ _⟩, fm, by rw [wm, hem]⟩
  intro r hr
  simp only [Proof.RsaOaep.RISCV64.fx, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [pv _ (by decide) (by decide)]; exact A.s1
  · rw [pv _ (by decide) (by decide)]; exact A.s2
  · rw [pv _ (by decide) (by decide)]; exact A.s3
  · exact r4

theorem priv_ok {t : State} (E : Entered s t) : WP isa (Impl.RsaOaep.RISCV64.Dec.priv pc) t (AfterPriv pc s) :=
  WP.seq (WP.mono (privF_ok P E) fun _ h => h.2)

end

end VG.Proof.RsaOaep.RISCV64.Dec
