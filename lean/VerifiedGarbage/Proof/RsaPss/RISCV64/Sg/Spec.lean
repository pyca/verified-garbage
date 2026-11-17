module

public import VerifiedGarbage.Proof.RsaOaep.RISCV64.Pub
import VerifiedGarbage.Proof.RsaOaep.RISCV64.MgfT
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.RsaPss.EncBytes
import VerifiedGarbage.Proof.RsaPss.SignCases
import VerifiedGarbage.Proof.RsaPss.Params
import VerifiedGarbage.Proof.RsaPss.CtPad
import VerifiedGarbage.Proof.RsaPss.MgfBytes
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Spec.RsaPss
public import VerifiedGarbage.Spec.RsaPss.Contract
public import VerifiedGarbage.Spec.RsaPss.MdTable
public import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Proof.RsaOaep.RISCV64.Base
public import VerifiedGarbage.Proof.RsaPss.RISCV64.Pre
public import VerifiedGarbage.Impl.RsaPss.RISCV64.Sign
import VerifiedGarbage.Proof.Framework.Mem

/-! ### `RsaPss.RISCV64.Sg.Pre`, which this module and modules that import it used -/

section

/-!
# RSASSA-PSS signing on RISC-V: the precondition and the entry

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaPss/PPC64LE/Sg/Pre.lean`, `Sg/Entry.lean`), with the frame of
RSAES-OAEP decryption (`Proof/RsaOaep/RISCV64/Dc/Priv.lean`): `PreS pc D s`, the
shared contract's precondition (`Spec.RsaPss.signMdTableContract`, with the stack of
the frames and of `vg_rsa_private_checked`, `stackBytes`), by name
(`preS_of`), for a digest of `D` bytes; the working space `Ss s` and the
values `Base` fixes in `s1`–`s4` (`vS s`: `k`, `out`, `lo` and `salt_len`),
all public; `fits`; `pro_ok`: the saves and the prologue leave our caller's
registers and return address in their slots and the arguments in the
registers that keep them (`Pro`); and `spill_ok`: then `spill` leaves
`Base`, the modulus' first byte in `t1`, and `n`, `e`, `e_len`, `p`, `p_len`
and the mask `c` of `DB`'s top bits in the six words at `scratch + oP`
(`Spilled`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.RISCV64.Sg

open VG VG.RISCV64
open VG.Impl.RsaOaep.RISCV64 (frameBytes oRsa save)
open VG.Impl.RsaPss.RISCV64.Sign (privBytes prologue spill oP)
open VG.Proof.RsaOaep.RISCV64 (Base Fits SC off fx kR fb fr save_ok Saves fb_al stackArgAddr_eq sc_inW sc_in)
open VG.Proof.RsaPss.RISCV64 (loB)
open VG.Proof.RsaPkcs1Sig.RISCV64 (Only Kept MemTo wp_ld wp_sd wp_mov wp_addSp wp_nil wp_lbu wp_srl wp_or wp_subi
  wp_li wp_sub wp_and)

theorem stackArgs_sixteen (s : State) :
    List.map (stackArg s) (List.range 16) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9, stackArg s 10,
      stackArg s 11, stackArg s 12, stackArg s 13, stackArg s 14, stackArg s 15] := rfl

/-- The stack the function uses: its frame (`frameBytes`), the private
operation's (`privBytes`) and that function's own. -/
def stackBytes (pc : Bool) : Nat := frameBytes + privBytes pc + Impl.Rsa.RISCV64.Priv.frameBytes

theorem stackBytes_eq : stackBytes false = 3472 := rfl
theorem stackBytes_true : stackBytes true = 3488 := rfl

theorem stackBytes_ge (pc : Bool) : 3472 ≤ stackBytes pc ∧ stackBytes pc ≤ 3488 := by cases pc <;> decide

/-! ## The buffers -/

abbrev oR (s : State) : Region := ⟨s.gpr .a0, (s.gpr .a1).toNat⟩
abbrev nR (s : State) : Region := ⟨s.gpr .a2, (s.gpr .a3).toNat⟩
abbrev eR (s : State) : Region := ⟨s.gpr .a4, (s.gpr .a5).toNat⟩
abbrev pR (s : State) : Region := ⟨s.gpr .a6, (s.gpr .a7).toNat⟩
abbrev qR (s : State) : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩
abbrev dpR (s : State) : Region := ⟨stackArg s 2, (stackArg s 3).toNat⟩
abbrev dqR (s : State) : Region := ⟨stackArg s 4, (stackArg s 5).toNat⟩
abbrev qiR (s : State) : Region := ⟨stackArg s 6, (stackArg s 7).toNat⟩
abbrev dgR (D : Nat) (s : State) : Region := ⟨stackArg s 8, D⟩
abbrev sR (s : State) : Region := ⟨stackArg s 10, (stackArg s 11).toNat⟩
abbrev scR (s : State) : Region := ⟨stackArg s 12, (stackArg s 13).toNat * 8⟩
abbrev tHR (s : State) : Region := Sig.tableRegion 64 (stackArg s 14) 11
abbrev tGR (s : State) : Region := Sig.tableRegion 64 (stackArg s 15) 11
/-- The stack arguments: 16, or with `pc` (`vg_rsa_pss_sign_precomputed`) 18. -/
abbrev aR (pc : Bool) (s : State) : Region := ⟨stackArgAddr s 0, if pc then 144 else 128⟩
/-- With `pc`, the key's precomputed values, `pre_len` words. -/
abbrev preR (s : State) : Region := ⟨stackArg s 16, (stackArg s 17).toNat * 8⟩

/-- The buffers the function reads. -/
abbrev rdS (pc : Bool) (D : Nat) (s : State) : List Region :=
  [nR s, eR s, pR s, qR s, dpR s, dqR s, qiR s, dgR D s, sR s] ++ (if pc then [preR s] else []) ++
    [tHR s, tGR s, aR pc s]

/-- The stack the function uses. -/
abbrev kS (pc : Bool) (s : State) : Region := ⟨s.sp - BitVec.ofNat 64 (stackBytes pc), stackBytes pc⟩

/-- With `pc`, `pre` holds the key's precomputed values. -/
abbrev HypS (pc : Bool) (s : State) : Prop :=
  pc = true → Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .a6) (s.gpr .a7).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat) =
    some (Spec.Rsa.wordsAt s.mem (stackArg s 16) (stackArg s 17).toNat)

/-- What `vg_rsa_pss_sign_precomputed`'s precondition adds: `pre`'s facts. -/
structure PreXS (s : State) : Prop where
  oP : (oR s).Disjoint (preR s)
  sP : (scR s).Disjoint (preR s)
  kP : (kS true s).Disjoint (preR s)
  wP : (stackArg s 16).toNat + (stackArg s 17).toNat * 8 ≤ 2 ^ 64
  pl : (stackArg s 17).toNat =
    Spec.Rsa.privatePrecomputedWords (s.gpr .a3).toNat (s.gpr .a7).toNat (stackArg s 1).toNat
  sp3 : s.sp.toNat + 144 ≤ 2 ^ 64
  alP : (stackArg s 16).toNat % 8 = 0
  hyp : HypS true s

/-- What the code needs of `signMdTableContract.pre` (or with `pc`
`signPrecomputedMdTableContract.pre`), by name, for a hash function of
`D`-byte digests (the table `hash`'s). -/
structure PreS (pc : Bool) (D : Nat) (s : State) : Prop where
  spal : s.sp.toNat % 16 = 0
  sp1 : stackBytes pc ≤ s.sp.toNat
  sp2 : s.sp.toNat + (if pc then 144 else 128) ≤ 2 ^ 64
  hrd : s.rd = rdS pc D s
  hwr : s.wr = [oR s, scR s]
  on : (oR s).Disjoint (nR s)
  oe : (oR s).Disjoint (eR s)
  op : (oR s).Disjoint (pR s)
  oq : (oR s).Disjoint (qR s)
  odp : (oR s).Disjoint (dpR s)
  odq : (oR s).Disjoint (dqR s)
  oqi : (oR s).Disjoint (qiR s)
  odg : (oR s).Disjoint (dgR D s)
  osl : (oR s).Disjoint (sR s)
  os : (oR s).Disjoint (scR s)
  oth : (oR s).Disjoint (tHR s)
  otg : (oR s).Disjoint (tGR s)
  oa : (oR s).Disjoint (aR pc s)
  ns : (nR s).Disjoint (scR s)
  es : (eR s).Disjoint (scR s)
  ps : (pR s).Disjoint (scR s)
  qs : (qR s).Disjoint (scR s)
  dps : (dpR s).Disjoint (scR s)
  dqs : (dqR s).Disjoint (scR s)
  qis : (qiR s).Disjoint (scR s)
  dgs : (dgR D s).Disjoint (scR s)
  sls : (sR s).Disjoint (scR s)
  sth : (scR s).Disjoint (tHR s)
  stg : (scR s).Disjoint (tGR s)
  sa : (scR s).Disjoint (aR pc s)
  ko : (kS pc s).Disjoint (oR s)
  kn : (kS pc s).Disjoint (nR s)
  ke : (kS pc s).Disjoint (eR s)
  kp : (kS pc s).Disjoint (pR s)
  kq : (kS pc s).Disjoint (qR s)
  kdp : (kS pc s).Disjoint (dpR s)
  kdq : (kS pc s).Disjoint (dqR s)
  kqi : (kS pc s).Disjoint (qiR s)
  kdg : (kS pc s).Disjoint (dgR D s)
  ksl : (kS pc s).Disjoint (sR s)
  ks : (kS pc s).Disjoint (scR s)
  kth : (kS pc s).Disjoint (tHR s)
  ktg : (kS pc s).Disjoint (tGR s)
  ka : (kS pc s).Disjoint (aR pc s)
  wo : (s.gpr .a0).toNat + (s.gpr .a1).toNat ≤ 2 ^ 64
  wn : (s.gpr .a2).toNat + (s.gpr .a3).toNat ≤ 2 ^ 64
  we : (s.gpr .a4).toNat + (s.gpr .a5).toNat ≤ 2 ^ 64
  wp : (s.gpr .a6).toNat + (s.gpr .a7).toNat ≤ 2 ^ 64
  wq : (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64
  wdp : (stackArg s 2).toNat + (stackArg s 3).toNat ≤ 2 ^ 64
  wdq : (stackArg s 4).toNat + (stackArg s 5).toNat ≤ 2 ^ 64
  wqi : (stackArg s 6).toNat + (stackArg s 7).toNat ≤ 2 ^ 64
  wdg : (stackArg s 8).toNat + D ≤ 2 ^ 64
  wsl : (stackArg s 10).toNat + (stackArg s 11).toNat ≤ 2 ^ 64
  wsc : (stackArg s 12).toNat + (stackArg s 13).toNat * 8 ≤ 2 ^ 64
  wth : (stackArg s 14).toNat + 88 ≤ 2 ^ 64
  wtg : (stackArg s 15).toNat + 88 ≤ 2 ^ 64
  k1 : 64 ≤ (s.gpr .a3).toNat
  k2 : (s.gpr .a3).toNat ≤ 1024
  ok : (s.gpr .a1).toNat = (s.gpr .a3).toNat
  e1 : 1 ≤ (s.gpr .a5).toNat
  e2 : (s.gpr .a5).toNat ≤ (s.gpr .a3).toNat
  p1 : 1 ≤ (s.gpr .a7).toNat
  p2 : (s.gpr .a7).toNat < (s.gpr .a3).toNat
  q1 : 1 ≤ (stackArg s 1).toNat
  q2 : (stackArg s 1).toNat < (s.gpr .a3).toNat
  h3 : (stackArg s 3).toNat = (s.gpr .a7).toNat
  h7 : (stackArg s 7).toNat = (s.gpr .a7).toNat
  h5 : (stackArg s 5).toNat = (stackArg s 1).toNat
  hs : Spec.RsaPss.scratchWords (s.gpr .a3).toNat ≤ (stackArg s 13).toNat
  als : (stackArg s 12).toNat % 8 = 0
  al14 : (stackArg s 14).toNat % 8 = 0
  al15 : (stackArg s 15).toNat % 8 = 0
  /-- With `pc`, `pre`'s facts. -/
  px : pc = true → PreXS s

/-- The contract, with the hash function one of the tables `tsH` of `MdHash`
and MGF1's one of the tables `tsG` of `MdHash`, and the stack of the frames and
of `vg_rsa_private_checked`. -/
abbrev signSpec (tsH tsG : List FnTable) : Contract isa :=
  Spec.RsaPss.signMdTableContract (abi.withTables Spec.RsaPss.signMdTableSig [("hash", tsH), ("mgf1", tsG)])
    (stackBytes false)

/-- Unfolds the precondition at `h`. -/
macro "sign_pre" " at " h:ident : tactic => `(tactic| (
  have e : stackBytes false = 3471 + 1 := rfl
  unfold signSpec at $h:ident
  rw [e] at $h:ident
  sig_pre [Spec.RsaPss.signMdTableContract, Spec.RsaPss.signMdTableSig, Spec.RsaPss.digestLenOk, Spec.MdHashTable.param,
    Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Abi.withTables, Sig.wordIndex, abi,
    argRegs, stackArgs_sixteen, List.append_eq, List.range, List.range.loop, Spec.Rsa.lenValid] at $h:ident
  sig_pre [Spec.RsaPss.signMdTableContract, Spec.RsaPss.signMdTableSig, Spec.RsaPss.digestLenOk, Spec.MdHashTable.param,
    Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Abi.withTables, Sig.wordIndex, abi,
    argRegs, stackArgs_sixteen, List.append_eq, List.range, List.range.loop, Spec.Rsa.lenValid] at $h:ident
  simp only [Option.map_some, Nat.reduceAdd, List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq,
    exists_eq_left'] at $h:ident))

theorem preS_of {H : Spec.Mgf1.Hash} {tsH tsG : List FnTable} {s : State} (h : (signSpec tsH tsG).pre s)
    (hH : Spec.MdHashTable.hashAt 64 s.mem (stackArg s 14) = some H) : PreS false H.len s := by
  sign_pre at h
  sig_split h
  rename_i spal sp1 sp2 _ _ _ hrd hwr on oe op oq odp odq oqi odg osl os oth otg oa ns es ps qs dps dqs qis dgs
    sls sth stg sa ko kn ke kp kq kdp kdq kqi kdg ksl ks kth ktg ka wo wn we wp wq wdp wdq wqi wdg wsl wsc wth
    wtg k1 k2 ok e1 e2 p1 p2 q1 q2 h3 h7 h5 hs hl als al14
  obtain hl := hl H hH
  rw [hl] at hrd odg dgs kdg wdg
  exact ⟨spal, sp1, sp2, hrd, hwr, on, oe, op, oq, odp, odq, oqi, odg, osl, os, oth, otg, oa, ns, es, ps, qs, dps,
    dqs, qis, dgs, sls, sth, stg, sa, ko, kn, ke, kp, kq, kdp, kdq, kqi, kdg, ksl, ks, kth, ktg, ka, wo, wn, we, wp,
    wq, wdp, wdq, wqi, wdg, wsl, wsc, wth, wtg, k1, k2, ok, e1, e2, p1, p2, q1, q2, h3, h7, h5, hs, als, al14, h,
    nofun⟩

/-- The tables, as the contract gives them: the hash function's one of `tsH`
at the stack argument 14 and MGF1's one of `tsG` at 15, with the functions of
distinct names at distinct addresses. -/
theorem spec_tabS {tsH tsG : List FnTable} {s : State} (h : (signSpec tsH tsG).pre s) :
    (∃ T ∈ tsH, Abi.tableHeld 64 s.mem (stackArg s 14) (FnTable.words isa s T)) ∧
      (∃ T ∈ tsG, Abi.tableHeld 64 s.mem (stackArg s 15) (FnTable.words isa s T)) ∧
      ((tsH.map (fun T : FnTable => T.fns)).flatten ++ (tsG.map (fun T : FnTable => T.fns)).flatten).Pairwise
        (fun f g => f ≠ g → s.syms f ≠ s.syms g) := by
  sign_pre at h
  exact ⟨h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩

/-! ## The working space and the registers the code keeps -/

/-- The working space. -/
abbrev Ss (s : State) : Addr := stackArg s 12

/-- `k`. -/
abbrev kk (s : State) : Nat := (s.gpr .a3).toNat

/-- The modulus' first byte, zero-extended. -/
def n0S (s : State) : BitVec 64 := (s.mem (s.gpr .a2)).setWidth 64

/-- `lo` of the modulus' first byte: 1 if `emLen = k - 1`. -/
abbrev loS (s : State) : BitVec 64 := loB (s.mem (s.gpr .a2))

/-- The values `Base` fixes in `s1`–`s4`: `k`, `out`, `lo` and `salt_len`. -/
def vS (s : State) : Reg → BitVec 64
  | .s1 => s.gpr .a3
  | .s2 => s.gpr .a0
  | .s3 => loS s
  | .s4 => stackArg s 11
  | _ => 0

section
variable {pc : Bool} {D : Nat} {s : State} (P : PreS pc D s)
include P

theorem scLen : oRsa ≤ (stackArg s 13).toNat * 8 := by
  have := P.hs; unfold Spec.RsaPss.scratchWords Spec.Rsa.scratchWords at this; unfold oRsa; omega_using [this]

theorem sc_sub : Region.Sub (SC Ss s) (scR s) := Region.sub_prefix (scLen P)

omit P in
theorem kR_sub : Region.Sub (kR s) (kS pc s) :=
  below_sub (by have := stackBytes_ge pc; unfold Proof.RsaOaep.RISCV64.stackBytes; omega_using [this])
    (by have := stackBytes_ge pc; omega_using [this])

/-- `Fits` for the entry state. -/
theorem fits : Fits Ss s where
  sp1 := by have := P.sp1; have := stackBytes_ge pc; unfold Proof.RsaOaep.RISCV64.stackBytes; omega_arith
  sp16 := P.spal
  sc := ⟨scR s, by rw [P.hwr]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _), rfl, scLen P⟩
  ksc := (P.ks.sub_left kR_sub).sub_right (sc_sub P)
  wS := by show (stackArg s 12).toNat + oRsa ≤ 2 ^ 64; have := P.wsc; have := scLen P; omega_arith

end

section
variable {s t : State} (h : Base Ss vS s t)
include h

theorem Base.sk : t.gpr .s1 = s.gpr .a3 := h.vs .s1 (by decide)
theorem Base.sout : t.gpr .s2 = s.gpr .a0 := h.vs .s2 (by decide)
theorem Base.slo : t.gpr .s3 = loS s := h.vs .s3 (by decide)
theorem Base.ssl : t.gpr .s4 = stackArg s 11 := h.vs .s4 (by decide)

end

/-! ## The entry -/

/-- The stack arguments are in `aR`. -/
theorem in_aR {pc : Bool} {s : State} {j : Nat} (hj : j < 16) : (aR pc s).Contains (stackArgAddr s j) 8 := by
  rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by split <;> omega_using [hj]) (by omega_using [hj])

/-- With `pc`, the stack arguments 16 and 17 too. -/
theorem in_aR18 {s : State} {j : Nat} (hj : j < 18) : (aR true s).Contains (stackArgAddr s j) 8 := by
  rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by simp only [↓reduceIte]; omega_using [hj]) (by omega_using [hj])

/-- `n`, `e`, `e_len`, `p`, `p_len` and the mask `c` in the six words at `scratch + oP`. -/
structure Spilled (s : State) (m : Mem) : Prop where
  n : m.readW (off (Ss s) oP) 64 = s.gpr .a2
  e : m.readW (off (Ss s) (oP + 8)) 64 = s.gpr .a4
  el : m.readW (off (Ss s) (oP + 16)) 64 = s.gpr .a5
  p : m.readW (off (Ss s) (oP + 24)) 64 = s.gpr .a6
  pl : m.readW (off (Ss s) (oP + 32)) 64 = s.gpr .a7
  c : m.readW (off (Ss s) (oP + 40)) 64 = Proof.RsaPss.RISCV64.cmB (s.mem (s.gpr .a2))

/-- After the saves and the prologue. -/
structure Entered (s t : State) : Prop where
  base : Base Ss vS s t
  t1 : t.gpr .t1 = n0S s
  sp : Spilled s t.mem

section
variable {pc : Bool} {D : Nat} {s : State} (P : PreS pc D s)
include P

theorem arg_al {j : Nat} (hj : j < 16) : (stackArgAddr s j).toNat % 8 = 0 := by
  have := P.spal; have : s.sp.toNat + 128 ≤ 2 ^ 64 := by have := P.sp2; split at this <;> omega_using [this]
  obtain e : (stackArgAddr s j).toNat = s.sp.toNat + 8 * j := by
    simp only [stackArgAddr, BitVec.toNat_add, BitVec.toNat_ofNat]; omega_using [hj, this]
  rw [e]; omega_arith

omit P in
/-- With `pc`, the stack arguments 16 and 17 too. -/
theorem arg_al18 (P : PreS true D s) {j : Nat} (hj : j < 18) : (stackArgAddr s j).toNat % 8 = 0 := by
  have := P.spal; have : s.sp.toNat + 144 ≤ 2 ^ 64 := P.sp2
  obtain e : (stackArgAddr s j).toNat = s.sp.toNat + 8 * j := by
    simp only [stackArgAddr, BitVec.toNat_add, BitVec.toNat_ofNat]; omega_using [hj, this]
  rw [e]; omega_arith

theorem fb_al8 : (fb s).toNat % 8 = 0 := by
  have := fb_al (fits P); omega_using [this]

theorem oP_al (j : Nat) : (off (Ss s) (oP + 8 * j)).toNat % 8 = 0 := by
  have := P.als
  obtain e : (off (stackArg s 12) (oP + 8 * j)).toNat = (stackArg s 12).toNat + (oP + 8 * j) % 2 ^ 64 ∨
      (off (stackArg s 12) (oP + 8 * j)).toNat = ((stackArg s 12).toNat + (oP + 8 * j) % 2 ^ 64) - 2 ^ 64 := by
    simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]; omega_using []
  show (off (stackArg s 12) (oP + 8 * j)).toNat % 8 = 0
  unfold oP at *; omega_using [this, e]

/-- A load of our stack argument `j` through `t6`, the entry stack pointer,
with memory changed only in the stack and our part of the working space. -/
theorem wp_arg {t : State} {r : Reg} {j : Nat} {is : List Instr} {Q : State → Prop} (hj : j < 16)
    (h6 : t.gpr .t6 = s.sp) (hrd : t.rd = s.rd) (hm : Frame [kR s, SC Ss s] s.mem t.mem)
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

end

section
variable {pc : Bool} {D : Nat} {s : State} (P : PreS pc D s)
include P

omit P in
theorem sc_c8 (j : Nat) (hj : j < 6) : (SC Ss s).Contains (off (Ss s) (oP + 8 * j)) (64 / 8) :=
  Offset.contains_base (Ss s) (by unfold oP oRsa; omega_using [hj]) (by unfold oP; omega_using [hj])

/-- After the saves and the prologue. -/
structure Pro (s t : State) : Prop where
  sv : Saves s t
  rd : t.rd = s.rd
  s0 : t.gpr .s0 = Ss s
  s1 : t.gpr .s1 = s.gpr .a3
  s2 : t.gpr .s2 = s.gpr .a0
  s4 : t.gpr .s4 = stackArg s 11
  args : ∀ r ∈ [Reg.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7], t.gpr r = s.gpr r
  mem : Frame [kR s, SC Ss s] s.mem t.mem

theorem pro_ok : WP isa (.block (save ++ prologue)) (allocd frameBytes s) (Pro s) := by
  refine save_ok (u := allocd frameBytes s) rfl rfl (fb_al8 P) (Frame.refl _ _) (fun r _ => rfl)
    fun v kv h0 hm hsv => ?_
  have hrd : v.rd = s.rd := kv.rd
  have hsp : v.sp = fb s := kv.sp
  obtain hm2 : Frame [kR s, SC Ss s] s.mem v.mem := hm.mono fun r hr => by rw [List.mem_singleton.mp hr]; simp
  obtain gs : ∀ r ∈ [Reg.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7], v.gpr r = s.gpr r := fun r hr => by
    rw [kv.gpr r (by revert r; decide)]; rfl
  simp only [prologue, Impl.RsaOaep.RISCV64.argBase]
  refine wp_addSp fun v₁ o₁ e₁ => ?_
  obtain g6 : v₁.gpr .t6 = s.sp := by rw [e₁, hsp, BitVec.sub_add_cancel]
  refine wp_arg P (j := 12) (by decide) g6 (o₁.rd.trans hrd) (by rw [o₁.mem]; exact hm2) fun v₂ o₂ e₂ => ?_
  refine wp_mov fun v₃ o₃ e₃ => wp_mov fun v₄ o₄ e₄ => ?_
  refine wp_arg P (j := 11) (by decide) (by rw [o₄.get .t6, o₃.get .t6, o₂.get .t6, g6])
    (by rw [o₄.rd, o₃.rd, o₂.rd, o₁.rd, hrd]) (by rw [o₄.mem, o₃.mem, o₂.mem, o₁.mem]; exact hm2)
    fun v₅ o₅ e₅ => wp_nil ?_
  obtain k₅ : Only [.t6, .s0, .s1, .s2, .s4] v v₅ := (o₁.trans (o₂.trans (o₃.trans (o₄.trans o₅)))).mono
  obtain sv0 : Saves s v := ⟨hsp, by rw [kv.wr]; rfl, hsv⟩
  exact ⟨sv0.keep k₅.keep (R := []) (by rw [k₅.mem]; exact Frame.refl _ _) (by simp), by rw [k₅.rd, hrd],
    by rw [o₅.get .s0, o₄.get .s0, o₃.get .s0, e₂],
    by rw [o₅.get .s1, o₄.get .s1, e₃, o₂.get .a3, o₁.get .a3, gs .a3 (by decide)],
    by rw [o₅.get .s2, e₄, o₃.get .a0, o₂.get .a0, o₁.get .a0, gs .a0 (by decide)], e₅,
    fun r hr => by rw [k₅.gpr r (by revert r; decide), gs r hr], by rw [k₅.mem]; exact hm2⟩

theorem spill_ok {v₅ : State} (E : Pro s v₅) : WP isa (.block spill) v₅ (Entered s) := by
  obtain F := fits P
  have hrd : v₅.rd = s.rd := E.rd
  have hm2 : Frame [kR s, SC Ss s] s.mem v₅.mem := E.mem
  have a5 := E.args
  have g0 : v₅.gpr .s0 = Ss s := E.s0
  simp only [spill, Impl.RsaPss.RISCV64.Sign.smear, Impl.RsaPss.RISCV64.Sign.cMask, List.cons_append,
    List.nil_append]
  obtain w8 : ∀ {u : State} (j : Nat), u.wr = v₅.wr → j < 6 → InRegions u.wr (off (Ss s) (oP + 8 * j)) 8 :=
    fun j hu hj => by
      rw [hu, E.sv.wr]; exact sc_inW F (by unfold oP oRsa; omega_using [hj])
  refine wp_sd (a := off (Ss s) oP) (by rw [g0]) (by simpa using oP_al P 0) (by simpa using w8 0 rfl (by decide))
    fun v₆ m₆ => ?_
  refine wp_sd (a := off (Ss s) (oP + 8)) (by rw [m₆.gpr, g0]) (oP_al P 1) (w8 1 m₆.wr (by decide))
    fun v₇ m₇ => ?_
  refine wp_sd (a := off (Ss s) (oP + 16)) (by rw [m₇.gpr, m₆.gpr, g0]) (oP_al P 2)
    (w8 2 (m₇.wr.trans m₆.wr) (by decide)) fun v₈ m₈ => ?_
  refine wp_sd (a := off (Ss s) (oP + 24)) (by rw [m₈.gpr, m₇.gpr, m₆.gpr, g0]) (oP_al P 3)
    (w8 3 (m₈.wr.trans (m₇.wr.trans m₆.wr)) (by decide)) fun v₉ m₉ => ?_
  refine wp_sd (a := off (Ss s) (oP + 32)) (by rw [m₉.gpr, m₈.gpr, m₇.gpr, m₆.gpr, g0]) (oP_al P 4)
    (w8 4 (m₉.wr.trans (m₈.wr.trans (m₇.wr.trans m₆.wr))) (by decide)) fun v₁₀ m₁₀ => ?_
  obtain kg : v₁₀.gpr = v₅.gpr := by rw [m₁₀.gpr, m₉.gpr, m₈.gpr, m₇.gpr, m₆.gpr]
  obtain hn : nR s ∈ s.rd := by rw [P.hrd]; simp
  obtain hc : (nR s).Contains (s.gpr .a2) 1 := by
    have := Offset.contains_base (s.gpr .a2) (d := 0) (n := 1) (k := (s.gpr .a3).toNat) (by have := P.k1; omega_using [this])
      (by decide)
    simpa only [BitVec.add_zero] using this
  obtain hf1 : Frame [SC Ss s] v₅.mem v₁₀.mem := by
    rw [m₁₀.mem, m₉.mem, m₈.mem, m₇.mem, m₆.mem]
    obtain hS : SC Ss s ∈ [SC Ss s] := List.mem_singleton_self _
    exact (((((Frame.refl _ _).writeW hS _ (by simpa using sc_c8 0 (by decide))).writeW hS _
      (sc_c8 1 (by decide))).writeW hS _ (sc_c8 2 (by decide))).writeW hS _ (sc_c8 3 (by decide))).writeW hS _
      (sc_c8 4 (by decide))
  obtain hf : Frame [kR s, SC Ss s] s.mem v₁₀.mem := hm2.trans (hf1.mono (by simp))
  refine wp_lbu (a := s.gpr .a2) (by rw [kg, a5 .a2 (by decide), BitVec.add_zero])
    (by rw [m₁₀.rd, m₉.rd, m₈.rd, m₇.rd, m₆.rd, hrd]; exact ⟨nR s, List.mem_append_left _ hn, hc⟩)
    fun v₁₁ o₁₁ e₁₁ => ?_
  refine wp_srl fun v₁₂ o₁₂ e₁₂ => wp_srl fun v₁₃ o₁₃ e₁₃ => wp_or fun v₁₄ o₁₄ e₁₄ => wp_srl fun v₁₅ o₁₅ e₁₅ =>
    wp_or fun v₁₆ o₁₆ e₁₆ => wp_srl fun v₁₇ o₁₇ e₁₇ => wp_or fun v₁₈ o₁₈ e₁₈ =>
    wp_subi (imm := 1) fun v₁₉ o₁₉ e₁₉ => wp_srl fun w ow ew => ?_
  obtain hb : v₁₁.gpr .t1 = n0S s := by
    rw [e₁₁]
    show (v₁₀.mem (s.gpr .a2)).setWidth 64 = (s.mem (s.gpr .a2)).setWidth 64
    rw [hf _ fun r hr hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (P.kn.sub_left kR_sub) _ hx hc
      · exact (P.ns.sub_right (sc_sub P)).symm _ hx hc]
  obtain m18 : v₁₈.gpr .t2 = Proof.RsaPss.RISCV64.smB (s.mem (s.gpr .a2)) := by
    rw [e₁₈, o₁₇.get .t2, e₁₇, e₁₆, o₁₅.get .t2, e₁₅, e₁₄, o₁₃.get .t2, e₁₃, e₁₂, hb]; rfl
  obtain m20 : w.gpr .s3 = loS s := by rw [ew, e₁₉, m18]; rfl
  -- The mask `c`.
  refine wp_li (imm := 0) (by decide) fun y₁ p₁ f₁ => wp_sub fun y₂ p₂ f₂ =>
    wp_li (imm := 0xFF) (by decide) fun y₃ p₃ f₃ => wp_and fun y₄ p₄ f₄ => wp_or fun y₅ p₅ f₅ => ?_
  obtain kw : Only [.t1, .t2, .t3, .s3, .t4] v₁₀ y₅ :=
    (o₁₁.trans (o₁₂.trans (o₁₃.trans (o₁₄.trans (o₁₅.trans (o₁₆.trans (o₁₇.trans (o₁₈.trans (o₁₉.trans (ow.trans (p₁.trans (p₂.trans (p₃.trans (p₄.trans p₅)))))))))))))).mono
  obtain c5 : y₅.gpr .t2 = Proof.RsaPss.RISCV64.cmB (s.mem (s.gpr .a2)) := by
    rw [f₅, p₄.get .t2, p₃.get .t2, p₂.get .t2, p₁.get .t2, ow.get .t2, o₁₉.get .t2, m18, f₄, p₃.get .t3, f₂,
      f₁, p₁.get .s3, m20, f₃]; rfl
  refine wp_sd (a := off (Ss s) (oP + 40)) (by rw [kw.get .s0, kg, g0]) (oP_al P 5)
    (w8 5 (by rw [kw.wr, m₁₀.wr, m₉.wr, m₈.wr, m₇.wr, m₆.wr]) (by decide)) fun y m => wp_nil ?_
  obtain hm : y.mem = v₁₀.mem.writeW (off (Ss s) (oP + 40)) (Proof.RsaPss.RISCV64.cmB (s.mem (s.gpr .a2))) := by
    rw [m.mem, c5, kw.mem]
  obtain kK : Kept [.t1, .t2, .t3, .s3, .t4] v₅ y :=
    (m₆.keep.trans (m₇.keep.trans (m₈.keep.trans (m₉.keep.trans (m₁₀.keep.trans
      (kw.keep.trans m.keep)))))).mono
  obtain hS : SC Ss s ∈ [SC Ss s] := List.mem_singleton_self _
  obtain hfy : Frame [SC Ss s] v₅.mem y.mem := by rw [hm]; exact hf1.writeW hS _ (sc_c8 5 (by decide))
  obtain sv : Saves s y := E.sv.keep kK hfy fun r hr => by
    rw [List.mem_singleton.mp hr]; exact Proof.RsaOaep.RISCV64.slR_sc F
  obtain hfa : Frame [kR s, SC Ss s] s.mem y.mem := hm2.trans (hfy.mono (by simp))
  obtain sp : Spilled s y.mem := by
    rw [hm, m₁₀.mem, m₉.mem, m₈.mem, m₇.mem, m₆.mem]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Mem.readW_writeW_sep (Offset.sep _ (.inl (by unfold oP; omega_using [])) (by unfold oP; omega_using []) (by unfold oP; omega_using [])) (by decide),
        Mem.readW_writeW_sep (Offset.sep _ (.inl (by unfold oP; omega_using [])) (by unfold oP; omega_using []) (by unfold oP; omega_using [])) (by decide),
        Mem.readW_writeW_sep (Offset.sep _ (.inl (by unfold oP; omega_using [])) (by unfold oP; omega_using []) (by unfold oP; omega_using [])) (by decide),
        Mem.readW_writeW_sep (Offset.sep _ (.inl (by unfold oP; omega_using [])) (by unfold oP; omega_using []) (by unfold oP; omega_using [])) (by decide),
        Mem.readW_writeW_sep (Offset.sep _ (.inl (by unfold oP; omega_using [])) (by unfold oP; omega_using []) (by unfold oP; omega_using [])) (by decide),
        Mem.readW_writeW_self64, a5 .a2 (by decide)]
    · rw [Mem.readW_writeW_sep (Offset.sep _ (.inl (by unfold oP; omega_using [])) (by unfold oP; omega_using []) (by unfold oP; omega_using [])) (by decide),
        Mem.readW_writeW_sep (Offset.sep _ (.inl (by unfold oP; omega_using [])) (by unfold oP; omega_using []) (by unfold oP; omega_using [])) (by decide),
        Mem.readW_writeW_sep (Offset.sep _ (.inl (by unfold oP; omega_using [])) (by unfold oP; omega_using []) (by unfold oP; omega_using [])) (by decide),
        Mem.readW_writeW_sep (Offset.sep _ (.inl (by unfold oP; omega_using [])) (by unfold oP; omega_using []) (by unfold oP; omega_using [])) (by decide),
        Mem.readW_writeW_self64, m₆.gpr, a5 .a4 (by decide)]
    · rw [Mem.readW_writeW_sep (Offset.sep _ (.inl (by unfold oP; omega_using [])) (by unfold oP; omega_using []) (by unfold oP; omega_using [])) (by decide),
        Mem.readW_writeW_sep (Offset.sep _ (.inl (by unfold oP; omega_using [])) (by unfold oP; omega_using []) (by unfold oP; omega_using [])) (by decide),
        Mem.readW_writeW_sep (Offset.sep _ (.inl (by unfold oP; omega_using [])) (by unfold oP; omega_using []) (by unfold oP; omega_using [])) (by decide),
        Mem.readW_writeW_self64, m₇.gpr, m₆.gpr, a5 .a5 (by decide)]
    · rw [Mem.readW_writeW_sep (Offset.sep _ (.inl (by unfold oP; omega_using [])) (by unfold oP; omega_using []) (by unfold oP; omega_using [])) (by decide),
        Mem.readW_writeW_sep (Offset.sep _ (.inl (by unfold oP; omega_using [])) (by unfold oP; omega_using []) (by unfold oP; omega_using [])) (by decide),
        Mem.readW_writeW_self64, m₈.gpr, m₇.gpr, m₆.gpr, a5 .a6 (by decide)]
    · rw [Mem.readW_writeW_sep (Offset.sep _ (.inl (by unfold oP; omega_using [])) (by unfold oP; omega_using []) (by unfold oP; omega_using [])) (by decide),
        Mem.readW_writeW_self64, m₉.gpr, m₈.gpr, m₇.gpr, m₆.gpr, a5 .a7 (by decide)]
    · rw [Mem.readW_writeW_self64]
  refine ⟨⟨sv, by rw [m.rd, kw.rd, m₁₀.rd, m₉.rd, m₈.rd, m₇.rd, m₆.rd, hrd],
    by rw [m.gpr, kw.get .s0, kg, g0], fun r hr => ?_, hfa⟩,
    by rw [m.gpr, (o₁₂.trans (o₁₃.trans (o₁₄.trans (o₁₅.trans (o₁₆.trans (o₁₇.trans (o₁₈.trans (o₁₉.trans
      (ow.trans (p₁.trans (p₂.trans (p₃.trans (p₄.trans p₅))))))))))))).get .t1, hb], sp⟩
  simp only [Proof.RsaOaep.RISCV64.fx, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> simp only [vS] <;> rw [m.gpr]
  · rw [kw.get .s1, kg]; exact E.s1
  · rw [kw.get .s2, kg]; exact E.s2
  · rw [p₅.get .s3, p₄.get .s3, p₃.get .s3, p₂.get .s3, p₁.get .s3]; exact m20
  · rw [kw.get .s4, kg]; exact E.s4

end

end VG.Proof.RsaPss.RISCV64.Sg

end

end

/-!
# RSASSA-PSS signing on RISC-V: the checks, and the outcome by cases

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaPss/PPC64LE/Sg/Checks.lean`, `Sg/Spec.lean`): for a modulus whose
first byte is not zero, `lo` is EMSA-PSS's (`lo_eq`); `chkEm_ok` and
`chkSalt_ok`: whether `emLen < hLen + 2` and whether the salt is longer than
`emLen - hLen - 2`, in `a0`; `fail_ok`: `encFail` writes zeros to `out` and
returns 0. `signOut G s`, what the contract asks of a call from `s`: it is
`invalid` if the modulus' first byte is zero (`signOut_zero`) or the salt
does not fit (`signOut_long`), and otherwise the private operation
(`privOut`) on the encoding `encEm`, with `lo` and the mask `c` the code
computes (`signOut_eq`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.RISCV64.Sg

open VG VG.RISCV64 VG.Impl.RsaPss.RISCV64.Sign VG.WriteBytes
open VG.Impl.RsaOaep.RISCV64 (encFail)
open VG.Proof.RsaOaep.RISCV64 (Base Fits fx Saves kR ne_zero_ltBit msgBit slR_sub)
open VG.Proof.RsaPkcs1Sig.RISCV64 (Only wp_li wp_sub wp_subi wp_srl wp_or wp_mov wp_nil fill_ok)

/-- `lo` as a number. -/
def loN (s : State) : Nat := if (s.mem (s.gpr .a2)).toNat = 1 then 1 else 0

theorem ofNat_toNat (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by simp

theorem loN_le (s : State) : loN s ≤ 1 := by unfold loN; split <;> omega_using []

theorem lo_eq {s : State} (h0 : s.mem (s.gpr .a2) ≠ 0) : loS s = BitVec.ofNat 64 (loN s) := by
  have hn : (s.mem (s.gpr .a2)).toNat ≠ 0 := fun h => h0 (BitVec.eq_of_toNat_eq h)
  have := (Proof.RsaPss.RISCV64.byte_ok _ (s.mem (s.gpr .a2)).isLt hn).1
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq] at this
  exact this

section
variable {pc : Bool} {D : Nat} {s : State} (P : PreS pc D s)
include P

theorem Entered.only {t t' : State} {rs : List Reg} (E : Entered s t) (o : Only rs t t')
    (hrs : ∀ r ∈ rs, r ∉ .s0 :: fx ++ ([.t1] : List Reg) := by decide) : Entered s t' :=
  ⟨E.base.only (fits P) o fun r h h' => hrs r h (List.mem_append_left _ h'),
    (o.gpr .t1 fun h => hrs _ h (List.mem_append_right _ (List.mem_singleton_self _))).trans E.t1,
    by rw [o.mem]; exact E.sp⟩

theorem k_lo (h0 : s.mem (s.gpr .a2) ≠ 0) : s.gpr .a3 - loS s = BitVec.ofNat 64 (kk s - loN s) := by
  have hk1 : 64 ≤ kk s := P.k1
  have ek : (s.gpr .a3).toNat = kk s := rfl
  have := loN_le s
  rw [lo_eq h0, ← ofNat_toNat (s.gpr .a3), Offset.ofNat_sub_ofNat (by omega_using [hk1, ek, this])]

/-- `chkEm`: whether `emLen < hLen + 2`. -/
theorem chkEm_ok {H : Impl.Hmac.Stream.RISCV64.Hash} (hD64 : H.D ≤ 64) {t : State} (E : Entered s t)
    (h0 : s.mem (s.gpr .a2) ≠ 0) :
    WP isa (.block (chkEm H)) t fun t' => Entered s t' ∧
      (t'.gpr .a0 != 0) = decide (kk s - loN s < H.D + 2) := by
  have hk2 : kk s ≤ 1024 := P.k2
  refine wp_sub fun t₁ o₁ e₁ => wp_subi (imm := H.D + 2) (h := by omega_using [hD64]) fun t₂ o₂ e₂ => wp_srl fun t₃ o₃ e₃ =>
    wp_nil ?_
  have k₃ : Only [.a0] t t₃ := (o₁.trans (o₂.trans o₃)).mono
  refine ⟨E.only P k₃, ?_⟩
  rw [e₃, e₂, e₁, Base.sk E.base, Base.slo E.base, k_lo P h0]
  exact ne_zero_ltBit (by omega_using [hk2]) (by omega_using [hD64])

/-- `chkSalt`: whether the salt is longer than `emLen - hLen - 2`. -/
theorem chkSalt_ok {H : Impl.Hmac.Stream.RISCV64.Hash} (hD64 : H.D ≤ 64) {t : State} (E : Entered s t)
    (h0 : s.mem (s.gpr .a2) ≠ 0) (hem : H.D + 2 ≤ kk s - loN s) :
    WP isa (.block (chkSalt H)) t fun t' => Entered s t' ∧
      (t'.gpr .a0 != 0) = decide (kk s - loN s - (H.D + 2) < (stackArg s 11).toNat) := by
  have hk2 : kk s ≤ 1024 := P.k2
  refine wp_sub fun t₅ o₅ e₅ => wp_subi (imm := H.D + 2) (h := by omega_using [hD64]) fun t₆ o₆ e₆ => wp_sub fun t₇ o₇ e₇ =>
    wp_srl fun t₈ o₈ e₈ => wp_srl fun t₉ o₉ e₉ => wp_or fun t₁₀ o₁₀ e₁₀ => wp_nil ?_
  have k₁₀ : Only [.a0, .a2] t t₁₀ := (o₅.trans (o₆.trans (o₇.trans (o₈.trans (o₉.trans o₁₀))))).mono
  refine ⟨E.only P k₁₀, ?_⟩
  rw [e₁₀, o₉.get .a0, e₉, e₈, o₈.get .s4, e₇, o₇.get .s4, e₆, o₆.get .s4, e₅, o₅.get .s4, Base.sk E.base,
    Base.slo E.base, Base.ssl E.base, k_lo P h0, Offset.ofNat_sub_ofNat hem, BitVec.or_comm]
  have := msgBit (x := kk s - loN s - (H.D + 2)) (y := (stackArg s 11).toNat) (by omega_using [hk2]) (BitVec.isLt _)
  rwa [ofNat_toNat] at this

theorem oR_eq : oR s = ⟨s.gpr .a0, (s.gpr .a3).toNat⟩ := by rw [oR, P.ok]

/-- `encFail`: zeros to `out`, and 0. -/
theorem fail_ok {t : State} (h : Base Ss vS s t) :
    WP isa encFail t fun t' => Saves s t' ∧ t'.rd = s.rd ∧ t'.gpr .a0 = 0 ∧
      Spec.Rsa.bytesAt t'.mem (s.gpr .a0) (kk s) = List.replicate (kk s) 0 := by
  have hk1 := P.k1; have hk2 := P.k2
  have ek : kk s = (s.gpr .a3).toNat := rfl
  refine WP.seq (WP.seq (wp_mov fun t₁ o₁ e₁ => wp_mov fun t₂ o₂ e₂ => wp_li (imm := 0) (by decide)
    fun t₃ o₃ e₃ => wp_nil ?_))
  have k₃ : Only [.a1, .t5, .t0] t t₃ := (o₁.trans (o₂.trans o₃)).mono
  have hout : ∀ i < kk s, InRegions t₃.wr (s.gpr .a0 + BitVec.ofNat 64 i) 1 := fun i hi => by
    rw [k₃.wr, h.wr]
    exact ⟨oR s, List.mem_cons_of_mem _ (by rw [P.hwr]; simp),
      Offset.contains_base _ (by rw [P.ok]; omega_using [ek, hi]) (by have := P.wo; omega_using [ek, hi])⟩
  refine WP.mono (fill_ok (p := s.gpr .a0) (n := kk s) (b := 0) (by omega_using [hk1, ek]) (by omega_using [ek])
    (by rw [o₃.get .a1, o₂.get .a1, e₁, Base.sout h]) (by rw [o₃.get .t5, e₂, o₁.get .s1, Base.sk h]; simp)
    (by rw [e₃]; rfl) hout) fun t₄ ⟨k₄, m₄⟩ => wp_li (imm := 0) (by decide) fun t₅ o₅ e₅ => wp_nil ?_
  have hko : (kR s).Disjoint ⟨s.gpr .a0, (s.gpr .a3).toNat⟩ := by
    rw [← oR_eq P]; exact P.ko.sub_left kR_sub
  have hf : Frame [⟨s.gpr .a0, kk s⟩] t.mem t₅.mem := by
    have := Proof.RsaPkcs1Sig.frame_writeBytes t₃.mem (s.gpr .a0) (List.replicate (kk s) (0 : Byte))
    rw [List.length_replicate] at this
    rw [o₅.mem, m₄, ← k₃.mem] at *; exact this
  have K := (k₃.keep.trans (k₄.trans o₅.keep)).mono (rs' := [.a0, .a1, .t5, .t0])
  refine ⟨h.sv.keep K hf (fun r hr => by rw [List.mem_singleton.mp hr]; exact hko.sub_left (slR_sub s)),
    K.rd.trans h.rd, by rw [e₅]; rfl, ?_⟩
  have := Proof.RsaPkcs1Sig.bytesAt_writeBytes t₃.mem (s.gpr .a0) (List.replicate (kk s) (0 : Byte))
    (by simp; omega_using [ek])
  rw [List.length_replicate] at this
  rw [o₅.mem, m₄, this]

end

end VG.Proof.RsaPss.RISCV64.Sg

namespace VG.Proof.RsaPss.RISCV64.Sg

open VG VG.RISCV64
open VG.Proof.RsaPss.RISCV64 (cmB byte_ok)

/-- The digest and the salt, from the entry state. -/
abbrev digB (D : Nat) (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (stackArg s 8) D
abbrev saltB (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (stackArg s 10) (stackArg s 11).toNat

variable (H G : Spec.Mgf1.Hash)

/-- The private operation on `em`, with the entry's key. -/
def privOut (s : State) (em : List Byte) : Spec.Rsa.Outcome :=
  Spec.Rsa.privateChecked (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat) em
    (Spec.Rsa.bytesAt s.mem (s.gpr .a6) (s.gpr .a7).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 2) (s.gpr .a7).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 4) (stackArg s 1).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 6) (s.gpr .a7).toNat)

/-- The outcome `signMdTableContract.post` asks for. -/
def signOut (s : State) : Spec.Rsa.Outcome :=
  Spec.RsaPss.sign H G (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .a6) (s.gpr .a7).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 2) (s.gpr .a7).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 4) (stackArg s 1).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 6) (s.gpr .a7).toNat)
    (digB H.len s) (saltB s)

/-- `H = Hash(0⁸ ‖ mHash ‖ salt)`. -/
abbrev hS (s : State) : List Byte := H.hash (Spec.RsaPss.zeros 8 ++ digB H.len s ++ saltB s)

/-- `dbLen`. -/
abbrev dbS (s : State) : Nat := kk s - loN s - H.len - 1

/-- The mask of `maskedDB`'s first byte, as a byte. -/
abbrev cS (s : State) : Byte := (cmB (s.mem (s.gpr .a2))).setWidth 8

/-- The encoding, as `k` bytes. -/
def encEm (s : State) : List Byte :=
  (List.range (kk s)).map (RsaPss.emT (loN s) (dbS H s) (stackArg s 11).toNat (saltB s) (hS H s)
    (Spec.Mgf1.mgf1 G (hS H s) (dbS H s)) (cS s))

theorem bytesAt_cons (m : Mem) (p : Addr) {k : Nat} (hk : 1 ≤ k) :
    Spec.Rsa.bytesAt m p k = m p :: Spec.Rsa.bytesAt m (p + 1) (k - 1) := by
  obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega_using [hk]⟩
  simp only [Spec.Rsa.bytesAt, List.range_succ_eq_map, List.map_cons, List.map_map, Nat.add_sub_cancel]
  refine List.cons_eq_cons.mpr ⟨by simp, List.map_congr_left fun i _ => ?_⟩
  simp only [Function.comp, BitVec.add_assoc]
  rw [show (1 : Addr) + BitVec.ofNat 64 i = BitVec.ofNat 64 (i + 1) by
    rw [BitVec.add_comm, ← BitVec.ofNat_add_ofNat]; rfl]

theorem signOut_zero {s : State} (hk : 1 ≤ kk s) (h0 : s.mem (s.gpr .a2) = 0) : signOut H G s = .invalid := by
  unfold signOut
  rw [bytesAt_cons _ _ hk, h0]
  exact RsaPss.sign_zero₂ G H ..

theorem emLen_eq {s : State} (hk : 1 ≤ kk s) (h0 : s.mem (s.gpr .a2) ≠ 0) :
    Spec.RsaPss.emLength (Spec.RsaPss.bitLength (Spec.Rsa.os2ip
      (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (kk s))) - 1) = kk s - loN s := by
  rw [bytesAt_cons _ _ hk, RsaPss.emLength_eq _ h0, VG.Proof.RsaPkcs1Sig.bytesAt_length]
  unfold loN
  split <;> omega_arith

theorem signOut_long {s : State} (hk : 1 ≤ kk s) (h0 : s.mem (s.gpr .a2) ≠ 0)
    (h : kk s - loN s < H.len + (stackArg s 11).toNat + 2) : signOut H G s = .invalid := by
  unfold signOut
  refine RsaPss.sign_long₂ G H _ _ _ _ _ _ _ _ ?_
  rw [emLen_eq hk h0, VG.Proof.RsaPkcs1Sig.bytesAt_length]
  exact h

theorem cS_eq {s : State} (h0 : s.mem (s.gpr .a2) ≠ 0) :
    cS s = if (s.mem (s.gpr .a2)).toNat = 1 then 0xFF
      else BitVec.ofNat 8 (2 ^ Nat.log2 (s.mem (s.gpr .a2)).toNat - 1) := by
  have hn : (s.mem (s.gpr .a2)).toNat ≠ 0 := fun h => h0 (BitVec.eq_of_toNat_eq h)
  have := (byte_ok _ (s.mem (s.gpr .a2)).isLt hn).2
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq] at this
  unfold cS
  rw [this]
  split
  · rfl
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    exact Nat.mod_mod_of_dvd _ (by decide)

theorem signOut_eq (hH : Proof.Mgf1.Valid H) (hG : Proof.Mgf1.Valid G) {s : State} (hk : 1 ≤ kk s)
    (h0 : s.mem (s.gpr .a2) ≠ 0) (hfit : H.len + (stackArg s 11).toNat + 2 ≤ kk s - loN s) :
    signOut H G s = privOut s (encEm H G s) := by
  have hel := emLen_eq hk h0
  have hc := RsaPss.mask_eq (Spec.Rsa.bytesAt s.mem (s.gpr .a2 + 1) (kk s - 1)) h0
  unfold signOut privOut encEm
  generalize hnB : Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat = nB at hel ⊢
  rw [bytesAt_cons _ _ hk] at hnB
  subst hnB
  rw [RsaPss.sign_eq₂ G H hH hG h0 (lo := loN s) (db := dbS H s)
    (VG.Proof.RsaPkcs1Sig.bytesAt_length _ _ _) rfl hel
    (by rw [List.length_cons, VG.Proof.RsaPkcs1Sig.bytesAt_length]; unfold loN; split <;> omega_arith) rfl
    (by rw [VG.Proof.RsaPkcs1Sig.bytesAt_length]; exact hfit)]
  rw [hel] at hc
  rw [hc, ← cS_eq h0]
  simp only [List.length_cons, VG.Proof.RsaPkcs1Sig.bytesAt_length]
  rw [Nat.sub_add_cancel hk]

end VG.Proof.RsaPss.RISCV64.Sg
