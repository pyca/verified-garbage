module

public import VerifiedGarbage.Spec.RsaPss.MdTable
public import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Base
public import VerifiedGarbage.Impl.RsaPss.PPC64LE.Sign
import VerifiedGarbage.Proof.Framework.Offset

/-!
# RSASSA-PSS signing on PPC64LE: the precondition

Untrusted: everything here is checked by Lean. `PreS D s`: the shared
contract's precondition (`Spec.RsaPss.signMdTableContract`, with the stack of the
frames and of `vg_rsa_private_checked`, `stackBytes`), by name (`preS_of`),
for a digest of `D` bytes; the working space `Ss s` and the values the code
keeps in `r15`–`r23` (`vS s`), both functions of the entry state `s` alone,
as `Base` takes them, all public; and `Fits` for any state with `s`'s stack
pointer and regions.
-/

@[expose] public section

namespace VG.Proof.RsaPss.PPC64LE.Sg

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE VG.Impl.RsaPss.PPC64LE.Sign
open VG.Proof.RsaOaep.PPC64LE

theorem stackArgs_sixteen (s : State) :
    List.map (stackArg s) (List.range 16) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9, stackArg s 10,
      stackArg s 11, stackArg s 12, stackArg s 13, stackArg s 14, stackArg s 15] := rfl

/-- The stack the function uses: its frame (`frameBytes`), the private
operation's (`privBytes`) and that function's own. -/
def stackBytes (pc : Bool) : Nat := frameBytes + privBytes pc + Impl.Rsa.PPC64LE.Priv.frameBytes

theorem stackBytes_eq : stackBytes false = 3776 := rfl
theorem stackBytes_true : stackBytes true = 3792 := rfl

theorem stackBytes_ge (pc : Bool) : 3776 ≤ stackBytes pc ∧ stackBytes pc ≤ 3792 := by cases pc <;> decide

/-! ## The buffers -/

abbrev oR (s : State) : Region := ⟨s.gpr .r3, (s.gpr .r4).toNat⟩
abbrev nR (s : State) : Region := ⟨s.gpr .r5, (s.gpr .r6).toNat⟩
abbrev eR (s : State) : Region := ⟨s.gpr .r7, (s.gpr .r8).toNat⟩
abbrev pR (s : State) : Region := ⟨s.gpr .r9, (s.gpr .r10).toNat⟩
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

/-- What the code needs of `signMdTableContract.pre`, by name, for a hash
function of `D`-byte digests. -/
structure PreS (pc : Bool) (D : Nat) (s : State) : Prop where
  sp1 : stackBytes pc ≤ s.sp.toNat
  sp2 : s.sp.toNat + 224 ≤ 2 ^ 64
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
  wo : (s.gpr .r3).toNat + (s.gpr .r4).toNat ≤ 2 ^ 64
  wn : (s.gpr .r5).toNat + (s.gpr .r6).toNat ≤ 2 ^ 64
  we : (s.gpr .r7).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64
  wp : (s.gpr .r9).toNat + (s.gpr .r10).toNat ≤ 2 ^ 64
  wq : (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64
  wdp : (stackArg s 2).toNat + (stackArg s 3).toNat ≤ 2 ^ 64
  wdq : (stackArg s 4).toNat + (stackArg s 5).toNat ≤ 2 ^ 64
  wqi : (stackArg s 6).toNat + (stackArg s 7).toNat ≤ 2 ^ 64
  wdg : (stackArg s 8).toNat + D ≤ 2 ^ 64
  wsl : (stackArg s 10).toNat + (stackArg s 11).toNat ≤ 2 ^ 64
  wsc : (stackArg s 12).toNat + (stackArg s 13).toNat * 8 ≤ 2 ^ 64
  wth : (stackArg s 14).toNat + 88 ≤ 2 ^ 64
  wtg : (stackArg s 15).toNat + 88 ≤ 2 ^ 64
  k1 : 64 ≤ (s.gpr .r6).toNat
  k2 : (s.gpr .r6).toNat ≤ 1024
  ok : (s.gpr .r4).toNat = (s.gpr .r6).toNat
  e1 : 1 ≤ (s.gpr .r8).toNat
  e2 : (s.gpr .r8).toNat ≤ (s.gpr .r6).toNat
  p1 : 1 ≤ (s.gpr .r10).toNat
  p2 : (s.gpr .r10).toNat < (s.gpr .r6).toNat
  q1 : 1 ≤ (stackArg s 1).toNat
  q2 : (stackArg s 1).toNat < (s.gpr .r6).toNat
  h3 : (stackArg s 3).toNat = (s.gpr .r10).toNat
  h7 : (stackArg s 7).toNat = (s.gpr .r10).toNat
  h5 : (stackArg s 5).toNat = (stackArg s 1).toNat
  hs : Spec.RsaPss.scratchWords (s.gpr .r6).toNat ≤ (stackArg s 13).toNat

/-- With `pc`, `pre` holds the key's precomputed values. -/
abbrev HypS (pc : Bool) (s : State) : Prop :=
  pc = true → Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .r9) (s.gpr .r10).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat) =
    some (Spec.Rsa.wordsAt s.mem (stackArg s 16) (stackArg s 17).toNat)

/-- What `vg_rsa_pss_sign_precomputed`'s precondition adds: `pre`'s facts. -/
structure PreXS (s : State) : Prop where
  oP : (oR s).Disjoint (preR s)
  sP : (scR s).Disjoint (preR s)
  kP : (kS true s).Disjoint (preR s)
  wP : (stackArg s 16).toNat + (stackArg s 17).toNat * 8 ≤ 2 ^ 64
  pl : (stackArg s 17).toNat =
    Spec.Rsa.privatePrecomputedWords (s.gpr .r6).toNat (s.gpr .r10).toNat (stackArg s 1).toNat
  hyp : HypS true s

/-- The shared contract, with the hash function's table one of `hs` and
MGF1's one of `gs`, and the stack of the frames and of
`vg_rsa_private_checked`. -/
abbrev signSpec (hs gs : List FnTable) : Contract isa :=
  Spec.RsaPss.signMdTableContract (abi.withTables Spec.RsaPss.signMdTableSig [("hash", hs), ("mgf1", gs)]) (stackBytes false)

/-- Unfolds the precondition at `h`. -/
macro "sign_pre" " at " h:ident : tactic => `(tactic| (
  have e : stackBytes false = 3775 + 1 := rfl
  unfold signSpec at $h:ident
  rw [e] at $h:ident
  sig_pre [Spec.RsaPss.signMdTableContract, Spec.RsaPss.signMdTableSig,
    Spec.RsaPss.digestLenOk, Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns,
    Spec.MdHashTable.dataWords, Abi.withTables,
    Sig.wordIndex, abi, argRegs, stackArgs_sixteen, List.append_eq, List.range, List.range.loop] at $h:ident
  sig_pre [Spec.RsaPss.signMdTableContract, Spec.RsaPss.signMdTableSig,
    Spec.RsaPss.digestLenOk, Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns,
    Spec.MdHashTable.dataWords, Abi.withTables,
    Sig.wordIndex, abi, argRegs, stackArgs_sixteen, List.append_eq, List.range, List.range.loop] at $h:ident
  simp only [Option.map_some, Nat.reduceAdd, List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq,
    exists_eq_left'] at $h:ident))

theorem preS_of {H : Spec.Mgf1.Hash} {hs gs : List FnTable} {s : State} (h : (signSpec hs gs).pre s)
    (hH : Spec.MdHashTable.hashAt 64 s.mem (stackArg s 14) = some H) : PreS false H.len s := by
  sign_pre at h
  obtain ⟨sp1, sp2, -, -, -, hrd, hwr, on, oe, op, oq, odp, odq, oqi, odg, osl, os, oth, otg, oa, ns, es, ps, qs,
    dps, dqs, qis, dgs, sls, sth, stg, sa, ko, kn, ke, kp, kq, kdp, kdq, kqi, kdg, ksl, ks, kth, ktg, ka, wo, wn, we,
    wp, wq, wdp, wdq, wqi, wdg, wsl, wsc, wth, wtg, ⟨k1, k2⟩, ok, e1, e2, p1, p2, q1, q2, h3, h7, h5, hs, hl⟩ := h
  have hl := hl H hH
  rw [hl] at hrd odg dgs kdg wdg
  exact ⟨sp1, by omega, hrd, hwr, on, oe, op, oq, odp, odq, oqi, odg, osl, os, oth, otg, oa, ns, es, ps, qs, dps,
    dqs, qis, dgs, sls, sth, stg, sa, ko, kn, ke, kp, kq, kdp, kdq, kqi, kdg, ksl, ks, kth, ktg, ka, wo, wn, we, wp,
    wq, wdp, wdq, wqi, wdg, wsl, wsc, wth, wtg, k1, k2, ok, e1, e2, p1, p2, q1, q2, h3, h7, h5, hs⟩

/-- The tables, as the contract gives them: the hash function's one of `hs`
at the stack argument 14 and MGF1's one of `gs` at 15, with the functions of
distinct names at distinct addresses. -/
theorem spec_tabS {hs gs : List FnTable} {s : State} (h : (signSpec hs gs).pre s) :
    (∃ T ∈ hs, Abi.tableHeld 64 s.mem (stackArg s 14) (FnTable.words isa s T)) ∧
      (∃ T ∈ gs, Abi.tableHeld 64 s.mem (stackArg s 15) (FnTable.words isa s T)) ∧
      ((hs.map (fun T : FnTable => T.fns)).flatten ++ (gs.map (fun T : FnTable => T.fns)).flatten).Pairwise
        (fun f g => f ≠ g → s.syms f ≠ s.syms g) := by
  sign_pre at h
  exact ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩

/-! ## The working space and the registers the code keeps -/

/-- The working space. -/
abbrev Ss (s : State) : Addr := stackArg s 12

/-- `k`. -/
abbrev kk (s : State) : Nat := (s.gpr .r6).toNat

/-- `lo` of the modulus' first byte: 1 if `emLen = k - 1`. -/
def loS (s : State) : BitVec 64 :=
  let a := (s.mem (s.gpr .r5)).setWidth 64 >>> 1
  let b := a ||| a >>> 1
  let c := b ||| b >>> 2
  ((c ||| c >>> 4) - BitVec.ofNat 64 1) >>> 63

/-- The values `Base` fixes in `r15`–`r23`: `k`, `out`, `p`, `p_len`,
`salt_len`, `n`, `e`, `e_len` and `lo`. -/
def vS (s : State) : Reg → BitVec 64
  | .r15 => s.gpr .r6
  | .r16 => s.gpr .r3
  | .r17 => s.gpr .r9
  | .r18 => s.gpr .r10
  | .r19 => stackArg s 11
  | .r20 => s.gpr .r5
  | .r21 => s.gpr .r7
  | .r22 => s.gpr .r8
  | .r23 => loS s
  | _ => 0

section
variable {pc : Bool} {D : Nat} {s : State} (P : PreS pc D s)
include P

theorem scLen : oRsa ≤ (stackArg s 13).toNat * 8 := by
  have := P.hs; unfold Spec.RsaPss.scratchWords Spec.Rsa.scratchWords at this; unfold oRsa; omega

theorem sc_sub : Region.Sub (SC Ss s) (scR s) := Region.sub_prefix (scLen P)

omit P in
theorem kR_sub : Region.Sub (kR s) (kS pc s) := below_sub (by have := stackBytes_ge pc; omega)
  (by have := stackBytes_ge pc; omega)

/-- `Fits` for any state with the entry's stack pointer, regions and stack
arguments. -/
theorem fits : Fits Ss s where
  sp1 := by have := P.sp1; have := stackBytes_ge pc; omega
  sc := ⟨scR s, by rw [P.hwr]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _), rfl, scLen P⟩
  ksc := (P.ks.sub_left kR_sub).sub_right (sc_sub P)
  wS := by show (stackArg s 12).toNat + oRsa ≤ 2 ^ 64; have := P.wsc; have := scLen P; omega

end

section
variable {s t : State} (h : Base Ss vS s t)
include h

theorem Base.r15 : t.gpr .r15 = s.gpr .r6 := h.vs .r15 (by decide)
theorem Base.r16 : t.gpr .r16 = s.gpr .r3 := h.vs .r16 (by decide)
theorem Base.r17 : t.gpr .r17 = s.gpr .r9 := h.vs .r17 (by decide)
theorem Base.r18 : t.gpr .r18 = s.gpr .r10 := h.vs .r18 (by decide)
theorem Base.r19 : t.gpr .r19 = stackArg s 11 := h.vs .r19 (by decide)
theorem Base.r20 : t.gpr .r20 = s.gpr .r5 := h.vs .r20 (by decide)
theorem Base.r21 : t.gpr .r21 = s.gpr .r7 := h.vs .r21 (by decide)
theorem Base.r22 : t.gpr .r22 = s.gpr .r8 := h.vs .r22 (by decide)
theorem Base.r23 : t.gpr .r23 = loS s := h.vs .r23 (by decide)

end

end VG.Proof.RsaPss.PPC64LE.Sg
