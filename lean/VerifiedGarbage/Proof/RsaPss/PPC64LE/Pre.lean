module

public import VerifiedGarbage.Spec.RsaPss.Table
public import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Base
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.RsaOaep.PPC64LE

/-!
# RSASSA-PSS verification on PPC64LE: the precondition

Untrusted: everything here is checked by Lean. `PreP D s`: the shared
contract's precondition (`Spec.RsaPss.verifyPrecomputedTableContract`, with the
stack of the frame and of the streaming hash functions, 304 bytes), by name
(`preP_of`); the working space and the values `Base` fixes (`Sp`, `vP`: the
encoding's parameters `lo`, `c` and `dbLen` from the modulus' first byte),
and what `Base` needs of the entry (`PreP.fits`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.PPC64LE

open VG VG.PPC64LE
open VG.Impl.RsaOaep.PPC64LE (frameBytes saved oLr arg oEm oSt oDig oW oRsa copyLoop zeroLoop mgfXor save restore)
open VG.Proof.RsaOaep.PPC64LE (Base Fits SC off fx kR)

theorem stackArgs_eight (s : State) :
    List.map (stackArg s) (List.range 8) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7] := rfl

/-- The buffers: `n`, `e`, the digest, the signature, the working space, the
precomputed values, the tables of the hash function and of MGF1's, and the
arguments on the stack. -/
abbrev nR (s : State) : Region := ⟨s.gpr .r3, (s.gpr .r4).toNat⟩
abbrev eR (s : State) : Region := ⟨s.gpr .r5, (s.gpr .r6).toNat⟩
abbrev dR (D : Nat) (s : State) : Region := ⟨s.gpr .r7, D⟩
abbrev gR (s : State) : Region := ⟨s.gpr .r9, (s.gpr .r10).toNat⟩
abbrev scR (s : State) : Region := ⟨stackArg s 2, (stackArg s 3).toNat * 8⟩
abbrev pR (s : State) : Region := ⟨stackArg s 4, (stackArg s 5).toNat * 8⟩
abbrev tHR (s : State) : Region := Sig.tableRegion 64 (stackArg s 6) 11
abbrev tGR (s : State) : Region := Sig.tableRegion 64 (stackArg s 7) 5
abbrev aR (s : State) : Region := ⟨stackArgAddr s 0, 64⟩

/-- What the code needs of `verifyPrecomputedTableContract.pre`, by name,
for a hash function of `D`-byte digests. -/
structure PreP (D : Nat) (s : State) : Prop where
  sp1 : 304 ≤ s.sp.toNat
  sp2 : s.sp.toNat + 160 ≤ 2 ^ 64
  hrd : s.rd = [nR s, eR s, dR D s, gR s, pR s, tHR s, tGR s, aR s]
  hwr : s.wr = [scR s]
  ns : (nR s).Disjoint (scR s)
  es : (eR s).Disjoint (scR s)
  ds : (dR D s).Disjoint (scR s)
  gs : (gR s).Disjoint (scR s)
  sp : (scR s).Disjoint (pR s)
  sth : (scR s).Disjoint (tHR s)
  stg : (scR s).Disjoint (tGR s)
  sa : (scR s).Disjoint (aR s)
  kn : (kR s).Disjoint (nR s)
  ke : (kR s).Disjoint (eR s)
  kd : (kR s).Disjoint (dR D s)
  kg : (kR s).Disjoint (gR s)
  ksc : (kR s).Disjoint (scR s)
  kp : (kR s).Disjoint (pR s)
  kth : (kR s).Disjoint (tHR s)
  ktg : (kR s).Disjoint (tGR s)
  ka : (kR s).Disjoint (aR s)
  wn : (s.gpr .r3).toNat + (s.gpr .r4).toNat ≤ 2 ^ 64
  we : (s.gpr .r5).toNat + (s.gpr .r6).toNat ≤ 2 ^ 64
  wd : (s.gpr .r7).toNat + D ≤ 2 ^ 64
  wg : (s.gpr .r9).toNat + (s.gpr .r10).toNat ≤ 2 ^ 64
  wsc : (stackArg s 2).toNat + (stackArg s 3).toNat * 8 ≤ 2 ^ 64
  wp : (stackArg s 4).toNat + (stackArg s 5).toNat * 8 ≤ 2 ^ 64
  wth : (stackArg s 6).toNat + 88 ≤ 2 ^ 64
  wtg : (stackArg s 7).toNat + 40 ≤ 2 ^ 64
  k1 : 64 ≤ (s.gpr .r4).toNat
  k2 : (s.gpr .r4).toNat ≤ 1024
  e1 : 1 ≤ (s.gpr .r6).toNat
  e2 : (s.gpr .r6).toNat ≤ (s.gpr .r4).toNat
  gk : (s.gpr .r10).toNat = (s.gpr .r4).toNat
  hs : Spec.RsaPss.publicScratchWords (s.gpr .r4).toNat ≤ (stackArg s 3).toNat
  hp : (stackArg s 5).toNat = Spec.Rsa.precomputedWords (s.gpr .r4).toNat

/-- The shared contract, with the hash function's table one of `hs` and
MGF1's one of `gs`, and the stack of the frame and of the streaming hash
functions. -/
abbrev verSpec (hs gs : List FnTable) : Contract isa :=
  Spec.RsaPss.verifyPrecomputedTableContract
    (abi.withTables Spec.RsaPss.verifyPrecomputedTableSig [("hash", hs), ("mgf1", gs)]) 304

/-- Unfolds the precondition at `h`. -/
macro "ver_pre" " at " h:ident : tactic => `(tactic| (
  have e : (304 : Nat) = 303 + 1 := rfl
  unfold verSpec at $h:ident
  rw [e] at $h:ident
  sig_pre [Spec.RsaPss.verifyPrecomputedTableContract, Spec.RsaPss.verifyPrecomputedTableSig,
    Spec.RsaPss.digestLenOk, Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns,
    Spec.MdHashTable.dataWords, Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables,
    Sig.wordIndex, abi, argRegs, stackArgs_eight, List.append_eq, List.range, List.range.loop] at $h:ident
  sig_pre [Spec.RsaPss.verifyPrecomputedTableContract, Spec.RsaPss.verifyPrecomputedTableSig,
    Spec.RsaPss.digestLenOk, Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns,
    Spec.MdHashTable.dataWords, Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables,
    Sig.wordIndex, abi, argRegs, stackArgs_eight, List.append_eq, List.range, List.range.loop] at $h:ident
  simp only [Option.map_some, Nat.reduceAdd, List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq,
    exists_eq_left'] at $h:ident))

theorem preP_of {H : Spec.Mgf1.Hash} {hs gs : List FnTable} {s : State} (h : (verSpec hs gs).pre s)
    (hH : Spec.MdHashTable.hashAt 64 s.mem (stackArg s 6) = some H) : PreP H.len s := by
  ver_pre at h
  obtain ⟨sp1, sp2, -, -, -, hrd, hwr, ns, es, ds, gs, sp, sth, stg, sa, kn, ke, kd, kg, ksc, kp, kth, ktg, ka,
    wn, we, wd, wg, wsc, wp, wth, wtg, ⟨k1, k2⟩, e1, e2, gk, hs, hp, hl⟩ := h
  have hl := hl H hH
  rw [hl] at hrd ds kd wd
  exact ⟨sp1, by omega, hrd, hwr, ns, es, ds, gs, sp, sth, stg, sa, kn, ke, kd, kg, ksc, kp, kth, ktg, ka, wn, we,
    wd, wg, wsc, wp, wth, wtg, k1, k2, e1, e2, gk, hs, hp⟩

/-- The tables, as the contract gives them: the hash function's one of `hs`
at the stack argument 6 and MGF1's one of `gs` at 7, with the functions of
distinct names at distinct addresses. -/
theorem spec_tab {hs gs : List FnTable} {s : State} (h : (verSpec hs gs).pre s) :
    (∃ T ∈ hs, Abi.tableHeld 64 s.mem (stackArg s 6) (FnTable.words isa s T)) ∧
      (∃ T ∈ gs, Abi.tableHeld 64 s.mem (stackArg s 7) (FnTable.words isa s T)) ∧
      ((hs.map (fun T : FnTable => T.fns)).flatten ++ (gs.map (fun T : FnTable => T.fns)).flatten).Pairwise
        (fun f g => f ≠ g → s.syms f ≠ s.syms g) := by
  ver_pre at h
  exact ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩

/-- The working space. -/
abbrev Sp (s : State) : Addr := stackArg s 2

/-- The modulus' first byte, zero-extended. -/
def n0 (s : State) : BitVec 64 := (s.mem (s.gpr .r3)).setWidth 64

/-- The bits of `n₀ >> 1` smeared down. -/
def smear (s : State) : BitVec 64 :=
  let a := n0 s >>> 1
  let b := a ||| a >>> 1
  let c := b ||| b >>> 2
  c ||| c >>> 4

/-- 1 if `emLen = k - 1`, else 0. -/
def lo (s : State) : BitVec 64 := (smear s - BitVec.ofNat 64 1) >>> 63

/-- The mask of `maskedDB`'s first byte. -/
def cm (s : State) : BitVec 64 := smear s ||| ((BitVec.ofNat 64 0 - lo s) &&& BitVec.ofNat 64 0xFF)

/-- `dbLen = k - lo - hLen - 1`. -/
def dbLen (D : Nat) (s : State) : BitVec 64 := s.gpr .r4 - lo s - BitVec.ofNat 64 (D + 1)

/-- The salt-length mode, zero-extended. -/
def anyL (s : State) : BitVec 64 := ((stackArg s 1).setWidth 32 >>> 0).setWidth 64

/-- The values `Base` fixes in `r15`–`r23`: `k`, `digest`, `lo`, `c`,
`salt_len`, `any_salt_len`, `dbLen`, `pre` and its length. -/
def vP (D : Nat) (s : State) : Reg → BitVec 64
  | .r15 => s.gpr .r4
  | .r16 => s.gpr .r7
  | .r17 => lo s
  | .r18 => cm s
  | .r19 => stackArg s 0
  | .r20 => anyL s
  | .r21 => dbLen D s
  | .r22 => stackArg s 4
  | .r23 => stackArg s 5
  | _ => 0

section
variable {D : Nat} {s : State} (P : PreP D s)
include P

theorem scLen : oRsa ≤ (stackArg s 3).toNat * 8 := by
  have := P.hs; unfold Spec.RsaPss.publicScratchWords at this; unfold oRsa; omega

theorem sc_sub : Region.Sub (SC Sp s) (scR s) := Region.sub_prefix (scLen P)

theorem PreP.fits : Fits Sp s where
  sp1 := P.sp1
  sc := ⟨scR s, by rw [P.hwr]; simp, rfl, scLen P⟩
  ksc := P.ksc.sub_right (sc_sub P)
  wS := by show (stackArg s 2).toNat + oRsa ≤ 2 ^ 64; have := P.wsc; have := scLen P; omega

end

section
variable {D : Nat} {s t : State} (h : Base Sp (vP D) s t)
include h

theorem _root_.VG.Proof.RsaOaep.PPC64LE.Base.pk : t.gpr .r15 = s.gpr .r4 := h.vs .r15 (by decide)
theorem _root_.VG.Proof.RsaOaep.PPC64LE.Base.pdig : t.gpr .r16 = s.gpr .r7 := h.vs .r16 (by decide)
theorem _root_.VG.Proof.RsaOaep.PPC64LE.Base.plo : t.gpr .r17 = lo s := h.vs .r17 (by decide)
theorem _root_.VG.Proof.RsaOaep.PPC64LE.Base.pc : t.gpr .r18 = cm s := h.vs .r18 (by decide)
theorem _root_.VG.Proof.RsaOaep.PPC64LE.Base.psl : t.gpr .r19 = stackArg s 0 := h.vs .r19 (by decide)
theorem _root_.VG.Proof.RsaOaep.PPC64LE.Base.pany : t.gpr .r20 = anyL s := h.vs .r20 (by decide)
theorem _root_.VG.Proof.RsaOaep.PPC64LE.Base.pdb : t.gpr .r21 = dbLen D s := h.vs .r21 (by decide)
theorem _root_.VG.Proof.RsaOaep.PPC64LE.Base.ppre : t.gpr .r22 = stackArg s 4 := h.vs .r22 (by decide)
theorem _root_.VG.Proof.RsaOaep.PPC64LE.Base.pprel : t.gpr .r23 = stackArg s 5 := h.vs .r23 (by decide)

end

end VG.Proof.RsaPss.PPC64LE
