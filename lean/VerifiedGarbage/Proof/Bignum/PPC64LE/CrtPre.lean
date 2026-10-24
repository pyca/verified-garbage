module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Proof.Bignum.CrtFrame
public import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtFront
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubCorrect
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# The RSA private-key operation on PPC64LE: what the precondition gives

`pre_facts`: from `fnContract.pre`, the lengths, the layout of the three
working spaces in the scratch, and that each buffer is readable and apart
from the scratch (`PF`).
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Crt

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.Crt
open VG.Proof.Bignum.PPC64LE

/-- What the precondition gives. -/
structure PF (s₀ : State) : Prop where
  k64 : 64 ≤ ck s₀
  k1024 : ck s₀ ≤ 1024
  p1 : 1 ≤ cpL s₀
  pk : cpL s₀ < ck s₀
  q1 : 1 ≤ cqL s₀
  qk : cqL s₀ < ck s₀
  room : slot (cwX s₀) 8 + slot (wsWords (cpL s₀)) 8 + slot (wsWords (cqL s₀)) 8 ≤ cZ s₀
  pq : wsWords (cpL s₀) + wsWords (cqL s₀) ≤ cwX s₀
  nw : (cS s₀).toNat + cZ s₀ ≤ 2 ^ 64
  out : Scr s₀ (s₀.gpr .r3) (ck s₀)
  sepO : ∀ x, ofs (s₀.gpr .r3) x < ck s₀ → cZ s₀ ≤ ofs (cS s₀) x
  rN : ∀ i < ck s₀, InRegions (s₀.rd ++ s₀.wr) (off (s₀.gpr .r5) i) 1
  sN : ∀ i < ck s₀, ∀ x, ofs (cS s₀) x < cZ s₀ → off (s₀.gpr .r5) i ≠ x
  rI : ∀ i < ck s₀, InRegions (s₀.rd ++ s₀.wr) (off (s₀.gpr .r7) i) 1
  sI : ∀ i < ck s₀, ∀ x, ofs (cS s₀) x < cZ s₀ → off (s₀.gpr .r7) i ≠ x
  rP : ∀ i < cpL s₀, InRegions (s₀.rd ++ s₀.wr) (off (s₀.gpr .r9) i) 1
  sP : ∀ i < cpL s₀, ∀ x, ofs (cS s₀) x < cZ s₀ → off (s₀.gpr .r9) i ≠ x
  rQ : ∀ i < cqL s₀, InRegions (s₀.rd ++ s₀.wr) (off (stackArg s₀ 0) i) 1
  sQ : ∀ i < cqL s₀, ∀ x, ofs (cS s₀) x < cZ s₀ → off (stackArg s₀ 0) i ≠ x
  rDP : ∀ i < cpL s₀, InRegions (s₀.rd ++ s₀.wr) (off (stackArg s₀ 2) i) 1
  sDP : ∀ i < cpL s₀, ∀ x, ofs (cS s₀) x < cZ s₀ → off (stackArg s₀ 2) i ≠ x
  rDQ : ∀ i < cqL s₀, InRegions (s₀.rd ++ s₀.wr) (off (stackArg s₀ 4) i) 1
  sDQ : ∀ i < cqL s₀, ∀ x, ofs (cS s₀) x < cZ s₀ → off (stackArg s₀ 4) i ≠ x
  rQI : ∀ i < cpL s₀, InRegions (s₀.rd ++ s₀.wr) (off (stackArg s₀ 6) i) 1
  sQI : ∀ i < cpL s₀, ∀ x, ofs (cS s₀) x < cZ s₀ → off (stackArg s₀ 6) i ≠ x

theorem rd_of_mem {s : State} {A : Addr} {L n : Nat} (h : (⟨A, L⟩ : Region) ∈ s.rd) (hn : n ≤ L)
    (hL : L < 2 ^ 64) :
    ∀ i < n, InRegions (s.rd ++ s.wr) (off A i) 1 := fun i hi =>
  ⟨_, List.mem_append_left _ h, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩

theorem pre_facts {s₀ : State} (h : fnContract.pre s₀) : PF s₀ := by
  obtain ⟨hsp, hrd, hwr, dON, dOI, dOP, dOQ, dODP, dODQ, dOQI, dOS, dOA, dNS, dIS, dPS, dQS, dDPS, dDQS, dQIS,
    dSA, nwO, nwN, nwI, nwP, nwQ, nwDP, nwDQ, nwQI, nwS, ⟨hk, hk'⟩, hOL, hIL, hp1, hpk, hq1, hqk, hdpl, hqil, hdql,
    hsl⟩ := h
  simp only [Spec.Rsa.scratchWords] at hsl
  refine ⟨hk, hk', hp1, hpk, hq1, hqk, ?_, ?_, nwS, Scr.of_mem (by rw [hwr, hOL]; simp)
    (by show (s₀.gpr .r3).toNat + (s₀.gpr .r6).toNat ≤ 2 ^ 64; rw [← hOL]; exact nwO),
    fun x hx => Pub.sep_of_disjoint dOS x (by rw [hOL]; exact hx),
    rd_of_mem (by rw [hrd]; simp) (Nat.le_refl _) (BitVec.isLt _),
    Pub.ne_of_disjoint dNS (Nat.le_of_lt (BitVec.isLt _)),
    rd_of_mem (L := (s₀.gpr .r8).toNat) (by rw [hrd]; simp) (Nat.le_of_eq hIL.symm) (BitVec.isLt _),
    fun i hi => Pub.ne_of_disjoint dIS (Nat.le_of_lt (BitVec.isLt _)) i (by
      change i < (s₀.gpr .r6).toNat at hi; omega_arith),
    rd_of_mem (by rw [hrd]; simp) (Nat.le_refl _) (BitVec.isLt _),
    Pub.ne_of_disjoint dPS (Nat.le_of_lt (BitVec.isLt _)),
    rd_of_mem (by rw [hrd]; simp) (Nat.le_refl _) (BitVec.isLt _),
    Pub.ne_of_disjoint dQS (Nat.le_of_lt (BitVec.isLt _)),
    rd_of_mem (L := (stackArg s₀ 3).toNat) (by rw [hrd]; simp) (Nat.le_of_eq hdpl.symm) (BitVec.isLt _),
    fun i hi => Pub.ne_of_disjoint dDPS (Nat.le_of_lt (BitVec.isLt _)) i (by
      change i < (s₀.gpr .r10).toNat at hi; omega_arith),
    rd_of_mem (L := (stackArg s₀ 5).toNat) (by rw [hrd]; simp) (Nat.le_of_eq hdql.symm) (BitVec.isLt _),
    fun i hi => Pub.ne_of_disjoint dDQS (Nat.le_of_lt (BitVec.isLt _)) i (by
      change i < (stackArg s₀ 1).toNat at hi; omega_arith),
    rd_of_mem (L := (stackArg s₀ 7).toNat) (by rw [hrd]; simp) (Nat.le_of_eq hqil.symm) (BitVec.isLt _),
    fun i hi => Pub.ne_of_disjoint dQIS (Nat.le_of_lt (BitVec.isLt _)) i (by
      change i < (s₀.gpr .r10).toNat at hi; omega_arith)⟩
  · show slot (2 * (((s₀.gpr .r6).toNat + 7) / 8)) 8 + slot (wsWords (s₀.gpr .r10).toNat) 8 +
      slot (wsWords (stackArg s₀ 1).toNat) 8 ≤ (stackArg s₀ 9).toNat * 8
    unfold slot wsWords hdrBytes; omega_arith
  · show wsWords (s₀.gpr .r10).toNat + wsWords (stackArg s₀ 1).toNat ≤ 2 * (((s₀.gpr .r6).toNat + 7) / 8)
    unfold wsWords; omega_arith

end VG.Proof.Bignum.PPC64LE.Crt
