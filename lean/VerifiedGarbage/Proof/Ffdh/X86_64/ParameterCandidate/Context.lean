module

public import VerifiedGarbage.Proof.Rsa.X86_64.CvStore
import VerifiedGarbage.Proof.Bignum.X86_64.PubCode
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Proof.Framework.X86_64.Taint
public import VerifiedGarbage.Proof.Ffdh.Contract

/-! ### `Ffdh.X86_64.ParameterCandidate.Contract`, which this module and modules that import it used -/

section

/-! # FFDH parameter generation on x86-64: the callable contract -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Spec.Ffdh
open VG.Spec.Rsa (bytesAt wordsAt i2osp)

def pcPre (s : State) : Prop :=
  let out : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
  let used : Region := ⟨s.gpr .rdx, 8⟩
  let rand : Region := ⟨s.gpr .r9, (stackArg s 0).toNat⟩
  let scr : Region := ⟨stackArg s 1, (stackArg s 2).toNat * 8⟩
  let args : Region := ⟨stackArgAddr s 0, 24⟩
  let ret : Region := ⟨s.gpr .rsp, 8⟩
  let below : Region := ⟨s.gpr .rsp - 128#64, 128⟩
  (s.gpr .rsp).toNat + 32 ≤ 2 ^ 64 ∧ 128 ≤ (s.gpr .rsp).toNat ∧
    s.rd = [rand, args] ∧ s.wr = [out, used, scr] ∧
    out.Disjoint used ∧ out.Disjoint rand ∧ out.Disjoint scr ∧ out.Disjoint args ∧
    used.Disjoint rand ∧ used.Disjoint scr ∧ used.Disjoint args ∧
    rand.Disjoint scr ∧ scr.Disjoint args ∧
    ret.Disjoint out ∧ ret.Disjoint used ∧ ret.Disjoint rand ∧ ret.Disjoint scr ∧ ret.Disjoint args ∧
    below.Disjoint out ∧ below.Disjoint used ∧ below.Disjoint rand ∧ below.Disjoint scr ∧ below.Disjoint args ∧
    (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + 8 ≤ 2 ^ 64 ∧
    (s.gpr .r9).toNat + (stackArg s 0).toNat ≤ 2 ^ 64 ∧
    (stackArg s 1).toNat + (stackArg s 2).toNat * 8 ≤ 2 ^ 64 ∧
    512 ≤ (s.gpr .rcx).toNat ∧ (s.gpr .rcx).toNat ≤ 8192 ∧
    (s.gpr .rsi).toNat = ((s.gpr .rcx).toNat + 7) / 8 ∧
    (((s.gpr .r8).setWidth 32).toNat = 2 ∨ ((s.gpr .r8).setWidth 32).toNat = 5) ∧
    Spec.Rsa.scratchWords (s.gpr .rsi).toNat ≤ (stackArg s 2).toNat

abbrev pcRand (s : State) : List Byte := bytesAt s.mem (s.gpr .r9) (stackArg s 0).toNat

def pcResult (s : State) : Option (Option Nat × Spec.RsaKeyGen.Rand) :=
  sievedParameterCandidate (s.gpr .rcx).toNat ((s.gpr .r8).setWidth 32).toNat (pcRand s)

def pcPost (s t : State) : Prop :=
  ((t.gpr .rax).setWidth 32).toNat = candidateStatus (pcResult s) ∧
    bytesAt t.mem (s.gpr .rdi) (s.gpr .rsi).toNat =
      (match pcResult s with
        | some (some p, _) => i2osp p (s.gpr .rsi).toNat
        | _ => List.replicate (s.gpr .rsi).toNat 0) ∧
    wordsAt t.mem (s.gpr .rdx) 1 =
      [BitVec.ofNat 64 (match pcResult s with
        | some (_, rest) => (stackArg s 0).toNat - rest.length
        | none => 0)]

def pcPub (s t : State) : Prop :=
  s.gpr .rsp = t.gpr .rsp ∧ (pcRand s).map (·.toNat) = (pcRand t).map (·.toNat) ∧
    s.gpr .rdi = t.gpr .rdi ∧ s.gpr .rsi = t.gpr .rsi ∧ s.gpr .rdx = t.gpr .rdx ∧
    s.gpr .rcx = t.gpr .rcx ∧ (s.gpr .r8).setWidth 32 = (t.gpr .r8).setWidth 32 ∧ s.gpr .r9 = t.gpr .r9 ∧
    stackArg s 0 = stackArg t 0 ∧ stackArg s 1 = stackArg t 1 ∧ stackArg s 2 = stackArg t 2

def pcContract : Contract isa where
  pre := pcPre
  post := pcPost
  pub := pcPub

end VG.Proof.Ffdh.X86_64.ParameterCandidate

end

end

/-! # FFDH parameter generation on x86-64: buffers and workspace bounds -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

structure PcCtx (s : State) : Prop where
  bits1 : 512 ≤ (s.gpr .rcx).toNat
  bits2 : (s.gpr .rcx).toNat ≤ 8192
  len : (s.gpr .rsi).toNat = ((s.gpr .rcx).toNat + 7) / 8
  gen : ((s.gpr .r8).setWidth 32).toNat = 2 ∨ ((s.gpr .r8).setWidth 32).toNat = 5
  room : 128 * (s.gpr .rsi).toNat + 256 ≤ (stackArg s 2).toNat * 8
  scr : Scr s (stackArg s 1) ((stackArg s 2).toNat * 8)
  out : OutOk s (stackArg s 1) ((stackArg s 2).toNat * 8) (s.gpr .rdi) (s.gpr .rsi).toNat
  used : OutOk s (stackArg s 1) ((stackArg s 2).toNat * 8) (s.gpr .rdx) 8
  usedMem : Scr s (s.gpr .rdx) 8
  rand : Src s (stackArg s 1) ((stackArg s 2).toNat * 8) (s.gpr .r9) (pcRand s)
  args : ∀ i < 3, InRegions (s.rd ++ s.wr) (stackArgAddr s i) 8
  outRand : Apart (s.gpr .rdi) (s.gpr .rsi).toNat (s.gpr .r9) (stackArg s 0).toNat
  outUsed : Apart (s.gpr .rdi) (s.gpr .rsi).toNat (s.gpr .rdx) 8
  stackSize : 128 ≤ (s.gpr .rsp).toNat
  stackScr : (⟨s.gpr .rsp - 128#64, 128⟩ : Region).Disjoint
    ⟨stackArg s 1, (stackArg s 2).toNat * 8⟩
  stackRand : (⟨s.gpr .rsp - 128#64, 128⟩ : Region).Disjoint
    ⟨s.gpr .r9, (stackArg s 0).toNat⟩

theorem pcCtx_of {s : State} (h : pcPre s) : PcCtx s := by
  obtain ⟨_, hstack, hrd, hwr, dou, dor, dos, _, _, dus, _, drs, _, _, _, _, _, _, _, _, dbr, dbs, _,
    wo, wu, wr, ws, hb1, hb2, hlen, hgen, hroom⟩ := h
  unfold Spec.Rsa.scratchWords at hroom
  refine ⟨hb1, hb2, hlen, hgen, by omega_using [hroom], Scr.of_mem (by rw [hwr]; simp) ws,
    ⟨?_, ?_⟩, ⟨?_, ?_⟩, Scr.of_mem (by rw [hwr]; simp) wu, src_of_region (by rw [hrd]; simp) (by omega_using []) drs,
    ?_, apart_of dor (by omega_using []) (by omega_using []), apart_of dou (by omega_using []) (by omega_using []), hstack, dbs, dbr⟩
  · intro i hi
    rw [hwr]
    exact ⟨⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩, by simp, contains_byte _ (by omega_using [hi]) (by omega_using [])⟩
  · intro i hi
    exact out_scr dos (contains_byte _ (by omega_using [hi]) (by omega_using []))
  · intro i hi
    rw [hwr]
    exact ⟨⟨s.gpr .rdx, 8⟩, by simp, contains_byte _ (by omega_using [hi]) (by omega_using [])⟩
  · intro i hi
    exact out_scr dus (contains_byte _ (by omega_using [hi]) (by omega_using []))
  · intro i hi
    refine ⟨⟨stackArgAddr s 0, 24⟩, by rw [hrd]; simp, ?_⟩
    rw [show stackArgAddr s i = stackArgAddr s 0 + BitVec.ofNat 64 (8 * i) by
      simp only [stackArgAddr, Nat.zero_add, Nat.mul_one, Offset.add_add]; congr 2; omega_using []]
    exact Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])

/-- The outer header and all 28 arrays of the shared windowed round fit
even at the 511/512-bit boundary and with a non-byte-aligned p. -/
theorem candidate_room {bits len Z : Nat} (hb1 : 512 ≤ bits) (hb2 : bits ≤ 8192)
    (hlen : len = (bits + 7) / 8) (hz : 128 * len + 256 ≤ Z) (q : Bool) :
    let nbits := if q then bits - 1 else bits
    let nbytes := (nbits + 7) / 8
    let w := (nbytes + 7) / 8
    4 ≤ w ∧ w ≤ 128 ∧ 256 + slot w 28 ≤ Z := by
  have hlo : 511 ≤ (if q then bits - 1 else bits) := by cases q <;> simp <;> omega_using [hb1]
  have hhi : (if q then bits - 1 else bits) ≤ bits := by cases q <;> simp
  dsimp only
  simp only [slot, VG.Impl.Bignum.hdrBytes]
  omega_using [hb2, hlen, hz, hlo, hhi]

end VG.Proof.Ffdh.X86_64.ParameterCandidate
