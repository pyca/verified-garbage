module

public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Contract
public import VerifiedGarbage.Proof.Rsa.X86_64.CvStore
import VerifiedGarbage.Proof.Bignum.X86_64.PubCode
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

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
  refine ⟨hb1, hb2, hlen, hgen, by omega, Scr.of_mem (by rw [hwr]; simp) ws,
    ⟨?_, ?_⟩, ⟨?_, ?_⟩, Scr.of_mem (by rw [hwr]; simp) wu, src_of_region (by rw [hrd]; simp) (by omega) drs,
    ?_, apart_of dor (by omega) (by omega), apart_of dou (by omega) (by omega), hstack, dbs, dbr⟩
  · intro i hi
    rw [hwr]
    exact ⟨⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩, by simp, contains_byte _ (by omega) (by omega)⟩
  · intro i hi
    exact out_scr dos (contains_byte _ (by omega) (by omega))
  · intro i hi
    rw [hwr]
    exact ⟨⟨s.gpr .rdx, 8⟩, by simp, contains_byte _ (by omega) (by omega)⟩
  · intro i hi
    exact out_scr dus (contains_byte _ (by omega) (by omega))
  · intro i hi
    refine ⟨⟨stackArgAddr s 0, 24⟩, by rw [hrd]; simp, ?_⟩
    rw [show stackArgAddr s i = stackArgAddr s 0 + BitVec.ofNat 64 (8 * i) by
      simp only [stackArgAddr, Nat.zero_add, Nat.mul_one, Offset.add_add]; congr 2; omega]
    exact Offset.contains_base _ (by omega) (by omega)

/-- The outer header and all 28 arrays of the shared windowed round fit
even at the 511/512-bit boundary and with a non-byte-aligned p. -/
theorem candidate_room {bits len Z : Nat} (hb1 : 512 ≤ bits) (hb2 : bits ≤ 8192)
    (hlen : len = (bits + 7) / 8) (hz : 128 * len + 256 ≤ Z) (q : Bool) :
    let nbits := if q then bits - 1 else bits
    let nbytes := (nbits + 7) / 8
    let w := (nbytes + 7) / 8
    4 ≤ w ∧ w ≤ 128 ∧ 256 + slot w 28 ≤ Z := by
  have hlo : 511 ≤ (if q then bits - 1 else bits) := by cases q <;> simp <;> omega
  have hhi : (if q then bits - 1 else bits) ≤ bits := by cases q <;> simp
  dsimp only
  simp only [slot, VG.Impl.Bignum.hdrBytes]
  omega

end VG.Proof.Ffdh.X86_64.ParameterCandidate
