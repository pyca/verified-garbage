module

public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.Rsa.Arm.RvBase
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Rsa.Arm.RvFin5
import VerifiedGarbage.Proof.Framework.Sig

/-! # `vg_rsa_recover_primes` on ARMv7: the contract's arguments

`mkP s`: the public parameters of a call from `s`; `CIn s`: the contract's
precondition, as the proof uses it (`cin_of_pre`).
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm

/-- The public parameters of a call: the frame, the pointers, the lengths,
`n`, `e` and the number of candidates tried. -/
def mkP (s : State) : RP where
  sp := s.sp - BitVec.ofNat 32 56
  pP := s.gpr .r0
  qP := s.gpr .r2
  nP := stackArg s 0
  eP := stackArg s 2
  dP := stackArg s 4
  B := stackArg s 6
  K := (stackArg s 1).toNat
  el := (stackArg s 3).toNat
  dl := (stackArg s 5).toNat
  SL := (stackArg s 7).toNat
  nB := Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 0)) (stackArg s 1).toNat
  eB := Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 2)) (stackArg s 3).toNat
  nt := (Spec.Rsa.primesKey (Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 0)) (stackArg s 1).toNat)
    (Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 2)) (stackArg s 3).toNat)
    (Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 4)) (stackArg s 5).toNat)).2

/-- The regions the body runs with: the frame, `p`, `q`, the working space
and Montgomery multiplication's. -/
def xRegs (s : State) : List Region := [(mkP s).rFr, (mkP s).rP, (mkP s).rQ, (mkP s).rS, (mkP s).rM]

/-- The arguments' regions. -/
abbrev cP (s : State) : Region := ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩
abbrev cQ (s : State) : Region := ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩
abbrev cN (s : State) : Region := ⟨State.addr (stackArg s 0), (stackArg s 1).toNat⟩
abbrev cE (s : State) : Region := ⟨State.addr (stackArg s 2), (stackArg s 3).toNat⟩
abbrev cD (s : State) : Region := ⟨State.addr (stackArg s 4), (stackArg s 5).toNat⟩
abbrev cS (s : State) : Region := ⟨State.addr (stackArg s 6), (stackArg s 7).toNat * 8⟩
abbrev cA (s : State) : Region := ⟨stackArgAddr s 0, 32⟩
abbrev cF (s : State) : Region := ⟨State.addr s.sp - 56#64, 56⟩

/-- The contract's precondition. -/
structure CIn (s : State) : Prop where
  spLo : 56 ≤ s.sp.toNat
  spHi : s.sp.toNat + 32 ≤ 2 ^ 32
  rd : s.rd = [cN s, cE s, cD s, cA s]
  wr : s.wr = [cP s, cQ s, cS s]
  pq : (cP s).Disjoint (cQ s)
  pn : (cP s).Disjoint (cN s)
  pe : (cP s).Disjoint (cE s)
  pd : (cP s).Disjoint (cD s)
  pS : (cP s).Disjoint (cS s)
  pA : (cP s).Disjoint (cA s)
  qn : (cQ s).Disjoint (cN s)
  qe : (cQ s).Disjoint (cE s)
  qd : (cQ s).Disjoint (cD s)
  qS : (cQ s).Disjoint (cS s)
  qA : (cQ s).Disjoint (cA s)
  nS : (cN s).Disjoint (cS s)
  eS : (cE s).Disjoint (cS s)
  dS : (cD s).Disjoint (cS s)
  SA : (cS s).Disjoint (cA s)
  Fp : (cF s).Disjoint (cP s)
  Fq : (cF s).Disjoint (cQ s)
  Fn : (cF s).Disjoint (cN s)
  Fe : (cF s).Disjoint (cE s)
  Fd : (cF s).Disjoint (cD s)
  FS : (cF s).Disjoint (cS s)
  FA : (cF s).Disjoint (cA s)
  fp : (s.gpr .r0).toNat + (s.gpr .r1).toNat ≤ 2 ^ 32
  fq : (s.gpr .r2).toNat + (s.gpr .r3).toNat ≤ 2 ^ 32
  fn : (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 32
  fe : (stackArg s 2).toNat + (stackArg s 3).toNat ≤ 2 ^ 32
  fd : (stackArg s 4).toNat + (stackArg s 5).toNat ≤ 2 ^ 32
  fS : (stackArg s 6).toNat + (stackArg s 7).toNat * 8 ≤ 2 ^ 32
  valid : Spec.Rsa.lenValid (stackArg s 1).toNat
  pl : (s.gpr .r1).toNat = (stackArg s 1).toNat
  ql : (s.gpr .r3).toNat = (stackArg s 1).toNat
  el1 : 1 ≤ (stackArg s 3).toNat
  el2 : (stackArg s 3).toNat ≤ (stackArg s 1).toNat
  dl1 : 1 ≤ (stackArg s 5).toNat
  dl2 : (stackArg s 5).toNat ≤ (stackArg s 1).toNat
  scr : Spec.Rsa.scratchWords (stackArg s 1).toNat ≤ (stackArg s 7).toNat

theorem cin_of_pre (s : State) (h : (Spec.Rsa.recoverPrimesContract abi 56).pre s) : CIn s := by
  sig_pre [Spec.Rsa.recoverPrimesContract, Spec.Rsa.recoverPrimesSig, abi, argRegs, reduceClassify, Loc.val] at h
  obtain ⟨spLo, spHi, rd, wr, pq, pn, pe, pd, pS, pA, qn, qe, qd, qS, qA, nS, eS, dS, SA, Fp, Fq, Fn, Fe, Fd, FS, FA,
    fp, fq, fn, fe, fd, fS, valid, pl, ql, el1, el2, dl1, dl2, scr⟩ := h
  exact ⟨spLo, spHi, rd, wr, pq, pn, pe, pd, pS, pA, qn, qe, qd, qS, qA, nS, eS, dS, SA, Fp, Fq, Fn, Fe, Fd, FS, FA,
    fp, fq, fn, fe, fd, fS, valid, pl, ql, el1, el2, dl1, dl2, scr⟩

end VG.Proof.Rsa.Arm.Recover
