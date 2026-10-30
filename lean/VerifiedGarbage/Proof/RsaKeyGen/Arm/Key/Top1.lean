module

public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.Base
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Framework.Sig
import Mathlib.Tactic.Finiteness.Attr
public import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Tactic.Basic
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit

/-! # An RSA key on ARMv7: the contract's arguments

`mkP s`: the public parameters of a call from `s`; `CIn s`: the contract's
precondition, as the proof uses it (`cin_of_pre`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Key
open VG VG.Arm

/-- The public parameters of a call: the frame, the pointers, the lengths,
`e` and the status returned. -/
def mkP (s : State) : KP where
  sp := s.sp - BitVec.ofNat 32 56
  nP := s.gpr .r0
  dP := s.gpr .r2
  pP := stackArg s 0
  qP := stackArg s 2
  dpP := stackArg s 4
  dqP := stackArg s 6
  qiP := stackArg s 8
  eP := stackArg s 10
  B := stackArg s 12
  K := (stackArg s 1).toNat
  el := (stackArg s 11).toNat
  SL := (stackArg s 13).toNat
  eB := Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 10)) (stackArg s 11).toNat
  st := Spec.RsaKeyGen.keyStatus (Spec.RsaKeyGen.keyOp (stackArg s 1).toNat
    (Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 10)) (stackArg s 11).toNat)
    (Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 0)) (stackArg s 1).toNat)
    (Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 2)) (stackArg s 1).toNat))

/-- The regions the body runs with: the frame, the outputs and the working space. -/
def xRegs (s : State) : List Region :=
  [(mkP s).rFr, (mkP s).rN, (mkP s).rD, (mkP s).rP, (mkP s).rQ, (mkP s).rDp, (mkP s).rDq, (mkP s).rQi, (mkP s).rS]

/-- The arguments' regions. -/
abbrev cN (s : State) : Region := ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩
abbrev cD (s : State) : Region := ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩
abbrev cP (s : State) : Region := ⟨State.addr (stackArg s 0), (stackArg s 1).toNat⟩
abbrev cQ (s : State) : Region := ⟨State.addr (stackArg s 2), (stackArg s 3).toNat⟩
abbrev cDp (s : State) : Region := ⟨State.addr (stackArg s 4), (stackArg s 5).toNat⟩
abbrev cDq (s : State) : Region := ⟨State.addr (stackArg s 6), (stackArg s 7).toNat⟩
abbrev cQi (s : State) : Region := ⟨State.addr (stackArg s 8), (stackArg s 9).toNat⟩
abbrev cE (s : State) : Region := ⟨State.addr (stackArg s 10), (stackArg s 11).toNat⟩
abbrev cS (s : State) : Region := ⟨State.addr (stackArg s 12), (stackArg s 13).toNat * 8⟩
abbrev cA (s : State) : Region := ⟨stackArgAddr s 0, 56⟩
abbrev cF (s : State) : Region := ⟨State.addr s.sp - 56#64, 56⟩

/-- The contract's precondition. -/
structure CIn (s : State) : Prop where
  spLo : 56 ≤ s.sp.toNat
  spHi : s.sp.toNat + 56 ≤ 2 ^ 32
  rd : s.rd = [cE s, cA s]
  wr : s.wr = [cN s, cD s, cP s, cQ s, cDp s, cDq s, cQi s, cS s]
  nD : (cN s).Disjoint (cD s)
  nP : (cN s).Disjoint (cP s)
  nQ : (cN s).Disjoint (cQ s)
  nDp : (cN s).Disjoint (cDp s)
  nDq : (cN s).Disjoint (cDq s)
  nQi : (cN s).Disjoint (cQi s)
  nE : (cN s).Disjoint (cE s)
  nS : (cN s).Disjoint (cS s)
  nA : (cN s).Disjoint (cA s)
  dP : (cD s).Disjoint (cP s)
  dQ : (cD s).Disjoint (cQ s)
  dDp : (cD s).Disjoint (cDp s)
  dDq : (cD s).Disjoint (cDq s)
  dQi : (cD s).Disjoint (cQi s)
  dE : (cD s).Disjoint (cE s)
  dS : (cD s).Disjoint (cS s)
  dA : (cD s).Disjoint (cA s)
  pQ : (cP s).Disjoint (cQ s)
  pDp : (cP s).Disjoint (cDp s)
  pDq : (cP s).Disjoint (cDq s)
  pQi : (cP s).Disjoint (cQi s)
  pE : (cP s).Disjoint (cE s)
  pS : (cP s).Disjoint (cS s)
  pA : (cP s).Disjoint (cA s)
  qDp : (cQ s).Disjoint (cDp s)
  qDq : (cQ s).Disjoint (cDq s)
  qQi : (cQ s).Disjoint (cQi s)
  qE : (cQ s).Disjoint (cE s)
  qS : (cQ s).Disjoint (cS s)
  qA : (cQ s).Disjoint (cA s)
  dpDq : (cDp s).Disjoint (cDq s)
  dpQi : (cDp s).Disjoint (cQi s)
  dpE : (cDp s).Disjoint (cE s)
  dpS : (cDp s).Disjoint (cS s)
  dpA : (cDp s).Disjoint (cA s)
  dqQi : (cDq s).Disjoint (cQi s)
  dqE : (cDq s).Disjoint (cE s)
  dqS : (cDq s).Disjoint (cS s)
  dqA : (cDq s).Disjoint (cA s)
  qiE : (cQi s).Disjoint (cE s)
  qiS : (cQi s).Disjoint (cS s)
  qiA : (cQi s).Disjoint (cA s)
  eS : (cE s).Disjoint (cS s)
  SA : (cS s).Disjoint (cA s)
  Fn : (cF s).Disjoint (cN s)
  Fd : (cF s).Disjoint (cD s)
  Fp : (cF s).Disjoint (cP s)
  Fq : (cF s).Disjoint (cQ s)
  Fdp : (cF s).Disjoint (cDp s)
  Fdq : (cF s).Disjoint (cDq s)
  Fqi : (cF s).Disjoint (cQi s)
  Fe : (cF s).Disjoint (cE s)
  FS : (cF s).Disjoint (cS s)
  FA : (cF s).Disjoint (cA s)
  fn : (s.gpr .r0).toNat + (s.gpr .r1).toNat ≤ 2 ^ 32
  fd : (s.gpr .r2).toNat + (s.gpr .r3).toNat ≤ 2 ^ 32
  fp : (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 32
  fq : (stackArg s 2).toNat + (stackArg s 3).toNat ≤ 2 ^ 32
  fdp : (stackArg s 4).toNat + (stackArg s 5).toNat ≤ 2 ^ 32
  fdq : (stackArg s 6).toNat + (stackArg s 7).toNat ≤ 2 ^ 32
  fqi : (stackArg s 8).toNat + (stackArg s 9).toNat ≤ 2 ^ 32
  fe : (stackArg s 10).toNat + (stackArg s 11).toNat ≤ 2 ^ 32
  fS : (stackArg s 12).toNat + (stackArg s 13).toNat * 8 ≤ 2 ^ 32
  valid : Spec.RsaKeyGen.primeLenValid (stackArg s 1).toNat
  nl : (s.gpr .r1).toNat = 2 * (stackArg s 1).toNat
  dl : (s.gpr .r3).toNat = (s.gpr .r1).toNat
  ql : (stackArg s 3).toNat = (stackArg s 1).toNat
  dpl : (stackArg s 5).toNat = (stackArg s 1).toNat
  dql : (stackArg s 7).toNat = (stackArg s 1).toNat
  qil : (stackArg s 9).toNat = (stackArg s 1).toNat
  el1 : 1 ≤ (stackArg s 11).toNat
  el2 : (stackArg s 11).toNat ≤ 8
  scr : Spec.Rsa.scratchWords (s.gpr .r1).toNat ≤ (stackArg s 13).toNat

theorem cin_of_pre (s : State) (h : (Spec.RsaKeyGen.keyContract abi 56).pre s) : CIn s := by
  sig_pre [Spec.RsaKeyGen.keyContract, Spec.RsaKeyGen.keySig, abi, argRegs, reduceClassify, Loc.val] at h
  sig_split h
  rename_i spLo spHi rd wr nD nP nQ nDp nDq nQi nE nS nA dP dQ dDp dDq dQi dE dS dA pQ pDp pDq pQi pE pS pA
    qDp qDq qQi qE qS qA dpDq dpQi dpE dpS dpA dqQi dqE dqS dqA qiE qiS qiA eS SA Fn Fd Fp Fq Fdp Fdq Fqi Fe
    FS FA fn fd fp fq fdp fdq fqi fe fS valid nl dl ql dpl dql qil el1 el2
  have scr := h
  exact ⟨spLo, spHi, rd, wr, nD, nP, nQ, nDp, nDq, nQi, nE, nS, nA, dP, dQ, dDp, dDq, dQi, dE, dS, dA,
    pQ, pDp, pDq, pQi, pE, pS, pA, qDp, qDq, qQi, qE, qS, qA, dpDq, dpQi, dpE, dpS, dpA, dqQi, dqE, dqS, dqA,
    qiE, qiS, qiA, eS, SA, Fn, Fd, Fp, Fq, Fdp, Fdq, Fqi, Fe, FS, FA, fn, fd, fp, fq, fdp, fdq, fqi, fe, fS,
    valid, nl, dl, ql, dpl, dql, qil, el1, el2, scr⟩

end VG.Proof.RsaKeyGen.Arm.Key
