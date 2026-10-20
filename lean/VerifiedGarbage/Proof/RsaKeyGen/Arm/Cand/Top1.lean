module

public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import Mathlib.Data.Int.ModEq
public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Base
public import VerifiedGarbage.Proof.RsaKeyGen.Table
public import VerifiedGarbage.TCB.Arm.Target

/-! # A candidate on ARMv7: the contract's arguments

`mkP s`: the public parameters of a call from `s` (the branches only when
`rand` holds the candidate's octets, as the leak determines them then);
`CIn s`: the contract's precondition, as the proof uses it (`cin_of_pre`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Cand
open VG VG.Arm

/-- The public parameters of a call: the frame, the pointers, the lengths,
`e` and the branches. -/
def mkP (s : State) : CP where
  sp := s.sp - BitVec.ofNat 32 56
  oP := s.gpr .r0
  uP := s.gpr .r2
  eP := s.gpr .r3
  pP := stackArg s 1
  nP := stackArg s 3
  B := stackArg s 5
  L := (s.gpr .r1).toNat
  el := (stackArg s 0).toNat
  pl := (stackArg s 2).toNat
  rl := (stackArg s 4).toNat
  SL := (stackArg s 6).toNat
  eB := Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r3)) (stackArg s 0).toNat
  sch := if (s.gpr .r1).toNat ≤ (stackArg s 4).toNat then
      VG.Proof.RsaKeyGen.schedOf (s.gpr .r1).toNat
        (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r3)) (stackArg s 0).toNat))
        (Spec.RsaKeyGen.otherPrime (Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 1)) (stackArg s 2).toNat))
        (Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 3)) (stackArg s 4).toNat)
    else ⟨false, false, false, none⟩

/-- The regions the body runs with: the frame, `out`, `used`, the working
space, and Montgomery multiplication's part of it. -/
def xRegs (s : State) : List Region := [(mkP s).rFr, (mkP s).rO, (mkP s).rU, (mkP s).rS, (mkP s).rM]

/-- The arguments' regions. -/
abbrev cO (s : State) : Region := ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩
abbrev cU (s : State) : Region := ⟨State.addr (s.gpr .r2), 8⟩
abbrev cE (s : State) : Region := ⟨State.addr (s.gpr .r3), (stackArg s 0).toNat⟩
abbrev cP (s : State) : Region := ⟨State.addr (stackArg s 1), (stackArg s 2).toNat⟩
abbrev cR (s : State) : Region := ⟨State.addr (stackArg s 3), (stackArg s 4).toNat⟩
abbrev cS (s : State) : Region := ⟨State.addr (stackArg s 5), (stackArg s 6).toNat * 8⟩
abbrev cA (s : State) : Region := ⟨stackArgAddr s 0, 28⟩
abbrev cF (s : State) : Region := ⟨State.addr s.sp - 112#64, 112⟩

/-- The contract's precondition. -/
structure CIn (s : State) : Prop where
  spLo : 112 ≤ s.sp.toNat
  spHi : s.sp.toNat + 28 ≤ 2 ^ 32
  rd : s.rd = [cE s, cP s, cR s, cA s]
  wr : s.wr = [cO s, cU s, cS s]
  oU : (cO s).Disjoint (cU s)
  oE : (cO s).Disjoint (cE s)
  oP : (cO s).Disjoint (cP s)
  oR : (cO s).Disjoint (cR s)
  oS : (cO s).Disjoint (cS s)
  oA : (cO s).Disjoint (cA s)
  uE : (cU s).Disjoint (cE s)
  uP : (cU s).Disjoint (cP s)
  uR : (cU s).Disjoint (cR s)
  uS : (cU s).Disjoint (cS s)
  uA : (cU s).Disjoint (cA s)
  eS : (cE s).Disjoint (cS s)
  pS : (cP s).Disjoint (cS s)
  rS : (cR s).Disjoint (cS s)
  SA : (cS s).Disjoint (cA s)
  Fo : (cF s).Disjoint (cO s)
  Fu : (cF s).Disjoint (cU s)
  Fe : (cF s).Disjoint (cE s)
  Fp : (cF s).Disjoint (cP s)
  Fr : (cF s).Disjoint (cR s)
  FS : (cF s).Disjoint (cS s)
  FA : (cF s).Disjoint (cA s)
  fo : (s.gpr .r0).toNat + (s.gpr .r1).toNat ≤ 2 ^ 32
  fu : (s.gpr .r2).toNat + 8 ≤ 2 ^ 32
  fe : (s.gpr .r3).toNat + (stackArg s 0).toNat ≤ 2 ^ 32
  fp : (stackArg s 1).toNat + (stackArg s 2).toNat ≤ 2 ^ 32
  fr : (stackArg s 3).toNat + (stackArg s 4).toNat ≤ 2 ^ 32
  fS : (stackArg s 5).toNat + (stackArg s 6).toNat * 8 ≤ 2 ^ 32
  valid : Spec.RsaKeyGen.primeLenValid (s.gpr .r1).toNat
  el1 : 1 ≤ (stackArg s 0).toNat
  el2 : (stackArg s 0).toNat ≤ 8
  plv : (stackArg s 2).toNat = 0 ∨ (stackArg s 2).toNat = (s.gpr .r1).toNat
  scr : Spec.Rsa.scratchWords (s.gpr .r1).toNat ≤ (stackArg s 6).toNat

theorem cin_of_pre (s : State) (h : (Spec.RsaKeyGen.candidateContract abi 112).pre s) : CIn s := by
  sig_pre [Spec.RsaKeyGen.candidateContract, Spec.RsaKeyGen.candidateSig, abi, argRegs, reduceClassify, Loc.val] at h
  obtain ⟨spLo, spHi, rd, wr, oU, oE, oP, oR, oS, oA, uE, uP, uR, uS, uA, eS, pS, rS, SA, Fo, Fu, Fe, Fp, Fr, FS, FA,
    fo, fu, fe, fp, fr, fS, valid, el1, el2, plv, scr⟩ := h
  exact ⟨spLo, spHi, rd, wr, oU, oE, oP, oR, oS, oA, uE, uP, uR, uS, uA, eS, pS, rS, SA, Fo, Fu, Fe, Fp, Fr, FS, FA,
    fo, fu, fe, fp, fr, fS, valid, el1, el2, plv, scr⟩

end VG.Proof.RsaKeyGen.Arm.Cand
