module

public import VerifiedGarbage.Proof.Dsa.Arm.Prime.Base
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Dsa.ProbablePrimeContract

/-! # DSA's probable-prime test on ARMv7: the contract's arguments

`mkP bits s`: the public parameters of a call from `s`; `CIn bits s`: the
contract's precondition for the size `bits`, the second stack argument, as
the proof uses it (`cin_of_pre`).
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Prime
open VG VG.Arm
open VG.Impl.Dsa.Arm.ProbablePrime (keyOff keyWords layout)

/-- The public parameters of a call: the frame, the pointers, the lengths,
the candidate and the tape. -/
def mkP (bits : Nat) (s : State) : CP where
  sp := s.sp - BitVec.ofNat 32 88
  uP := stackArg s 0
  nP := s.gpr .r2
  cP := s.gpr .r0
  B := s.gpr .r0 + BitVec.ofNat 32 keyOff
  L := 8 * Impl.Dsa.Arm.ProbablePrime.words bits
  rl := (s.gpr .r3).toNat
  SL := keyWords bits
  bits := bits
  cand := Proof.Dsa.ProbablePrime.candidateAt (layout bits) s.mem (State.addr (s.gpr .r0))
  rnd := Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat

/-- The arguments' regions, and the stack below the caller's. -/
abbrev cW (s : State) : Region := ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat * 8⟩
abbrev cR (s : State) : Region := ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩
abbrev cU (s : State) : Region := ⟨State.addr (stackArg s 0), 8⟩
abbrev cA (s : State) : Region := ⟨stackArgAddr s 0, 8⟩
abbrev cF (s : State) : Region := ⟨State.addr s.sp - 144#64, 144⟩

/-- The sizes the test takes. -/
abbrev Bits (bits : Nat) : Prop := bits = 160 ∨ bits = 256 ∨ bits = 1024 ∨ bits = 2048 ∨ bits = 3072

theorem bits_iff {bits : Nat} : bits ∈ Impl.Dsa.Arm.ProbablePrime.sizes ↔ Bits bits := by
  simp [Impl.Dsa.Arm.ProbablePrime.sizes]

/-- The test's contract. -/
abbrev primeK : Contract isa :=
  Proof.Dsa.ProbablePrime.sizedContract layout Impl.Dsa.Arm.ProbablePrime.sizes abi 144

/-- The contract's precondition, for the size `bits`. -/
structure CIn (bits : Nat) (s : State) : Prop where
  sized : Bits bits
  arg : stackArg s 1 = BitVec.ofNat 32 bits
  spLo : 144 ≤ s.sp.toNat
  spHi : s.sp.toNat + 8 ≤ 2 ^ 32
  rd : s.rd = [cR s, cA s]
  wr : s.wr = [cW s, cU s]
  wR : (cW s).Disjoint (cR s)
  wU : (cW s).Disjoint (cU s)
  wA : (cW s).Disjoint (cA s)
  rU : (cR s).Disjoint (cU s)
  uA : (cU s).Disjoint (cA s)
  FW : (cF s).Disjoint (cW s)
  FR : (cF s).Disjoint (cR s)
  FU : (cF s).Disjoint (cU s)
  FA : (cF s).Disjoint (cA s)
  fw : (s.gpr .r0).toNat + (s.gpr .r1).toNat * 8 ≤ 2 ^ 32
  fr : (s.gpr .r2).toNat + (s.gpr .r3).toNat ≤ 2 ^ 32
  fu : (stackArg s 0).toNat + 8 ≤ 2 ^ 32
  size : keyOff + 8 * keyWords bits ≤ 8 * (s.gpr .r1).toNat
  odd : Proof.Dsa.ProbablePrime.candidateAt (layout bits) s.mem (State.addr (s.gpr .r0)) % 2 = 1
  bl : Spec.Dsa.bitLength (Proof.Dsa.ProbablePrime.candidateAt (layout bits) s.mem (State.addr (s.gpr .r0))) = bits

theorem cin_of_pre (s : State) (h : primeK.pre s) : CIn (stackArg s 1).toNat s := by
  sig_pre [Proof.Dsa.ProbablePrime.sizedContract, Proof.Dsa.ProbablePrime.sizedSig, abi, argRegs, reduceClassify,
    Loc.val] at h
  obtain ⟨spLo, spHi, rd, wr, wR, wU, wA, rU, uA, FW, FR, FU, FA, fw, fr, fu, hb, size, odd, bl⟩ := h
  exact ⟨bits_iff.1 hb, by simp, spLo, spHi, rd, wr, wR, wU, wA, rU, uA, FW, FR, FU, FA, fw, fr, fu, size, odd, bl⟩

end VG.Proof.Dsa.Arm.Prime
