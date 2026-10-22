module

public import VerifiedGarbage.Impl.Dsa.Arm.ProbablePrime
public import VerifiedGarbage.Spec.Dsa.ProbablePrime
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract

/-! # DSA's probable-prime test on ARMv7, as its callers see it

The contract of `vg_dsa_probable_prime_{bits}` (`Spec.Dsa.ProbablePrime.contract`
for the ARMv7 layout, 144 bytes of stack) in plain facts: its precondition
(`PIn`, `pre_of_pin`), its postcondition (`PPost`, `ppost_of_post`) and what
two calls must agree on (`pub_of`). `PrimeOk bits code`: a verified test.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Gen
open VG VG.Arm
open VG.Impl.Dsa.Arm.ProbablePrime (keyOff keyWords layout)

/-- The test's contract. -/
abbrev primeK (bits : Nat) : Contract isa := Spec.Dsa.ProbablePrime.contract (layout bits) abi 144

/-- A verified test, with the stack it uses. -/
structure PrimeOk (bits : Nat) (code : Prog isa) : Prop where
  verified : Verified target code (primeK bits)
  stack : FrameStack.armStack code ≤ 144

/-- The candidate at `ws`. -/
abbrev candOf (bits : Nat) (s : State) : Nat :=
  Spec.Dsa.ProbablePrime.candidateAt (layout bits) s.mem (State.addr (s.gpr .r0))

/-- The precondition, as facts. -/
structure PIn (bits : Nat) (s : State) : Prop where
  spLo : 144 ≤ s.sp.toNat
  spHi : s.sp.toNat + 4 ≤ 2 ^ 32
  rd : s.rd = [⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩, ⟨stackArgAddr s 0, 4⟩]
  wr : s.wr = [⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat * 8⟩, ⟨State.addr (stackArg s 0), 8⟩]
  wR : Region.Disjoint ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat * 8⟩ ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩
  wU : Region.Disjoint ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat * 8⟩ ⟨State.addr (stackArg s 0), 8⟩
  wA : Region.Disjoint ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat * 8⟩ ⟨stackArgAddr s 0, 4⟩
  rU : Region.Disjoint ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩ ⟨State.addr (stackArg s 0), 8⟩
  uA : Region.Disjoint ⟨State.addr (stackArg s 0), 8⟩ ⟨stackArgAddr s 0, 4⟩
  FW : Region.Disjoint ⟨State.addr s.sp - 144#64, 144⟩ ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat * 8⟩
  FR : Region.Disjoint ⟨State.addr s.sp - 144#64, 144⟩ ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩
  FU : Region.Disjoint ⟨State.addr s.sp - 144#64, 144⟩ ⟨State.addr (stackArg s 0), 8⟩
  FA : Region.Disjoint ⟨State.addr s.sp - 144#64, 144⟩ ⟨stackArgAddr s 0, 4⟩
  fw : (s.gpr .r0).toNat + (s.gpr .r1).toNat * 8 ≤ 2 ^ 32
  fr : (s.gpr .r2).toNat + (s.gpr .r3).toNat ≤ 2 ^ 32
  fu : (stackArg s 0).toNat + 8 ≤ 2 ^ 32
  size : keyOff + 8 * keyWords bits ≤ 8 * (s.gpr .r1).toNat
  odd : candOf bits s % 2 = 1
  bl : Spec.Dsa.bitLength (candOf bits s) = bits

theorem pre_of_pin {bits : Nat} {s : State} (h : PIn bits s) : (primeK bits).pre s := by
  sig_pre [primeK, Spec.Dsa.ProbablePrime.contract, Spec.Dsa.ProbablePrime.sig, abi, argRegs, reduceClassify, Loc.val]
  exact ⟨h.spLo, h.spHi, h.rd, h.wr, h.wR, h.wU, h.wA, h.rU, h.uA, h.FW, h.FR, h.FU, h.FA, h.fw, h.fr, h.fu, h.size,
    h.odd, h.bl⟩

/-- The test's result. -/
abbrev resOf (bits : Nat) (s : State) : Option (Bool × Spec.RsaKeyGen.Rand) :=
  Spec.Dsa.probablePrime (candOf bits s) (Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat)

/-- The postcondition, as facts. -/
def PPost (bits : Nat) (s t : State) : Prop :=
  (t.gpr .r0).toNat = Spec.Dsa.ProbablePrime.status (resOf bits s) ∧
    Spec.Dsa.ModPow.Keeps (State.addr (s.gpr .r0)) (s.gpr .r1).toNat [(keyOff, 8 * keyWords bits)] s.mem t.mem ∧
    ∀ b rest, resOf bits s = some (b, rest) →
      Spec.Rsa.wordsAt t.mem (State.addr (stackArg s 0)) 1 = [BitVec.ofNat 64 ((s.gpr .r3).toNat - rest.length)]

theorem ppost_of_post {bits : Nat} {s t : State} (h : (primeK bits).post s t) : PPost bits s t := by
  sig_post [primeK, Spec.Dsa.ProbablePrime.contract, Spec.Dsa.ProbablePrime.sig, abi, argRegs, reduceClassify,
    Loc.val, State.addr] at h
  rw [BitVec.setWidth_append_eq_right] at h
  exact h

/-- Two calls with the same public arguments, candidate and tape. -/
theorem pub_of {bits : Nat} {s t : State} (sp : s.sp = t.sp) (p0 : s.gpr .r0 = t.gpr .r0)
    (p1 : s.gpr .r1 = t.gpr .r1) (p2 : s.gpr .r2 = t.gpr .r2) (p3 : s.gpr .r3 = t.gpr .r3)
    (a0 : stackArg s 0 = stackArg t 0) (hc : candOf bits s = candOf bits t)
    (hr : Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat =
      Spec.Rsa.bytesAt t.mem (State.addr (t.gpr .r2)) (t.gpr .r3).toNat) :
    (primeK bits).pub s t := by
  sig_pub [primeK, Spec.Dsa.ProbablePrime.contract, Spec.Dsa.ProbablePrime.sig, abi, argRegs, reduceClassify,
    Loc.val, State.addr]
  exact ⟨sp, by simp only [candOf, State.addr] at hc hr; rw [hc, hr], p0, p1, p2, p3, a0⟩

end VG.Proof.Dsa.Arm.Gen
