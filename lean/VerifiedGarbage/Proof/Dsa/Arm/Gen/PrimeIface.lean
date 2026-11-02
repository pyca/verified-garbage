module

public import VerifiedGarbage.Impl.Dsa.Arm.ProbablePrime
public import VerifiedGarbage.Proof.Dsa.ProbablePrimeContract
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract

/-! # DSA's probable-prime test on ARMv7, as its callers see it

The contract of `vg_dsa_probable_prime` (`Proof.Dsa.ProbablePrime.sizedContract`
for the ARMv7 layout and sizes, 144 bytes of stack) for a size `bits` in plain
facts: its precondition (`PIn`, `pre_of_pin`), its postcondition (`PPost`,
`ppost_of_post`) and what two calls must agree on (`pub_of`).
`PrimeOk bits code`: a verified test, and `bits` one of its sizes.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Gen
open VG VG.Arm
open VG.Impl.Dsa.Arm.ProbablePrime (keyOff keyWords layout sizes)

/-- The test's contract. -/
abbrev primeK : Contract isa := Proof.Dsa.ProbablePrime.sizedContract layout sizes abi 144

/-- A verified test, with the stack it uses, for a size it takes. -/
structure PrimeOk (bits : Nat) (code : Prog isa) : Prop where
  verified : Verified target code primeK
  stack : FrameStack.armStack code ≤ 144
  sized : bits ∈ sizes

/-- The candidate at `ws`. -/
abbrev candOf (bits : Nat) (s : State) : Nat :=
  Proof.Dsa.ProbablePrime.candidateAt (layout bits) s.mem (State.addr (s.gpr .r0))

/-- The precondition, as facts. -/
structure PIn (bits : Nat) (s : State) : Prop where
  sized : bits ∈ sizes
  arg : stackArg s 1 = BitVec.ofNat 32 bits
  spLo : 144 ≤ s.sp.toNat
  spHi : s.sp.toNat + 8 ≤ 2 ^ 32
  rd : s.rd = [⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩, ⟨stackArgAddr s 0, 8⟩]
  wr : s.wr = [⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat * 8⟩, ⟨State.addr (stackArg s 0), 8⟩]
  wR : Region.Disjoint ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat * 8⟩ ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩
  wU : Region.Disjoint ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat * 8⟩ ⟨State.addr (stackArg s 0), 8⟩
  wA : Region.Disjoint ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat * 8⟩ ⟨stackArgAddr s 0, 8⟩
  rU : Region.Disjoint ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩ ⟨State.addr (stackArg s 0), 8⟩
  uA : Region.Disjoint ⟨State.addr (stackArg s 0), 8⟩ ⟨stackArgAddr s 0, 8⟩
  FW : Region.Disjoint ⟨State.addr s.sp - 144#64, 144⟩ ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat * 8⟩
  FR : Region.Disjoint ⟨State.addr s.sp - 144#64, 144⟩ ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩
  FU : Region.Disjoint ⟨State.addr s.sp - 144#64, 144⟩ ⟨State.addr (stackArg s 0), 8⟩
  FA : Region.Disjoint ⟨State.addr s.sp - 144#64, 144⟩ ⟨stackArgAddr s 0, 8⟩
  fw : (s.gpr .r0).toNat + (s.gpr .r1).toNat * 8 ≤ 2 ^ 32
  fr : (s.gpr .r2).toNat + (s.gpr .r3).toNat ≤ 2 ^ 32
  fu : (stackArg s 0).toNat + 8 ≤ 2 ^ 32
  size : keyOff + 8 * keyWords bits ≤ 8 * (s.gpr .r1).toNat
  odd : candOf bits s % 2 = 1
  bl : Spec.Dsa.bitLength (candOf bits s) = bits

/-- The size, from the second stack argument. -/
theorem PIn.bits {bits : Nat} {s : State} (h : PIn bits s) : (stackArg s 1).toNat = bits := by
  rw [h.arg, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  have := h.sized; simp only [sizes, List.mem_cons, List.not_mem_nil, or_false] at this
  rcases this with rfl | rfl | rfl | rfl | rfl <;> decide

theorem pre_of_pin {bits : Nat} {s : State} (h : PIn bits s) : primeK.pre s := by
  sig_pre [primeK, Proof.Dsa.ProbablePrime.sizedContract, Proof.Dsa.ProbablePrime.sizedSig, abi, argRegs,
    reduceClassify, Loc.val]
  rw [h.bits]
  exact ⟨h.spLo, h.spHi, h.rd, h.wr, h.wR, h.wU, h.wA, h.rU, h.uA, h.FW, h.FR, h.FU, h.FA, h.fw, h.fr, h.fu, h.sized,
    h.size, h.odd, h.bl⟩

/-- The test's result. -/
abbrev resOf (bits : Nat) (s : State) : Option (Bool × Spec.RsaKeyGen.Rand) :=
  Spec.Dsa.probablePrime (candOf bits s) (Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat)

/-- The postcondition, as facts. -/
def PPost (bits : Nat) (s t : State) : Prop :=
  (t.gpr .r0).toNat = Proof.Dsa.ProbablePrime.status (resOf bits s) ∧
    Proof.Dsa.ModPow.Keeps (State.addr (s.gpr .r0)) (s.gpr .r1).toNat [(keyOff, 8 * keyWords bits)] s.mem t.mem ∧
    ∀ b rest, resOf bits s = some (b, rest) →
      Spec.Rsa.wordsAt t.mem (State.addr (stackArg s 0)) 1 = [BitVec.ofNat 64 ((s.gpr .r3).toNat - rest.length)]

theorem ppost_of_post {bits : Nat} {s t : State} (hb : (stackArg s 1).toNat = bits) (h : primeK.post s t) :
    PPost bits s t := by
  sig_post [primeK, Proof.Dsa.ProbablePrime.sizedContract, Proof.Dsa.ProbablePrime.sizedSig, abi, argRegs,
    reduceClassify, Loc.val, State.addr] at h
  rw [BitVec.setWidth_append_eq_right, hb] at h
  exact h

/-- Two calls with the same public arguments, candidate and tape. -/
theorem pub_of {bits : Nat} {s t : State} (sp : s.sp = t.sp) (p0 : s.gpr .r0 = t.gpr .r0)
    (p1 : s.gpr .r1 = t.gpr .r1) (p2 : s.gpr .r2 = t.gpr .r2) (p3 : s.gpr .r3 = t.gpr .r3)
    (a0 : stackArg s 0 = stackArg t 0) (a1 : stackArg s 1 = stackArg t 1) (hb : (stackArg s 1).toNat = bits)
    (hc : candOf bits s = candOf bits t)
    (hr : Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat =
      Spec.Rsa.bytesAt t.mem (State.addr (t.gpr .r2)) (t.gpr .r3).toNat) :
    primeK.pub s t := by
  sig_pub [primeK, Proof.Dsa.ProbablePrime.sizedContract, Proof.Dsa.ProbablePrime.sizedSig, abi, argRegs,
    reduceClassify, Loc.val, State.addr]
  rw [← a1, hb]
  exact ⟨sp, by simp only [candOf, State.addr] at hc hr; rw [hc, hr], p0, p1, p2, p3, a0, rfl⟩

end VG.Proof.Dsa.Arm.Gen
