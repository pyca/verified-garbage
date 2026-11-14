module

public import VerifiedGarbage.Impl.Dsa.AArch64.ProbablePrime
public import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.Dsa.ProbablePrimeContract
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeState
import VerifiedGarbage.Proof.Dsa.Generation.Primality
import VerifiedGarbage.Proof.Dsa.BitLengthBounds
import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-! ### `Dsa.AArch64.ProbablePrime.ABI`, which only this module used -/

section

/-! # The probable-prime test's arguments, from its contract's precondition -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.ProbablePrime
open VG VG.AArch64

/-- The stack the test uses: its frame (the round is a leaf). -/
abbrev stack : Nat := 272

/-- The test's contract on AArch64. -/
abbrev contract (bits : Nat) : Contract isa :=
  Proof.Dsa.ProbablePrime.contract (Impl.Dsa.AArch64.ProbablePrime.layout bits) abi stack

structure PrimeABI (bits : Nat) (s : State) : Prop where
  stackLower : stack ≤ s.sp.toNat
  rd : s.rd = [⟨s.gpr .x2, (s.gpr .x3).toNat⟩]
  wr : s.wr = [⟨s.gpr .x0, (s.gpr .x1).toNat * 8⟩, ⟨s.gpr .x4, 8⟩]
  wsRand : (⟨s.gpr .x0, (s.gpr .x1).toNat * 8⟩ : Region).Disjoint ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
  wsUsed : (⟨s.gpr .x0, (s.gpr .x1).toNat * 8⟩ : Region).Disjoint ⟨s.gpr .x4, 8⟩
  randUsed : (⟨s.gpr .x2, (s.gpr .x3).toNat⟩ : Region).Disjoint ⟨s.gpr .x4, 8⟩
  stackWs : (below s.sp stack : Region).Disjoint ⟨s.gpr .x0, (s.gpr .x1).toNat * 8⟩
  stackRand : (below s.sp stack : Region).Disjoint ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
  stackUsed : (below s.sp stack : Region).Disjoint ⟨s.gpr .x4, 8⟩
  wsBound : (s.gpr .x0).toNat + (s.gpr .x1).toNat * 8 ≤ 2 ^ 64
  randBound : (s.gpr .x2).toNat + (s.gpr .x3).toNat ≤ 2 ^ 64
  usedBound : (s.gpr .x4).toNat + 8 ≤ 2 ^ 64
  size : Impl.Dsa.Generation.Layout.domainCheck ≤ 8 * (s.gpr .x1).toNat
  odd : Proof.Dsa.ProbablePrime.candidateAt (Impl.Dsa.AArch64.ProbablePrime.layout bits) s.mem (s.gpr .x0) % 2 = 1
  bits : Spec.Dsa.bitLength
    (Proof.Dsa.ProbablePrime.candidateAt (Impl.Dsa.AArch64.ProbablePrime.layout bits) s.mem (s.gpr .x0)) = bits

theorem primeABI_of {bits : Nat} {s : State} (h : (contract bits).pre s) : PrimeABI bits s := by
  sig_pre [contract, Proof.Dsa.ProbablePrime.contract, Proof.Dsa.ProbablePrime.sig, abi, argRegs] at h
  sig_split h
  constructor <;> with_reducible assumption

end VG.Proof.Dsa.AArch64.ProbablePrime

end

end


/-! # The generation's prime-test parameters, from the function's arguments

The test runs the generation's `checkPrime` on the arithmetic workspace at
`Layout.arithmetic` of `ws`, with the witness buffer at `Layout.witness` and
the tape `rand`.
-/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.ProbablePrime
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.Dsa.AArch64.ProbablePrime VG.Impl.Dsa.Generation.Layout
open VG.Proof.Dsa.AArch64.Generation (PrimeParams)

/-- The candidate widths parameter generation tests. -/
def Supported (bits : Nat) : Prop :=
  bits = 160 ∨ bits = 256 ∨ bits = 1024 ∨ bits = 2048 ∨ bits = 3072

theorem Supported.le {bits : Nat} (hb : Supported bits) : 160 ≤ bits ∧ bits ≤ 3072 := by
  rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide

/-- The candidate. -/
abbrev candidateOf (bits : Nat) (s : State) : Nat :=
  Proof.Dsa.ProbablePrime.candidateAt (layout bits) s.mem (s.gpr .x0)

/-- `ws`'s region. -/
abbrev wsRegion (s : State) : Region := ⟨s.gpr .x0, (s.gpr .x1).toNat * 8⟩

theorem ws_sub {bits : Nat} {s : State} (A : PrimeABI bits s) {d n : Nat} (h : d + n ≤ domainCheck) :
    Region.Sub ⟨off (s.gpr .x0) d, n⟩ (wsRegion s) :=
  Offset.sub_base _ (by have := A.size; omega_using [h, this])

def params {bits : Nat} (hb : Supported bits) {s : State} (A : PrimeABI bits s) : PrimeParams where
  B := off (s.gpr .x0) arithmetic
  p := off (s.gpr .x0) witness
  rp := s.gpr .x2
  Z := arithmeticBytes
  w := words bits
  N := candidateOf bits s
  len := len bits
  drawBytes := draw bits
  checks := checks bits
  rand := Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat
  w4 := by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
  w128 := by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
  room := by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
  len2 := by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
  lenDraw := by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
  drawMax := by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
  drawMin := by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
  lenWords := by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
  predBits := by
    rw [VG.Proof.Dsa.Generation.predecessor_bits (by have := hb.le; omega_using [this]) A.odd A.bits]
    rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
  drawWidth := by
    rw [VG.Proof.Dsa.Generation.witness_width (by have := hb.le; omega_using [this]) A.odd A.bits]
    rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
  odd := A.odd
  n3 := by
    have h := ((bitLength_iff_bounds (by have := hb.le; omega_using [this])).mp A.bits).1
    have h4 : 2 ^ 2 ≤ 2 ^ (bits - 1) := Nat.pow_le_pow_right (by decide) (by have := hb.le; omega_using [this])
    exact Nat.le_trans (by decide) (Nat.le_trans h4 h)
  checksMax := by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
  randMax := by rw [bytesAt_length]; exact (s.gpr .x3).isLt
  bufferSeparate := Offset.disjoint _ (by
    right; rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide) (by decide)
    (by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide)
  bufferOutside := by
    intro i hi
    apply out_scr (r := ⟨off (s.gpr .x0) witness, len bits⟩)
    · exact Offset.disjoint _ (by
        left; rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide)
        (by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide) (by decide)
    · exact contains_byte _ hi (by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide)
  tapeBuffer := by
    rw [bytesAt_length]
    exact A.wsRand.symm.sub_right (ws_sub A (by
      rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide))

end VG.Proof.Dsa.AArch64.ProbablePrime
