module

public import VerifiedGarbage.Proof.Dsa.X86_64.ProbablePrime.ABI
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeState
import VerifiedGarbage.Proof.Dsa.Generation.Primality
import VerifiedGarbage.Proof.Dsa.BitLengthBounds
import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Dsa.ProbablePrimeContract

/-! # The generation's prime-test parameters, from the function's arguments

The test runs the generation's `primeBytes` on the arithmetic workspace at
`Layout.arithmetic` of `ws`, with the witness buffer at `Layout.witness`, the
tape `rand` and the stack below the function's 56-byte frame.
-/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.ProbablePrime
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Dsa.X86_64.ProbablePrime VG.Impl.Dsa.Generation.Layout
open VG.Proof.Dsa.X86_64.Generation (PrimeParams)

/-- The frame's stack pointer. -/
abbrev frameSp (s : State) : Addr := s.gpr .rsp - BitVec.ofNat 64 56

/-- The candidate. -/
abbrev candidateOf (bits : Nat) (s : State) : Nat :=
  Proof.Dsa.ProbablePrime.candidateAt (layout bits) s.mem (s.gpr .rdi)

/-- `ws`'s region. -/
abbrev wsRegion (s : State) : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat * 8⟩

theorem ws_sub {bits : Nat} {s : State} (A : PrimeABI bits s) {d n : Nat} (h : d + n ≤ domainCheck) :
    Region.Sub ⟨off (s.gpr .rdi) d, n⟩ (wsRegion s) :=
  Offset.sub_base _ (by have := A.size; omega)

theorem frame_stack_sub (s : State) {d n : Nat} (h : d + n ≤ 56) :
    Region.Sub ⟨off (frameSp s) d, n⟩ (below (s.gpr .rsp) 184) := by
  rw [show off (frameSp s) d = s.gpr .rsp - BitVec.ofNat 64 184 + BitVec.ofNat 64 (128 + d) by
    simp only [off, frameSp]
    rw [Offset.sub_ofNat_eq (s.gpr .rsp) (show 56 ≤ 184 by decide), BitVec.add_assoc,
      BitVec.ofNat_add_ofNat]]
  exact Offset.sub_base _ (by omega)

theorem below_frame_sub (s : State) :
    Region.Sub (below (frameSp s) 128) (below (s.gpr .rsp) 184) := by
  change Region.Sub ⟨s.gpr .rsp - BitVec.ofNat 64 56 - BitVec.ofNat 64 128, 128⟩ _
  rw [BitVec.sub_sub, BitVec.ofNat_add_ofNat]
  exact Offset.sub_below _ (by decide) (by decide)

def params {bits : Nat} (hb : Supported bits) {s : State} (A : PrimeABI bits s) : PrimeParams where
  B := off (s.gpr .rdi) arithmetic
  p := off (s.gpr .rdi) witness
  rp := s.gpr .rdx
  sp := frameSp s
  Z := arithmeticBytes
  w := words bits
  N := candidateOf bits s
  len := len bits
  drawBytes := draw bits
  checks := checks bits
  rand := Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat
  dims := by rcases hb with rfl | rfl | rfl | rfl | rfl <;> constructor <;> decide
  room := by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
  len2 := by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
  lenDraw := by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
  drawMax := by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
  drawMin := by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
  lenWords := by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
  predBits := by
    rw [VG.Proof.Dsa.Generation.predecessor_bits (by have := hb.le; omega) A.odd A.bits]
    rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
  drawWidth := by
    rw [VG.Proof.Dsa.Generation.witness_width (by have := hb.le; omega) A.odd A.bits]
    rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
  odd := A.odd
  n3 := by
    have h := ((bitLength_iff_bounds (by have := hb.le; omega)).mp A.bits).1
    have h4 : 2 ^ 2 ≤ 2 ^ (bits - 1) := Nat.pow_le_pow_right (by decide) (by have := hb.le; omega)
    exact Nat.le_trans (by decide) (Nat.le_trans h4 h)
  checksMax := by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
  randMax := by rw [bytesAt_length]; exact (s.gpr .rcx).isLt
  stackSize := by
    change 128 ≤ (s.gpr .rsp - BitVec.ofNat 64 56).toNat
    have : 184 ≤ (s.gpr .rsp).toNat := A.stackLower
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat]; omega)]
    simp only [BitVec.toNat_ofNat]
    omega
  stackSeparate :=
    ((A.stackWs.sub_left (below_frame_sub s)).sub_right (ws_sub A (by decide))).symm
  bufferSeparate := Offset.disjoint _ (by
    right; rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide) (by decide)
    (by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide)
  bufferOutside := by
    intro i hi
    apply out_scr (r := ⟨off (s.gpr .rdi) witness, len bits⟩)
    · exact Offset.disjoint _ (by
        left; rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide)
        (by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide) (by decide)
    · exact contains_byte _ hi (by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide)
  tapeBuffer := by
    rw [bytesAt_length]
    exact A.wsRand.symm.sub_right (ws_sub A (by
      rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide))
  tapeStack := by
    rw [bytesAt_length]
    exact (A.stackRand.sub_left (below_frame_sub s)).symm

end VG.Proof.Dsa.X86_64.ProbablePrime
