module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeState
import VerifiedGarbage.Proof.Dsa.Generation.Primality
import VerifiedGarbage.Proof.Dsa.BitLengthBounds
import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Dsa.ProbablePrimeContract
public import VerifiedGarbage.Impl.Dsa.X86_64.ProbablePrime
public import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Proof.Framework.Sig

/-! ### `Dsa.X86_64.ProbablePrime.ABI`, which this module and modules that import it used -/

section

/-! # The probable-prime test's arguments, from its contract's precondition -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.ProbablePrime
open VG VG.X86_64

/-- The stack the test uses: its frame and the round's calls. -/
abbrev stack : Nat := 184

/-- The test's contract on x86-64. -/
abbrev contract : Contract isa :=
  Proof.Dsa.ProbablePrime.sizedContract Impl.Dsa.X86_64.ProbablePrime.layout
    Impl.Dsa.X86_64.ProbablePrime.sizes abi stack

/-- The candidate widths parameter generation tests. -/
def Supported (bits : Nat) : Prop :=
  bits = 160 ∨ bits = 256 ∨ bits = 1024 ∨ bits = 2048 ∨ bits = 3072

theorem Supported.of_mem {bits : Nat} (h : bits ∈ Impl.Dsa.X86_64.ProbablePrime.sizes) :
    Supported bits := by
  simpa only [Supported, Impl.Dsa.X86_64.ProbablePrime.sizes, List.mem_cons, List.not_mem_nil,
    or_false] using h

theorem Supported.mem {bits : Nat} (h : Supported bits) : bits ∈ Impl.Dsa.X86_64.ProbablePrime.sizes := by
  rcases h with rfl | rfl | rfl | rfl | rfl <;> decide

theorem Supported.le {bits : Nat} (hb : Supported bits) : 160 ≤ bits ∧ bits ≤ 3072 := by
  rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide

structure PrimeABI (bits : Nat) (s : State) : Prop where
  width : s.gpr .r9 = BitVec.ofNat 64 bits
  stackLower : stack ≤ (s.gpr .rsp).toNat
  rd : s.rd = [⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩]
  wr : s.wr = [⟨s.gpr .rdi, (s.gpr .rsi).toNat * 8⟩, ⟨s.gpr .r8, 8⟩]
  wsRand : (⟨s.gpr .rdi, (s.gpr .rsi).toNat * 8⟩ : Region).Disjoint ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
  wsUsed : (⟨s.gpr .rdi, (s.gpr .rsi).toNat * 8⟩ : Region).Disjoint ⟨s.gpr .r8, 8⟩
  randUsed : (⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩ : Region).Disjoint ⟨s.gpr .r8, 8⟩
  retWs : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat * 8⟩
  retRand : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
  retUsed : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .r8, 8⟩
  stackWs : (below (s.gpr .rsp) stack : Region).Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat * 8⟩
  stackRand : (below (s.gpr .rsp) stack : Region).Disjoint ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
  stackUsed : (below (s.gpr .rsp) stack : Region).Disjoint ⟨s.gpr .r8, 8⟩
  wsBound : (s.gpr .rdi).toNat + (s.gpr .rsi).toNat * 8 ≤ 2 ^ 64
  randBound : (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64
  usedBound : (s.gpr .r8).toNat + 8 ≤ 2 ^ 64
  size : Impl.Dsa.Generation.Layout.domainCheck ≤ 8 * (s.gpr .rsi).toNat
  odd : Proof.Dsa.ProbablePrime.candidateAt (Impl.Dsa.X86_64.ProbablePrime.layout bits) s.mem (s.gpr .rdi) % 2 = 1
  bits : Spec.Dsa.bitLength
    (Proof.Dsa.ProbablePrime.candidateAt (Impl.Dsa.X86_64.ProbablePrime.layout bits) s.mem (s.gpr .rdi)) = bits

theorem primeABI_of {s : State} (h : contract.pre s) :
    Supported (s.gpr .r9).toNat ∧ PrimeABI (s.gpr .r9).toNat s := by
  sig_pre [contract, Proof.Dsa.ProbablePrime.sizedContract, Proof.Dsa.ProbablePrime.sizedSig, abi,
    argRegs] at h
  sig_split h
  refine ⟨Supported.of_mem (by with_reducible assumption), ?_⟩
  constructor <;> first | with_reducible assumption | exact (BitVec.ofNat_toNat 64 _ |>.trans (BitVec.setWidth_eq _)).symm

end VG.Proof.Dsa.X86_64.ProbablePrime

end

end

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
  Offset.sub_base _ (by have := A.size; omega_using [h, this])

theorem frame_stack_sub (s : State) {d n : Nat} (h : d + n ≤ 56) :
    Region.Sub ⟨off (frameSp s) d, n⟩ (below (s.gpr .rsp) 184) := by
  rw [show off (frameSp s) d = s.gpr .rsp - BitVec.ofNat 64 184 + BitVec.ofNat 64 (128 + d) by
    simp only [off, frameSp]
    rw [Offset.sub_ofNat_eq (s.gpr .rsp) (show 56 ≤ 184 by decide), BitVec.add_assoc,
      BitVec.ofNat_add_ofNat]]
  exact Offset.sub_base _ (by omega_using [h])

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
  randMax := by rw [bytesAt_length]; exact (s.gpr .rcx).isLt
  stackSize := by
    change 128 ≤ (s.gpr .rsp - BitVec.ofNat 64 56).toNat
    have : 184 ≤ (s.gpr .rsp).toNat := A.stackLower
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat]; omega_using [this])]
    simp only [BitVec.toNat_ofNat]
    omega_using [this]
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
