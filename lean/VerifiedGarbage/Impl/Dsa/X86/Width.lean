module

public import VerifiedGarbage.Impl.Dsa.X86.Checks

/-! # Exact bit-length masks, including leading-zero padded components -/

@[expose] public section
namespace VG.Impl.Dsa.X86
open VG VG.X86 VG.Impl.Mont.X86.Dynamic

def lessThanConstant (n a tmp value : Nat) : Prog isa :=
  .seq (setConstW (2 * n) tmp value) (lessThan n a tmp)

/-- Return edx = all ones precisely on the interval [2^(bits-1), 2^bits).
For a full-width value the upper bound follows from its storage width. -/
def widthMask (n a tmp bits : Nat) : Prog isa :=
  .seq (lessThanConstant n a tmp (2 ^ (bits - 1))) <|
  .seq (.block [.alu .xor .eax (.imm (BitVec.allOnes 32)), .mov .ebx (.reg .eax)])
  (if bits < 64 * n then
    .seq (lessThanConstant n a tmp (2 ^ bits)) (.block [.alu .and .eax (.reg .ebx), .mov .edx (.reg .eax)])
   else .block [.mov .edx (.reg .ebx)])

/-- A supported width larger than this buffer cannot match. -/
def optionalWidth (n a tmp bits : Nat) : Prog isa :=
  if bits ≤ 64 * n then widthMask n a tmp bits else .block [.mov .edx (.imm 0)]

end VG.Impl.Dsa.X86
