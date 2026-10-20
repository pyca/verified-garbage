module
public import VerifiedGarbage.Impl.Mont.Arm.Dynamic


/-! # DSA's fixed-width big-endian components on 32-bit ARM

Every supported component width is a multiple of four bytes, so a component
is a loop over its 32-bit words, read and written through `r11` from its last
word down, byte-reversed (`rev`). `r11` points to the component.
-/

@[expose] public section
namespace VG.Impl.Dsa.Arm
open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic

/-- Clear a public, nonzero number of words starting at `r10`. -/
def zeroPadLoop (k : Nat) : Prog isa :=
  .seq (.block [.movw .r9 (BitVec.ofNat 16 (4 * k)), .dp .add .r9 .r10 (.reg .r9), .mov .r4 (.imm 0)])
    (ptrLoop .r10 [.str .r4 .r10 0, bump .r10 4])

/-- Keep short padding inline; loop over longer padding. -/
def zeroPad (k : Nat) : Prog isa :=
  if k ≤ 4 then .block ((List.range k).flatMap fun j => [.mov .r4 (.imm 0), .str .r4 .r10 (4 * j)])
  else zeroPadLoop k

/-- `[out]` (`2 n` words) = the big-endian `len` bytes at `r11`. -/
def loadComponent (len n out : Nat) : Prog isa :=
  .seq (.block ([.movw .r8 (BitVec.ofNat 16 (len - 4)), .dp .add .r8 .r11 (.reg .r8)] ++ ptr .r10 out ++
      ptr .r9 (out + len)))
  (.seq (ptrLoop .r10 [.ldr .r4 .r8 0, .rev .r4 .r4, .str .r4 .r10 0, .dp .sub .r8 .r8 (.imm 4), bump .r10 4])
    (zeroPad (2 * n - len / 4)))

/-- The big-endian `len` bytes at `r11` = `[input]` masked with `r3`. -/
def storeComponent (len input : Nat) : Prog isa :=
  .seq (.block ([.movw .r8 (BitVec.ofNat 16 (len - 4)), .dp .add .r8 .r11 (.reg .r8)] ++ ptr .r10 input ++
      ptr .r9 (input + len)))
    (ptrLoop .r10 [.ldr .r4 .r10 0, .dp .and .r4 .r4 (.reg .r3), .rev .r4 .r4, .str .r4 .r8 0,
      .dp .sub .r8 .r8 (.imm 4), bump .r10 4])

end VG.Impl.Dsa.Arm
