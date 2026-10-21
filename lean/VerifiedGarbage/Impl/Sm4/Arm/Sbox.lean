module

public import VerifiedGarbage.Impl.Sm4.Circuit
meta import VerifiedGarbage.Impl.Sm4.Circuit
public import VerifiedGarbage.Impl.Aes.Arm.Sbox
meta import VerifiedGarbage.Impl.Aes.Arm.Sbox
meta import VerifiedGarbage.Impl.Sm4.Arm.Alloc
import VerifiedGarbage.Impl.Sm4.Arm.Alloc
public import VerifiedGarbage.Impl.Aes.Circuit
meta import VerifiedGarbage.Impl.Aes.Circuit
public import VerifiedGarbage.TCB.Arm.Isa
meta import VerifiedGarbage.TCB.Arm.Isa

/-!
# The bitsliced SM4 S-box on ARMv7

A complemented form of `Circuit.sbox` on the eight planes of the state
(`q j` holds bit `j` of 32 bytes: a word of eight blocks), in place: the
code that `compileOr` produces using the AES register allocator, with the temporaries in
`r10`–`r12` and `lr`, all ones in slot 0 of the scratch buffer at `r8`,
and spilling to its next slots. It is written out (and `#guard` checks
that it is what `compile` produces) so that the kernel, which evaluates
the code in the proofs, does not have to run the allocator.
-/

@[expose] public section

namespace VG.Impl.Sm4.Arm

open VG.Arm VG.Impl.Aes.Arm

/-- The circuit's input `xᵢ` and output `sᵢ` are bit `7 - i`, in `q (7 - i)`. -/
def sboxIns : List (Nat × Reg) := (List.range 8).map fun i => (VG.Impl.Sm4.Circuit.x i, q (7 - i))
def sboxOuts : List (Nat × Reg) := (List.range 8).map fun i => (VG.Impl.Sm4.Circuit.s i, q (7 - i))

/-- The variables `compile` uses for all ones and for the gates it splits,
above the circuit's own. -/
def onesVar : Nat := 200
def freshVar : Nat := 201

/-- A complemented representation of intermediate circuit values. OR gates
implement De Morgan's law, reducing explicit inversions. Exhaustive kernel
checking verifies the generated instructions against all 256 S-box inputs. -/
def sboxCircuit : List VG.Impl.Aes.Circuit.Gate := [
  ⟨131, .xor, 4, 7⟩, ⟨132, .xor, 6, 131⟩, ⟨130, .xor, 3, 5⟩, ⟨136, .xor, 0, 3⟩,
  ⟨139, .xnor, 0, 4⟩, ⟨151, .xor, 132, 136⟩, ⟨140, .xor, 1, 136⟩, ⟨154, .xor, 0, 5⟩,
  ⟨133, .xnor, 0, 130⟩, ⟨160, .xor, 0, 132⟩, ⟨141, .xor, 2, 130⟩, ⟨135, .xor, 1, 5⟩,
  ⟨150, .xor, 4, 141⟩, ⟨134, .xnor, 2, 132⟩, ⟨159, .xnor, 130, 132⟩, ⟨152, .xor, 130, 134⟩,
  ⟨137, .xor, 2, 133⟩, ⟨42, .and, 151, 159⟩, ⟨138, .xor, 1, 137⟩, ⟨143, .xor, 131, 133⟩,
  ⟨157, .xor, 2, 139⟩, ⟨156, .xor, 131, 141⟩, ⟨38, .and, 135, 157⟩, ⟨158, .xor, 6, 138⟩,
  ⟨142, .xnor, 6, 137⟩, ⟨32, .and, 158, 142⟩, ⟨153, .xor, 134, 135⟩, ⟨146, .xor, 6, 135⟩,
  ⟨147, .xor, 1, 143⟩, ⟨45, .and, 153, 133⟩, ⟨37, .and, 6, 156⟩, ⟨33, .and, 134, 150⟩,
  ⟨149, .xor, 6, 139⟩, ⟨145, .xor, 134, 140⟩, ⟨43, .and, 138, 160⟩, ⟨35, .and, 147, 149⟩,
  ⟨36, .xor, 35, 32⟩, ⟨34, .xor, 33, 32⟩, ⟨39, .xor, 38, 37⟩, ⟨144, .xor, 7, 140⟩,
  ⟨148, .xor, 7, 133⟩, ⟨44, .xor, 43, 42⟩, ⟨49, .xor, 39, 44⟩, ⟨46, .xor, 45, 42⟩,
  ⟨53, .xor, 49, 152⟩, ⟨40, .and, 146, 148⟩, ⟨47, .xor, 34, 44⟩, ⟨48, .xor, 36, 46⟩,
  ⟨52, .xor, 48, 145⟩, ⟨51, .xor, 47, 154⟩, ⟨41, .xor, 40, 37⟩, ⟨155, .xor, 6, 144⟩,
  ⟨50, .xor, 41, 46⟩, ⟨56, .and, 51, 53⟩, ⟨54, .xor, 50, 155⟩, ⟨55, .xor, 51, 52⟩,
  ⟨60, .xor, 53, 54⟩, ⟨61, .xor, 52, 56⟩, ⟨57, .xor, 54, 56⟩, ⟨62, .and, 61, 60⟩,
  ⟨63, .xor, 62, 54⟩, ⟨58, .and, 55, 57⟩, ⟨65, .xor, 57, 63⟩, ⟨66, .and, 54, 65⟩,
  ⟨59, .xor, 58, 52⟩, ⟨64, .xor, 53, 63⟩, ⟨68, .xor, 57, 66⟩, ⟨300, .xor, 147, 200⟩,
  ⟨109, .and, 63, 300⟩, ⟨69, .and, 59, 68⟩, ⟨70, .xor, 55, 69⟩, ⟨301, .xor, 63, 200⟩,
  ⟨100, .and, 301, 149⟩, ⟨67, .xnor, 66, 64⟩, ⟨72, .xor, 59, 63⟩, ⟨74, .xor, 63, 67⟩,
  ⟨73, .xor, 59, 70⟩, ⟨98, .and, 74, 142⟩, ⟨103, .and, 59, 148⟩, ⟨107, .and, 74, 158⟩,
  ⟨108, .and, 67, 134⟩, ⟨99, .and, 67, 150⟩, ⟨104, .and, 72, 159⟩, ⟨112, .and, 59, 146⟩,
  ⟨195, .xor, 98, 99⟩, ⟨171, .xor, 104, 108⟩, ⟨111, .and, 70, 135⟩, ⟨71, .xor, 70, 67⟩,
  ⟨173, .xor, 111, 171⟩, ⟨115, .and, 71, 153⟩, ⟨174, .xor, 112, 173⟩, ⟨172, .xor, 98, 103⟩,
  ⟨102, .and, 70, 157⟩, ⟨106, .and, 71, 133⟩, ⟨113, .and, 72, 151⟩, ⟨75, .xor, 72, 71⟩,
  ⟨110, .and, 73, 6⟩, ⟨187, .xor, 110, 113⟩, ⟨170, .xor, 107, 113⟩, ⟨175, .xor, 99, 106⟩,
  ⟨178, .xnor, 102, 172⟩, ⟨177, .xor, 115, 170⟩, ⟨114, .and, 75, 138⟩, ⟨105, .and, 75, 160⟩,
  ⟨181, .xor, 114, 175⟩, ⟨182, .xor, 170, 181⟩, ⟨186, .xor, 111, 114⟩, ⟨101, .and, 73, 156⟩,
  ⟨180, .xor, 109, 178⟩, ⟨183, .xor, 101, 172⟩, ⟨176, .xor, 105, 174⟩, ⟨189, .xor, 175, 180⟩,
  ⟨116, .xor, 186, 187⟩, ⟨184, .xor, 182, 183⟩, ⟨188, .xor, 171, 178⟩, ⟨119, .xor, 182, 188⟩,
  ⟨122, .xor, 174, 189⟩, ⟨192, .xor, 100, 176⟩, ⟨191, .xor, 108, 184⟩, ⟨179, .xor, 176, 177⟩,
  ⟨117, .xor, 180, 192⟩, ⟨118, .xor, 179, 195⟩, ⟨196, .xor, 101, 179⟩, ⟨120, .xor, 109, 177⟩,
  ⟨121, .xor, 102, 196⟩, ⟨123, .xor, 105, 191⟩]

def sboxOrs : List Nat := [32, 45, 33, 43, 35, 100, 98, 107, 108, 99, 115, 106, 114, 105]

/-- The S-box on the state in `q 0 … q 7`, in place. -/
def sboxCode : List Instr := [
  .mov .r10 (.imm 0), .dp .sub .r10 .r10 (.imm 1), stS 0 .r10,
  eorR .r10 .r3 .r0, eorR .r11 .r1 .r10, eorR .r12 .r4 .r2,
  eorR .r4 .r7 .r4, eorR .lr .r7 .r3, stS 1 .r0,
  ldS .r0 0, eorR .lr .lr .r0, stS 2 .r1,
  eorR .r1 .r11 .r4, eorR .r4 .r6 .r4, stS 3 .r4,
  eorR .r4 .r7 .r2, stS 4 .r4, eorR .r4 .r7 .r12,
  eorR .r4 .r4 .r0, eorR .r7 .r7 .r11, stS 5 .r7,
  eorR .r7 .r5 .r12, eorR .r2 .r6 .r2, eorR .r3 .r3 .r7,
  stS 6 .r3, eorR .r3 .r5 .r11, eorR .r3 .r3 .r0,
  eorR .r11 .r12 .r11, eorR .r11 .r11 .r0, eorR .r12 .r12 .r3,
  stS 7 .r12, eorR .r12 .r5 .r4, stS 8 .r3,
  andR .r3 .r1 .r11, stS 9 .r1, eorR .r1 .r6 .r12,
  stS 10 .r11, eorR .r11 .r10 .r4, eorR .r5 .r5 .lr,
  eorR .r10 .r10 .r7, andR .r7 .r2 .r5, stS 11 .r5,
  ldS .r5 2, stS 12 .r3, eorR .r3 .r5 .r1,
  eorR .r12 .r5 .r12, eorR .r12 .r12 .r0, .dp .orr .r0 .r3 (.reg .r12),
  stS 13 .r3, ldS .r3 8, stS 14 .r12,
  eorR .r12 .r3 .r2, stS 15 .r7, eorR .r7 .r5 .r2,
  eorR .r6 .r6 .r11, .dp .orr .r11 .r12 (.reg .r4), stS 16 .r12,
  andR .r12 .r5 .r10, stS 17 .r10, ldS .r10 6,
  stS 18 .r2, .dp .orr .r2 .r3 (.reg .r10), eorR .lr .r5 .lr,
  ldS .r10 3, eorR .r5 .r3 .r10, ldS .r3 5,
  stS 19 .r5, .dp .orr .r5 .r1 (.reg .r3), .dp .orr .r3 .r6 (.reg .lr),
  eorR .r3 .r3 .r0, eorR .r2 .r2 .r0, ldS .r0 15,
  eorR .r0 .r0 .r12, stS 15 .r1, ldS .r1 1,
  eorR .r10 .r1 .r10, eorR .r1 .r1 .r4, stS 1 .r4,
  ldS .r4 12, eorR .r5 .r5 .r4, eorR .r0 .r0 .r5,
  eorR .r11 .r11 .r4, ldS .r4 7, eorR .r0 .r0 .r4,
  andR .r4 .r7 .r1, eorR .r2 .r2 .r5, eorR .r3 .r3 .r11,
  ldS .r5 19, eorR .r3 .r3 .r5, ldS .r5 4,
  eorR .r2 .r2 .r5, eorR .r4 .r4 .r12, ldS .r12 2,
  eorR .r10 .r12 .r10, eorR .r4 .r4 .r11, andR .r11 .r2 .r0,
  eorR .r4 .r4 .r10, eorR .r2 .r2 .r3, eorR .r10 .r0 .r4,
  eorR .r5 .r3 .r11, eorR .r11 .r4 .r11, andR .r5 .r5 .r10,
  eorR .r5 .r5 .r4, andR .r10 .r2 .r11, eorR .r12 .r11 .r5,
  andR .r4 .r4 .r12, eorR .r10 .r10 .r3, eorR .r0 .r0 .r5,
  eorR .r11 .r11 .r4, ldS .r3 0, eorR .r6 .r6 .r3,
  andR .r6 .r5 .r6, andR .r11 .r10 .r11, eorR .r2 .r2 .r11,
  eorR .r11 .r5 .r3, .dp .orr .r11 .r11 (.reg .lr), eorR .r4 .r4 .r0,
  eorR .r4 .r4 .r3, eorR .r0 .r10 .r5, eorR .r5 .r5 .r4,
  eorR .lr .r10 .r2, ldS .r12 14, .dp .orr .r12 .r5 (.reg .r12),
  andR .r1 .r10 .r1, stS 14 .r11, ldS .r11 13,
  .dp .orr .r5 .r5 (.reg .r11), ldS .r11 8, .dp .orr .r11 .r4 (.reg .r11),
  stS 8 .r6, ldS .r6 6, .dp .orr .r6 .r4 (.reg .r6),
  ldS .r3 10, andR .r3 .r0 .r3, andR .r10 .r10 .r7,
  eorR .r7 .r12 .r6, eorR .r3 .r3 .r11, stS 10 .r7,
  ldS .r7 18, andR .r7 .r2 .r7, eorR .r4 .r2 .r4,
  stS 18 .r11, eorR .r11 .r7 .r3, stS 6 .r3,
  ldS .r3 16, .dp .orr .r3 .r4 (.reg .r3), eorR .r10 .r10 .r11,
  eorR .r12 .r12 .r1, ldS .r1 11, andR .r2 .r2 .r1,
  ldS .r1 1, .dp .orr .r1 .r4 (.reg .r1), ldS .r11 9,
  andR .r11 .r0 .r11, eorR .r0 .r0 .r4, ldS .r4 2,
  andR .r4 .lr .r4, eorR .r4 .r4 .r11, eorR .r5 .r5 .r11,
  eorR .r6 .r6 .r1, eorR .r1 .r2 .r12, ldS .r11 0,
  eorR .r1 .r1 .r11, eorR .r3 .r3 .r5, ldS .r11 15,
  .dp .orr .r11 .r0 (.reg .r11), stS 15 .r2, ldS .r2 5,
  .dp .orr .r0 .r0 (.reg .r2), eorR .r2 .r11 .r6, eorR .r5 .r5 .r2,
  eorR .r7 .r7 .r11, ldS .r11 17, andR .lr .lr .r11,
  ldS .r11 8, eorR .r2 .r11 .r1, eorR .r12 .lr .r12,
  eorR .r11 .r0 .r10, eorR .r6 .r6 .r2, eorR .r7 .r7 .r4,
  eorR .r12 .r5 .r12, ldS .r4 6, eorR .r4 .r4 .r1,
  eorR .r4 .r5 .r4, eorR .r1 .r10 .r6, ldS .r6 14,
  eorR .r6 .r6 .r11, ldS .r10 18, eorR .r10 .r10 .r12,
  eorR .r11 .r11 .r3, eorR .r6 .r2 .r6, ldS .r2 10,
  eorR .r5 .r11 .r2, eorR .lr .lr .r11, ldS .r11 8,
  eorR .r3 .r11 .r3, ldS .r11 15, eorR .r2 .r11 .lr,
  eorR .r0 .r0 .r10]
#guard sboxCode == compileOr sb sboxCircuit sboxOrs sboxIns sboxOuts sboxFree onesSlot onesVar freshVar
  spillSlots

end VG.Impl.Sm4.Arm
