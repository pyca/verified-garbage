module

public import VerifiedGarbage.Impl.Sm4.Circuit
meta import VerifiedGarbage.Impl.Sm4.Circuit
public import VerifiedGarbage.Impl.Aes.Arm.Sbox
meta import VerifiedGarbage.Impl.Aes.Arm.Sbox
meta import VerifiedGarbage.Impl.Aes.Arm.Alloc

/-!
# The bitsliced SM4 S-box on ARMv7

A topological ordering of the circuit `Circuit.sbox` on the eight planes of the state (`q j` holds
bit `j` of 32 bytes: a word of eight blocks), in place: the code that the
AES allocator `compile` produces for it, with the temporaries in
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

/-- A topological ordering of the same SM4 circuit, keeping its short-lived
intermediates close to their uses to reduce register spills on ARMv7. The
S-box truth-table proof checks the resulting code against all 256 inputs. -/
def sboxCircuit : List VG.Impl.Aes.Circuit.Gate := [
  ⟨131, .xor, 4, 7⟩, ⟨136, .xor, 0, 3⟩, ⟨130, .xor, 3, 5⟩, ⟨132, .xor, 6, 131⟩,
  ⟨154, .xnor, 0, 5⟩, ⟨133, .xor, 0, 130⟩, ⟨135, .xor, 1, 5⟩, ⟨141, .xor, 2, 130⟩,
  ⟨160, .xnor, 0, 132⟩, ⟨156, .xor, 131, 141⟩, ⟨151, .xor, 132, 136⟩, ⟨150, .xnor, 4, 141⟩,
  ⟨148, .xnor, 7, 133⟩, ⟨134, .xor, 2, 132⟩, ⟨139, .xor, 0, 4⟩, ⟨140, .xor, 1, 136⟩,
  ⟨149, .xor, 6, 139⟩, ⟨157, .xnor, 2, 139⟩, ⟨153, .xor, 134, 135⟩, ⟨144, .xor, 7, 140⟩,
  ⟨159, .xnor, 130, 132⟩, ⟨155, .xnor, 6, 144⟩, ⟨137, .xor, 2, 133⟩, ⟨138, .xor, 1, 137⟩,
  ⟨143, .xor, 131, 133⟩, ⟨45, .and, 153, 133⟩, ⟨158, .xor, 6, 138⟩, ⟨142, .xnor, 6, 137⟩,
  ⟨38, .and, 135, 157⟩, ⟨146, .xor, 6, 135⟩, ⟨147, .xor, 1, 143⟩, ⟨32, .and, 158, 142⟩,
  ⟨43, .and, 138, 160⟩, ⟨42, .and, 151, 159⟩, ⟨35, .and, 147, 149⟩, ⟨37, .and, 6, 156⟩,
  ⟨46, .xor, 45, 42⟩, ⟨39, .xor, 38, 37⟩, ⟨44, .xor, 43, 42⟩, ⟨36, .xor, 35, 32⟩,
  ⟨145, .xor, 134, 140⟩, ⟨33, .and, 134, 150⟩, ⟨34, .xor, 33, 32⟩, ⟨48, .xor, 36, 46⟩,
  ⟨47, .xor, 34, 44⟩, ⟨49, .xor, 39, 44⟩, ⟨152, .xor, 130, 134⟩, ⟨52, .xor, 48, 145⟩,
  ⟨53, .xor, 49, 152⟩, ⟨51, .xor, 47, 154⟩, ⟨40, .and, 146, 148⟩, ⟨55, .xor, 51, 52⟩,
  ⟨41, .xor, 40, 37⟩, ⟨56, .and, 51, 53⟩, ⟨61, .xor, 52, 56⟩, ⟨50, .xor, 41, 46⟩,
  ⟨54, .xor, 50, 155⟩, ⟨60, .xor, 53, 54⟩, ⟨57, .xor, 54, 56⟩, ⟨62, .and, 61, 60⟩,
  ⟨63, .xor, 62, 54⟩, ⟨65, .xor, 57, 63⟩, ⟨66, .and, 54, 65⟩, ⟨58, .and, 55, 57⟩,
  ⟨68, .xor, 57, 66⟩, ⟨59, .xor, 58, 52⟩, ⟨64, .xor, 53, 63⟩, ⟨67, .xor, 66, 64⟩,
  ⟨112, .and, 59, 146⟩, ⟨69, .and, 59, 68⟩, ⟨74, .xor, 63, 67⟩, ⟨108, .and, 67, 134⟩,
  ⟨70, .xor, 55, 69⟩, ⟨107, .and, 74, 158⟩, ⟨71, .xor, 70, 67⟩, ⟨109, .and, 63, 147⟩,
  ⟨106, .and, 71, 133⟩, ⟨103, .and, 59, 148⟩, ⟨102, .and, 70, 157⟩, ⟨98, .and, 74, 142⟩,
  ⟨111, .and, 70, 135⟩, ⟨99, .and, 67, 150⟩, ⟨172, .xor, 98, 103⟩, ⟨195, .xor, 98, 99⟩,
  ⟨100, .and, 63, 149⟩, ⟨73, .xor, 59, 70⟩, ⟨72, .xor, 59, 63⟩, ⟨75, .xor, 72, 71⟩,
  ⟨115, .and, 71, 153⟩, ⟨104, .and, 72, 159⟩, ⟨171, .xor, 104, 108⟩, ⟨113, .and, 72, 151⟩,
  ⟨101, .and, 73, 156⟩, ⟨173, .xor, 111, 171⟩, ⟨174, .xor, 112, 173⟩, ⟨110, .and, 73, 6⟩,
  ⟨175, .xor, 99, 106⟩, ⟨114, .and, 75, 138⟩, ⟨187, .xor, 110, 113⟩, ⟨170, .xor, 107, 113⟩,
  ⟨178, .xor, 102, 172⟩, ⟨105, .and, 75, 160⟩, ⟨188, .xor, 171, 178⟩, ⟨181, .xor, 114, 175⟩,
  ⟨186, .xor, 111, 114⟩, ⟨176, .xor, 105, 174⟩, ⟨182, .xor, 170, 181⟩, ⟨180, .xor, 109, 178⟩,
  ⟨177, .xor, 115, 170⟩, ⟨183, .xor, 101, 172⟩, ⟨120, .xor, 109, 177⟩, ⟨189, .xor, 175, 180⟩,
  ⟨192, .xor, 100, 176⟩, ⟨184, .xor, 182, 183⟩, ⟨179, .xor, 176, 177⟩, ⟨122, .xnor, 174, 189⟩,
  ⟨119, .xnor, 182, 188⟩, ⟨191, .xor, 108, 184⟩, ⟨196, .xor, 101, 179⟩, ⟨121, .xor, 102, 196⟩,
  ⟨117, .xnor, 180, 192⟩, ⟨116, .xnor, 186, 187⟩, ⟨123, .xnor, 105, 191⟩, ⟨118, .xor, 179, 195⟩]

/-- The S-box on the state in `q 0 … q 7`, in place. -/
def sboxCode : List Instr := [
  .mov .r10 (.imm 0), .dp .sub .r10 .r10 (.imm 1), stS 0 .r10,
  eorR .r10 .r3 .r0, eorR .r11 .r7 .r4, eorR .r4 .r4 .r2,
  eorR .r12 .r1 .r10, eorR .lr .r7 .r2, stS 1 .r1,
  ldS .r1 0, eorR .lr .lr .r1, stS 2 .lr,
  eorR .lr .r7 .r4, eorR .r2 .r6 .r2, stS 3 .r2,
  eorR .r2 .r5 .r4, stS 4 .r4, eorR .r4 .r7 .r12,
  eorR .r4 .r4 .r1, stS 5 .r4, eorR .r4 .r10 .r2,
  stS 6 .r4, eorR .r4 .r12 .r11, eorR .r2 .r3 .r2,
  eorR .r2 .r2 .r1, stS 7 .r2, eorR .r2 .r0 .lr,
  eorR .r2 .r2 .r1, stS 8 .r2, eorR .r2 .r5 .r12,
  eorR .r7 .r7 .r3, eorR .r11 .r6 .r11, ldS .r3 1,
  stS 9 .r4, eorR .r4 .r3 .r7, eorR .r7 .r5 .r7,
  eorR .r7 .r7 .r1, stS 10 .r4, ldS .r4 3,
  stS 11 .r7, eorR .r7 .r2 .r4, eorR .r0 .r0 .r11,
  stS 12 .r11, ldS .r11 4, eorR .r12 .r11 .r12,
  eorR .r12 .r12 .r1, eorR .r0 .r3 .r0, eorR .r0 .r0 .r1,
  eorR .r5 .r5 .lr, stS 13 .r0, eorR .r0 .r6 .r5,
  eorR .r10 .r10 .lr, andR .r11 .r7 .lr, stS 14 .r7,
  eorR .r7 .r3 .r0, eorR .r5 .r3 .r5, eorR .r5 .r5 .r1,
  ldS .r1 11, stS 15 .lr, andR .lr .r4 .r1,
  eorR .r1 .r3 .r4, eorR .r6 .r6 .r10, andR .r10 .r7 .r5,
  ldS .r4 5, stS 16 .r5, andR .r5 .r0 .r4,
  ldS .r4 9, stS 17 .r0, andR .r0 .r4 .r12,
  ldS .r4 10, stS 18 .r12, andR .r12 .r6 .r4,
  ldS .r4 6, stS 19 .r6, andR .r6 .r3 .r4,
  eorR .r11 .r11 .r0, eorR .lr .lr .r6, eorR .r5 .r5 .r0,
  eorR .r12 .r12 .r10, ldS .r0 12, eorR .r0 .r2 .r0,
  ldS .r3 7, andR .r4 .r2 .r3, eorR .r4 .r4 .r10,
  eorR .r12 .r12 .r11, eorR .r4 .r4 .r5, eorR .lr .lr .r5,
  ldS .r5 4, eorR .r5 .r5 .r2, eorR .r12 .r12 .r0,
  eorR .lr .lr .r5, ldS .r5 2, eorR .r4 .r4 .r5,
  ldS .r5 8, andR .r0 .r1 .r5, eorR .r10 .r4 .r12,
  eorR .r0 .r0 .r6, andR .r4 .r4 .lr, eorR .r6 .r12 .r4,
  eorR .r0 .r0 .r11, ldS .r11 13, eorR .r0 .r0 .r11,
  eorR .r11 .lr .r0, eorR .r4 .r0 .r4, andR .r6 .r6 .r11,
  eorR .r6 .r6 .r0, eorR .r11 .r4 .r6, andR .r0 .r0 .r11,
  andR .r11 .r10 .r4, eorR .r4 .r4 .r0, eorR .r11 .r11 .r12,
  eorR .lr .lr .r6, eorR .r0 .r0 .lr, andR .r1 .r11 .r1,
  andR .r4 .r11 .r4, eorR .lr .r6 .r0, andR .r2 .r0 .r2,
  eorR .r10 .r10 .r4, andR .r7 .lr .r7, eorR .r4 .r10 .r0,
  ldS .r12 19, andR .r12 .r6 .r12, stS 19 .r12,
  ldS .r12 15, andR .r12 .r4 .r12, andR .r5 .r11 .r5,
  stS 8 .r7, ldS .r7 11, andR .r7 .r10 .r7,
  stS 11 .r7, ldS .r7 16, andR .lr .lr .r7,
  ldS .r7 3, andR .r7 .r10 .r7, andR .r0 .r0 .r3,
  eorR .r5 .lr .r5, eorR .lr .lr .r0, ldS .r3 10,
  andR .r3 .r6 .r3, eorR .r10 .r11 .r10, eorR .r11 .r11 .r6,
  eorR .r6 .r11 .r4, stS 10 .lr, ldS .lr 14,
  andR .r4 .r4 .lr, ldS .lr 18, andR .lr .r11 .lr,
  eorR .lr .lr .r2, stS 18 .r2, ldS .r2 9,
  andR .r11 .r11 .r2, ldS .r2 6, andR .r2 .r10 .r2,
  stS 6 .r3, eorR .r3 .r7 .lr, eorR .r1 .r1 .r3,
  ldS .r3 1, andR .r10 .r10 .r3, eorR .r0 .r0 .r12,
  ldS .r12 17, andR .r12 .r6 .r12, eorR .r10 .r10 .r11,
  ldS .r3 8, eorR .r3 .r3 .r11, ldS .r11 11,
  stS 8 .r10, eorR .r10 .r11 .r5, ldS .r11 5,
  andR .r6 .r6 .r11, eorR .lr .lr .r10, eorR .r11 .r12 .r0,
  eorR .r7 .r7 .r12, eorR .r12 .r6 .r1, eorR .r11 .r3 .r11,
  stS 5 .r6, ldS .r6 19, eorR .r10 .r6 .r10,
  eorR .r4 .r4 .r3, eorR .r5 .r2 .r5, eorR .r3 .r6 .r4,
  eorR .r0 .r0 .r10, ldS .r6 6, eorR .r6 .r6 .r12,
  eorR .r5 .r11 .r5, eorR .r12 .r12 .r4, eorR .r1 .r1 .r0,
  ldS .r0 0, eorR .r1 .r1 .r0, eorR .r11 .r11 .lr,
  eorR .r4 .r11 .r0, ldS .r11 18, eorR .r11 .r11 .r5,
  eorR .r2 .r2 .r12, ldS .r5 11, eorR .r2 .r5 .r2,
  eorR .r10 .r10 .r6, eorR .r6 .r10 .r0, ldS .r10 8,
  eorR .r7 .r7 .r10, eorR .r7 .r7 .r0, ldS .r10 5,
  eorR .r10 .r10 .r11, eorR .r0 .r10 .r0, ldS .r10 10,
  eorR .r5 .r12 .r10]
#guard sboxCode == compile sb sboxCircuit sboxIns sboxOuts sboxFree onesSlot onesVar freshVar
  spillSlots

end VG.Impl.Sm4.Arm
