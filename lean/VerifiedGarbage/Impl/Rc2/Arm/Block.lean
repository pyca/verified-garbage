module

public import VerifiedGarbage.Impl.Rc2.Arm.Lookup

/-! # RC2 block encryption and decryption on baseline Arm -/

@[expose] public section

namespace VG.Impl.Rc2.Arm

open VG.Arm

def wordReg (i : Nat) : Reg := #[Reg.r4, .r5, .r6, .r7][i % 4]!

def blockSaved : List Reg := [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .lr]

def blockSave : List Instr :=
  (List.range 9).map fun i => .str (blockSaved.getD i .r4) .r2 (4 * i)

def blockRestore : List Instr :=
  (List.range 9).map fun i => .ldr (blockSaved.getD i .r4) .r2 (4 * i)

def loadWord (i : Nat) : List Instr :=
  [.ldrb (wordReg i) .r1 (2 * i), .ldrb .r12 .r1 (2 * i + 1),
   .dp .orr (wordReg i) (wordReg i) (.shifted .r12 .lsl 8)]

def blockLoad : List Instr := (List.range 4).flatMap loadWord

def rotate16 (r : Reg) (s : Nat) : List Instr :=
  [rr .r12 r, .mov .r12 (.shifted .r12 .lsr (16 - s)), .mov r (.shifted r .ror (32 - s)),
   .dp .orr r r (.reg .r12)] ++ mask r 16

def mixInputs (j i : Nat) : List Instr :=
  ([.dp .and .r10 (wordReg (i + 3)) (.reg (wordReg (i + 2))),
   imm .r11 0, .dp .sub .r11 .r11 (.reg (wordReg (i + 3))), .dp .sub .r11 .r11 (.imm 1),
   .dp .and .r11 .r11 (.reg (wordReg (i + 1))), .dp .add .r10 .r10 (.reg .r11)] : List Instr) ++ loadKey j

def addInputs (r : Reg) : List Instr :=
  ([.dp .add r r (.reg .r8), .dp .add r r (.reg .r10)] : List Instr) ++ mask r 16

def subInputs (r : Reg) : List Instr :=
  ([.dp .sub r r (.reg .r8), .dp .sub r r (.reg .r10)] : List Instr) ++ mask r 16

def adjust (sub : Bool) (r : Reg) : List Instr :=
  [if sub then .dp .sub r r (.reg .r12) else .dp .add r r (.reg .r12)] ++ mask r 16

def mix (j i : Nat) : List Instr :=
  mixInputs j i ++ addInputs (wordReg i) ++ rotate16 (wordReg i) (Spec.Rc2.rotation i)

def reverseMix (j i : Nat) : List Instr :=
  rotate16 (wordReg i) (16 - Spec.Rc2.rotation i) ++ mixInputs j i ++ subInputs (wordReg i)

def mash (direction : Spec.Rc2.Direction) (i : Nat) : Prog isa :=
  .seq (.block [rr .r12 (wordReg (i + 3))])
    (.seq keyLookup (.block (adjust (direction == .decrypt) (wordReg i))))

/-- The order of the words in a mashing round. -/
def mashOrder (direction : Spec.Rc2.Direction) : List Nat :=
  match direction with
  | .encrypt => List.range 4
  | .decrypt => [3, 2, 1, 0]

def mashRound (direction : Spec.Rc2.Direction) : Prog isa :=
  (mashOrder direction).foldr (fun i rest => .seq (mash direction i) rest) (.block [])

def mixRound (direction : Spec.Rc2.Direction) (j : Nat) : List Instr :=
  match direction with
  | .encrypt => (List.range 4).flatMap (fun i => mix (4 * j + i) i)
  | .decrypt => [3, 2, 1, 0].flatMap (fun i => reverseMix (4 * (15 - j) + i) i)

def round (direction : Spec.Rc2.Direction) (j : Nat) : Prog isa :=
  .seq (.block (mixRound direction j)) (if j = 4 ∨ j = 10 then mashRound direction else .block [])

def storeWord (i : Nat) : List Instr :=
  [.strb (wordReg i) .r1 (2 * i), .mov .r12 (.shifted (wordReg i) .lsr 8),
   .strb .r12 .r1 (2 * i + 1)]

def blockStore : List Instr := (List.range 4).flatMap storeWord

def rounds (direction : Spec.Rc2.Direction) : Prog isa :=
  (List.range 16).foldr (fun j rest => .seq (round direction j) rest) (.block [])

def blockCode (direction : Spec.Rc2.Direction) : Prog isa :=
  .seq (.block (blockSave ++ blockLoad)) (.seq (rounds direction) (.block (blockStore ++ blockRestore)))

def encryptBlock : Prog isa := blockCode .encrypt
def decryptBlock : Prog isa := blockCode .decrypt

end VG.Impl.Rc2.Arm
