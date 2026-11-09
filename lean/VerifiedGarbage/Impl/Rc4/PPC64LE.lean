module

public import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# RC4 on PPC64LE

The 256-byte table at `r3` is read and written only at fixed addresses, a
vector (16 bytes) or two at a time. A secret-indexed lookup reads the table
32 bytes at a time (`lxvd2x`); in each chunk `vperm` picks the byte at the
index mod 32 (control byte `index XOR 7`, as `lxvd2x` numbers the bytes it
loads `XOR 7`), and a tree of `vsel` by masks of the index's bits 5, 6 and 7
picks the chunk. A secret-indexed replacement XORs into each of the 16
vectors of the table, in turn, the byte's difference masked to the byte's
lane (`vperm` of a one-hot vector by the identity permutation plus a splat,
which rotates it) and to the vector that holds it (byte `k` of a one-hot
vector at the index's vector, splat by `vperm`), and stores it back. Only
the addresses, the PRGA index `i`, the key offset, the pointers and the
lengths are public; the secret indices are only operands of the masks'
arithmetic and of `vperm`, whose time does not depend on its operands.

Registers: the table at `r3`, the public index `i` in `r6`, the secret
index of a lookup or replacement in `r9`, its result in `r10`, zero in `r8`;
`r0`, `r11` and `r12` are scratch, with `v0`–`v19`. Initialization keeps the
key at `r7`, its length in `r4`, the key offset in `r5` and `j` in `r9`; the
stream function keeps the data at `r4`, the remaining length in `r5` and `j`
in `r7`. Only volatile registers are used, and no stack.
-/

@[expose] public section

namespace VG.Impl.Rc4.PPC64LE

open VG.PPC64LE

/-! ## Lookups -/

/-- The lookup's vectors: the control, the masks of bits 5, 6 and 7, a
chunk's halves and each chunk's pick. -/
def vCtl : VReg := .v0
def vBit : Nat → VReg
  | 5 => .v1 | 6 => .v2 | _ => .v3
def vLo : VReg := .v4
def vHi : VReg := .v5
def vPick : Nat → VReg
  | 0 => .v6 | 1 => .v7 | 2 => .v8 | 3 => .v9 | 4 => .v10 | 5 => .v11 | 6 => .v12 | _ => .v13

def vperm (d n m c : VReg) : Instr := .vop (.perm d n m c)

/-- The mask of bit `b` of the index: all ones if it is set, else zero, in
the first doubleword. -/
def bitMask (b : Nat) : List Instr :=
  [.lsl .r12 .r9 (63 - b), .lsr .d .r12 .r12 63, .sub .r12 .r8 .r12, .mtvsrd (vBit b) .r12]

/-- Chunk `i`'s pick, and `r11` to the next chunk. -/
def chunk (i : Nat) : List Instr :=
  [.lxvd2x vLo .r11 .r8, .lxvd2x vHi .r11 .r12, vperm (vPick i) vLo vHi vCtl, .addi .r11 .r11 32]

/-- `vPick d` := `vPick d` or `vPick n`, as bit `b` of the index says. -/
def choose (b d n : Nat) : Instr := .vop (.sel (vPick d) (vPick d) (vPick n) (vBit b))

/-- The byte of the table at `r3` indexed by `r9` (below 256), into `r10`.
Clobbers `r0`, `r11` and `r12`. -/
def lookup : List Instr :=
  [.li .r0 7, .logic .xor .r12 .r9 .r0, .lsl .r12 .r12 56, .mtvsrd vCtl .r12] ++
  bitMask 5 ++ bitMask 6 ++ bitMask 7 ++ [.li .r12 16, .logic .or .r11 .r3 .r3] ++
  chunk 0 ++ chunk 1 ++ chunk 2 ++ chunk 3 ++ chunk 4 ++ chunk 5 ++ chunk 6 ++ chunk 7 ++
  [choose 5 0 1, choose 5 2 3, choose 6 0 2, choose 5 4 5, choose 5 6 7, choose 6 4 6, choose 7 0 4,
   .mfvsrd .r10 (vPick 0), .lsr .d .r10 .r10 56]

/-! ## Replacements -/

/-- The replacement's vectors: zero; the difference in every byte; the
one-hot vector of byte 0 (rotated to the difference's lane, then masked to
the difference, in `vLane`; and rotated to the index's vector, in `vHot`);
a rotation's mask and the rotated vector; a table vector's mask; and the
table vector. -/
def vZ : VReg := .v14
def vDiff : VReg := .v15
def vLane : VReg := .v0
def vHot : VReg := .v1
def vRotM : VReg := .v2
def vRot : VReg := .v3
def vMask : VReg := .v4
def vS : VReg := .v5

/-- `v := 0xFF` in byte 0 and zero elsewhere. -/
def oneHot0 (v : VReg) : List Instr :=
  [.li .r12 255, .lsl .r12 .r12 56, .mtvsrd v .r12, .vop (.sldoi v vZ v 8), .vop (.sldoi v v vZ 8)]

/-- `v` rotated left by `2 ^ b` bytes if bit `b` of `r0` is set. -/
def rotStep (v : VReg) (b : Nat) : List Instr :=
  [.lsl .r12 .r0 (63 - b), .lsr .d .r12 .r12 63, .sub .r12 .r8 .r12, .mtvsrd vRotM .r12,
   vperm vRotM vRotM vRotM vZ, .vop (.sldoi vRot v v (2 ^ b)), .vop (.sel v v vRot vRotM)]

/-- `v` := the one-hot vector of byte `(16 - r0) mod 16`: byte 0's, rotated
left by `r0` (below 16). -/
def oneHot (v : VReg) : List Instr :=
  oneHot0 v ++ rotStep v 0 ++ rotStep v 1 ++ rotStep v 2 ++ rotStep v 3

/-- The difference in every byte, and `r0` := the lane's rotation. -/
def laneStart : List Instr :=
  [.vop (.logic .xor vZ vZ vZ), .lsl .r0 .r0 56, .mtvsrd vDiff .r0, vperm vDiff vDiff vDiff vZ,
   .lsl .r0 .r9 60, .lsr .d .r0 .r0 60, .li .r12 7, .logic .xor .r0 .r0 .r12, .sub .r0 .r8 .r0,
   .lsl .r0 .r0 60, .lsr .d .r0 .r0 60]

/-- The lane masked to the difference, and `r0` := the vector's rotation. -/
def vecStart : List Instr :=
  [.vop (.logic .and vLane vLane vDiff), .lsr .d .r0 .r9 4, .sub .r0 .r8 .r0, .lsl .r0 .r0 60,
   .lsr .d .r0 .r0 60]

/-- The masks of a replacement whose difference is in `r0`: the difference
in its lane, byte `(index mod 16) XOR 7` (rotation `(16 - lane) mod 16`), and
the one-hot vector of the index's vector, `index >> 4` (rotation
`(16 - index >> 4) mod 16`). -/
def replaceStart : List Instr :=
  laneStart ++ oneHot vLane ++ vecStart ++ oneHot vHot ++ [.logic .or .r11 .r3 .r3]

/-- Vector `k` of the table, at `r11`: the difference XORed into its lane
if `k` is the index's vector (byte `k` of `vHot`, now rotated to byte 0), and
on to the next. -/
def scatterStep : List Instr :=
  [vperm vMask vHot vHot vZ, .vop (.sldoi vHot vHot vHot 1), .vop (.logic .and vMask vLane vMask),
   .lxvd2x vS .r11 .r8, .vop (.logic .xor vS vS vMask), .stxvd2x vS .r11 .r8, .addi .r11 .r11 16]

/-- `r0` := the byte at the public index `r6` of the table, through `r12`. -/
def loadI : List Instr := [.add .r12 .r3 .r6, .lbz .r0 .r12 0]

/-- Replace the byte of the table at `r3` indexed by `r9` with the byte at
the public index `r6`, returning its original value in `r10`. Clobbers
`r0`, `r11` and `r12`. -/
def replace : List Instr :=
  lookup ++ loadI ++ [.logic .xor .r0 .r0 .r10] ++ replaceStart ++
    (List.range 16).flatMap fun _ => scatterStep

/-- Store the identity permutation, a byte at a time; `r12 := i - 256`. -/
def identityStep : List Instr :=
  [.add .r12 .r3 .r6, .stb .r6 .r12 0, .addi .r6 .r6 1, .li .r12 256, .sub .r12 .r6 .r12]

/-- `j += S[i] + key[off]`, the swap, then the next key offset (0 at the key
length, without a branch) and `i`; `r12 := i - 256`. -/
def scheduleStep : List Instr :=
  loadI ++ ([.add .r9 .r9 .r0, .add .r12 .r7 .r5, .lbz .r0 .r12 0, .add .r9 .r9 .r0,
    .lsl .r9 .r9 56, .lsr .d .r9 .r9 56] : List Instr) ++ replace ++
    ([.add .r12 .r3 .r6, .stb .r10 .r12 0,
      .addi .r5 .r5 1, .sub .r12 .r5 .r4, .subi .r0 .r12 1, .logic .xor .r0 .r0 .r12,
      .lsr .d .r12 .r0 63, .subi .r12 .r12 1, .logic .and .r5 .r5 .r12,
      .addi .r6 .r6 1, .li .r12 256, .sub .r12 .r6 .r12] : List Instr)

/-- Key scheduling after the key-length check: the key to `r7`, the context
to `r3`. -/
def initValid : Prog isa :=
  .seq (.block [.logic .or .r7 .r3 .r3, .logic .or .r3 .r5 .r5, .li .r6 0])
    (.seq (.loop (.block identityStep) (.nonzero .d .r12))
      (.seq (.block [.li .r6 0, .li .r5 0, .li .r9 0, .li .r8 0])
        (.seq (.loop (.block scheduleStep) (.nonzero .d .r12))
          (.block [.li .r12 0, .stb .r12 .r3 256, .stb .r12 .r3 257, .li .r3 0]))))

/-- Checked key scheduling: `(key_len - 1) >> 8` is zero exactly for
`key_len` in 1..=256; invalid lengths return 1, valid lengths 0. -/
def init : Prog isa :=
  .seq (.block [.subi .r12 .r4 1, .lsr .d .r12 .r12 8])
    (.ite (.nonzero .d .r12) (.block [.li .r3 1]) initValid)

/-- One PRGA step: `i += 1`, `j += S[i]`, the swap, then the keystream byte
`S[S[i] + S[j]]` XORed into the next data byte. -/
def applyStep : List Instr :=
  ([.addi .r6 .r6 1, .lsl .r6 .r6 56, .lsr .d .r6 .r6 56] : List Instr) ++ loadI ++
    ([.add .r7 .r7 .r0, .lsl .r7 .r7 56, .lsr .d .r7 .r7 56, .logic .or .r9 .r7 .r7] :
      List Instr) ++ replace ++ loadI ++
    ([.stb .r10 .r12 0, .add .r9 .r10 .r0, .lsl .r9 .r9 56, .lsr .d .r9 .r9 56] : List Instr) ++
    lookup ++
    ([.lbz .r0 .r4 0, .logic .xor .r0 .r0 .r10, .stb .r0 .r4 0, .addi .r4 .r4 1,
      .subi .r5 .r5 1] : List Instr)

/-- Streaming XOR, preserving the permutation and both PRGA indices. The
indices are loaded first. -/
def apply : Prog isa :=
  .seq (.block [.lbz .r6 .r3 256, .lbz .r7 .r3 257, .li .r8 0])
    (.ite (.zero .d .r5) (.block [])
      (.seq (.loop (.block applyStep) (.nonzero .d .r5))
        (.block [.stb .r6 .r3 256, .stb .r7 .r3 257])))

end VG.Impl.Rc4.PPC64LE
