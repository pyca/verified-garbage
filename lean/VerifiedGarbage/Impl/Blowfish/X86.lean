module

public import VerifiedGarbage.TCB.X86.Isa
public import VerifiedGarbage.Impl.Blowfish.Table

/-!
# Blowfish on baseline x86 (32-bit)

As on ARMv7 (`Impl/Blowfish/Arm.lean`): one block at a time, and an S-box
lookup reads every entry of the S-box's four byte planes, a row of four
entries (a word of each plane) at a time, keeping the index's byte lane of
the row that holds it under a mask made by `cmp` and `sbb`, and ORs the
masked words into one accumulator, plane `b`'s rotated left by `8b`; two
rotations selected by masks of the index's lane then give the entry. Every
address and branch is a public counter or pointer; the index is only ever an
operand of the masks' arithmetic.

Every argument is on the stack (cdecl): the schedule's address is read from
it where needed (at `esp + sch`, 4 for ECB and 12 for key expansion). The
working space `scratch` is at `ebp` throughout: our caller's `ebx`, `esi`,
`edi` and `ebp` at 0–15, the halves xL and xR at 16 and 20, F at 24, the
P-array pointer at 28, and the functions' own pointer and counter at 32 and
36. During a lookup, `esi` holds the index less four times the rows read so
far, `edi` the accumulator, `edx` the row's mask, `eax` the index's lane
mask, `ebx` the row's address and `ecx` a temporary.

`cipher sch up` is the block function: the halves at `ebp + 16` and
`ebp + 20` become their encryption (`up`) or decryption under the schedule
whose address is at `esp + sch`, changing only `eax`–`edi` but `ebp`, the
flags and the working space's bytes 16–31.

The pointer and counter stay public for the taint analysis that proves
constant time as long as nothing secret is stored at an address it cannot
follow (the data, the schedule's entries): they are read before such stores
and written after.
-/

@[expose] public section

namespace VG.Impl.Blowfish.X86

open VG.X86

/-- `[base + offset]`. -/
def at_ (base : Reg) (offset : Nat) : MemOp := { base, disp := offset }

/-- An immediate. -/
def imm (n : Nat) : Src := .imm (BitVec.ofNat 32 n)

/-- The offset of byte plane `b` of S-box `j` in the schedule. -/
def planeOff (j b : Nat) : Nat := 1024 * j + 256 * b

/-- The P-array's offset in the schedule. -/
def pOff : Nat := 4096

/-- The working space's slots. -/
def xlOff : Nat := 16
def xrOff : Nat := 20
def fOff : Nat := 24
def ppOff : Nat := 28
def ptrOff : Nat := 32
def cntOff : Nat := 36

/-! ## Lookups -/

/-- `esi` := the byte of xL that indexes S-box `j`: byte `3 - j`. -/
def index (j : Nat) : List Instr :=
  [.mov .esi (.mem (at_ .ebp xlOff))] ++
    (if j < 3 then [.shift .shr .esi (8 * (3 - j))] else []) ++ [.alu .and .esi (imm 255)]

/-- `x` rotated right by `a` if bit `c` (1 or 2) of `esi` is set: `edx` is all
ones if it is clear, and `x := ((x XOR r) AND edx) XOR r` for the rotation
`r`. -/
def condRot (x : Reg) (c a : Nat) : List Instr :=
  [.mov .edx (.reg .esi), .alu .and .edx (imm c), .alu .cmp .edx (imm 1), .alu .sbb .edx (.reg .edx),
   .mov .ecx (.reg x), .shift .ror .ecx a, .alu .xor x (.reg .ecx), .alu .and x (.reg .edx),
   .alu .xor x (.reg .ecx)]

/-- The lane mask `0xFF <<< 8L` for the index's lane `L`, the accumulator
and the row pointer. -/
def lookupStart (sch : Nat) : List Instr :=
  [.mov .eax (imm 255)] ++ condRot .eax 1 24 ++ condRot .eax 2 16 ++
    [.mov .edi (imm 0), .mov .ebx (.mem (at_ .esp sch))]

/-- Plane `b`'s word of the row, masked, into the accumulator, rotated left
by `8b`. -/
def plane (j b : Nat) : List Instr :=
  [.mov .ecx (.mem (at_ .ebx (planeOff j b))), .alu .and .ecx (.reg .edx)] ++
    (if b = 0 then [] else [.shift .ror .ecx (32 - 8 * b)]) ++ [.alu .or .edi (.reg .ecx)]

/-- One row of S-box `j`: the mask (all ones in the index's lane if
`esi < 4`), the four planes, and the next row; the flags say whether it was
the last (the schedule's address less the row's is `-256`). -/
def row (sch j : Nat) : List Instr :=
  [.alu .cmp .esi (imm 4), .alu .sbb .edx (.reg .edx), .alu .and .edx (.reg .eax), .alu .sub .esi (imm 4)] ++
    plane j 0 ++ plane j 1 ++ plane j 2 ++ plane j 3 ++
    [.alu .add .ebx (imm 4), .mov .ecx (.mem (at_ .esp sch)), .alu .sub .ecx (.reg .ebx),
     .alu .cmp .ecx (imm (2 ^ 32 - 256))]

/-- The accumulator rotated right by `8L`. -/
def lookupEnd : List Instr := condRot .edi 1 8 ++ condRot .edi 2 16

/-- S-box `j` of xL's byte `3 - j`, into the accumulator. -/
def lookup (sch j : Nat) : Prog isa :=
  .seq (.block (index j ++ lookupStart sch)) (.seq (.loop (.block (row sch j)) .ne) (.block lookupEnd))

/-- F's accumulation of S-box `j`: S₁, then + S₂, XOR S₃, + S₄. -/
def combine (j : Nat) : List Instr :=
  if j = 0 then [.store (at_ .ebp fOff) .edi]
  else [.mov .ecx (.mem (at_ .ebp fOff)), .alu (if j = 2 then .xor else .add) .ecx (.reg .edi),
    .store (at_ .ebp fOff) .ecx]

/-- F of xL into `ebp + 24`. -/
def f (sch : Nat) : Prog isa :=
  .seq (lookup sch 0) (.seq (.block (combine 0)) (.seq (lookup sch 1) (.seq (.block (combine 1))
    (.seq (lookup sch 2) (.seq (.block (combine 2)) (.seq (lookup sch 3) (.block (combine 3))))))))

/-! ## Rounds

The P-array pointer is at the P-array entry of the round (`up`, encrypting),
or four bytes below it (decrypting). -/

/-- The offset from the P-array pointer of the round's entry. -/
def pAt (up : Bool) : Nat := if up then 0 else 4

/-- `xL ^= P`, `xR ^= F(xL)`, the halves swapped, and the pointer to the
next entry; the flags say whether it is the end. -/
def round (sch : Nat) (up : Bool) : Prog isa :=
  .seq (.block [.mov .ebx (.mem (at_ .ebp ppOff)), .mov .ecx (.mem (at_ .ebx (pAt up))),
      .mov .eax (.mem (at_ .ebp xlOff)), .alu .xor .eax (.reg .ecx), .store (at_ .ebp xlOff) .eax])
    (.seq (f sch)
      (.block [.mov .eax (.mem (at_ .ebp xrOff)), .alu .xor .eax (.mem (at_ .ebp fOff)),
        .mov .ecx (.mem (at_ .ebp xlOff)), .store (at_ .ebp xrOff) .ecx, .store (at_ .ebp xlOff) .eax,
        .mov .ebx (.mem (at_ .ebp ppOff)), .alu (if up then .add else .sub) .ebx (imm 4),
        .store (at_ .ebp ppOff) .ebx, .mov .ecx (.mem (at_ .esp sch)), .alu .sub .ecx (.reg .ebx),
        .alu .cmp .ecx (imm (2 ^ 32 - if up then pOff + 64 else pOff))]))

/-- The block function: the sixteen rounds, then the last swap undone, xL
(at 20) ^= P₁₈ and xR (at 16) ^= P₁₇ when encrypting, P₁ and P₂ when
decrypting, into xL and xR. -/
def cipher (sch : Nat) (up : Bool) : Prog isa :=
  .seq (.block [.mov .ebx (.mem (at_ .esp sch)), .alu .add .ebx (imm (if up then pOff else pOff + 64)),
      .store (at_ .ebp ppOff) .ebx])
    (.seq (.loop (round sch up) .ne)
      (.block [.mov .ebx (.mem (at_ .ebp ppOff)), .mov .ecx (.mem (at_ .ebx (pAt up))),
        .alu .xor .ecx (.mem (at_ .ebp xlOff)), .mov .eax (.mem (at_ .ebx (4 - pAt up))),
        .alu .xor .eax (.mem (at_ .ebp xrOff)), .store (at_ .ebp xlOff) .eax,
        .store (at_ .ebp xrOff) .ecx]))

/-! ## Our caller's registers, in the working space -/

/-- The working space (the fourth argument) into `ebp`, our caller's `ebx`,
`esi`, `edi` and `ebp` saved in it first, through `eax`. -/
def save : List Instr :=
  [.mov .eax (.mem (at_ .esp 16)), .store (at_ .eax 0) .ebx, .store (at_ .eax 4) .esi,
   .store (at_ .eax 8) .edi, .store (at_ .eax 12) .ebp, .mov .ebp (.reg .eax)]

/-- Restore them, `ebp` last. -/
def restore : List Instr :=
  [.mov .ebx (.mem (at_ .ebp 0)), .mov .esi (.mem (at_ .ebp 4)), .mov .edi (.mem (at_ .ebp 8)),
   .mov .ebp (.mem (at_ .ebp 12))]

/-! ## ECB

`vg_blowfish_ecb_{en,de}crypt(schedule, data, n, scratch)`, all on the
stack: the data pointer and the blocks left are kept in the working space. -/

/-- The block at the data pointer into the halves, as big-endian words. -/
def loadBlock : List Instr :=
  [.mov .ebx (.mem (at_ .ebp ptrOff)), .mov .eax (.mem (at_ .ebx 0)), .bswap .eax,
   .store (at_ .ebp xlOff) .eax, .mov .eax (.mem (at_ .ebx 4)), .bswap .eax, .store (at_ .ebp xrOff) .eax]

/-- The halves to the block, the next block, and the blocks left less one;
the flags say whether none are. -/
def storeBlock : List Instr :=
  [.mov .ebx (.mem (at_ .ebp ptrOff)), .mov .edx (.mem (at_ .ebp cntOff)),
   .mov .eax (.mem (at_ .ebp xlOff)), .bswap .eax, .store (at_ .ebx 0) .eax,
   .mov .eax (.mem (at_ .ebp xrOff)), .bswap .eax, .store (at_ .ebx 4) .eax,
   .alu .add .ebx (imm 8), .store (at_ .ebp ptrOff) .ebx, .alu .sub .edx (imm 1),
   .store (at_ .ebp cntOff) .edx]

def ecb (up : Bool) : Prog isa :=
  .seq (.block (save ++ [.mov .ecx (.mem (at_ .esp 8)), .store (at_ .ebp ptrOff) .ecx,
      .mov .ecx (.mem (at_ .esp 12)), .store (at_ .ebp cntOff) .ecx, .alu .test .ecx (.reg .ecx)]))
    (.seq (.ite .e (.block [])
        (.loop (.seq (.block loadBlock) (.seq (cipher 4 up) (.block storeBlock))) .ne))
      (.block restore))

def encrypt : Prog isa := ecb true
def decrypt : Prog isa := ecb false

/-! ## Key expansion

`vg_blowfish_expand_key(key, key_len, schedule, scratch)`, all on the stack. -/

/-- Word `i` of the initial schedule's image, little-endian. -/
def initWord32 (i : Nat) : BitVec 32 :=
  (initWord (i / 2)).extractLsb' (32 * (i % 2)) 32

/-- Word `i` of the initial schedule, through `ecx`, at `ebx`. -/
def initStore (i : Nat) : List Instr :=
  [.mov .ecx (.imm (initWord32 i)), .store (at_ .ebx (4 * i)) .ecx]

def initSchedule : List Instr :=
  [.mov .ebx (.mem (at_ .esp 12)), .alu .add .ebx (imm 0)] ++ (List.range 1042).flatMap initStore

/-- The next key byte into the low byte of `edx` (rotated up a byte, which
moves only zeros while the word has three bytes or fewer), cycling: the
byte at `key + esi`, then `esi := esi + 1`, or 0 at `key_len`. -/
def keyByte : Prog isa :=
  .seq (.block [.mov .eax (.mem (at_ .esp 4)), .alu .add .eax (.reg .esi), .movzx8 .ecx (at_ .eax 0),
      .shift .ror .edx 24, .alu .or .edx (.reg .ecx), .alu .add .esi (imm 1), .mov .eax (.mem (at_ .esp 8)),
      .alu .cmp .esi (.reg .eax)])
    (.ite .e (.block [.mov .esi (imm 0)]) (.block []))

/-- The P-array entry at `ebx + 4096` XORed with the next 32 bits of the
key; the next entry, and the entries left in `edi`. -/
def keyWord : Prog isa :=
  .seq (.block [.mov .edx (imm 0)])
    (.seq keyByte (.seq keyByte (.seq keyByte (.seq keyByte
      (.block [.mov .eax (.mem (at_ .ebx pOff)), .alu .xor .eax (.reg .edx), .store (at_ .ebx pOff) .eax,
        .alu .add .ebx (imm 4), .alu .sub .edi (imm 1)])))))

/-- Pᵢ ^= the next 32 bits of the key, for the 18 entries. -/
def keyP : Prog isa :=
  .seq (.block [.mov .esi (imm 0), .mov .ebx (.mem (at_ .esp 12)), .alu .add .ebx (imm 0),
      .mov .edi (imm 18)])
    (.loop keyWord .ne)

/-- The output's two words into the P-array entries at the pointer, the
next pair, and the encryptions left less one. -/
def storeP : List Instr :=
  [.mov .ebx (.mem (at_ .ebp ptrOff)), .mov .edx (.mem (at_ .ebp cntOff)),
   .mov .eax (.mem (at_ .ebp xlOff)), .store (at_ .ebx 0) .eax,
   .mov .eax (.mem (at_ .ebp xrOff)), .store (at_ .ebx 4) .eax,
   .alu .add .ebx (imm 8), .store (at_ .ebp ptrOff) .ebx, .alu .sub .edx (imm 1),
   .store (at_ .ebp cntOff) .edx]

/-- The first nine encryptions replace the P-array, a pair of entries each. -/
def encryptP : Prog isa :=
  .seq (.block [.mov .ebx (.mem (at_ .esp 12)), .alu .add .ebx (imm pOff), .store (at_ .ebp ptrOff) .ebx,
      .mov .ecx (imm 9), .store (at_ .ebp cntOff) .ecx])
    (.loop (.seq (cipher 12 true) (.block storeP)) .ne)

/-- The bytes of the word in `eax` into the planes of the S-box entry at
`ebx + e`. -/
def storeEntry (e : Nat) : List Instr :=
  [.store8 (at_ .ebx e) .al, .shift .shr .eax 8, .store8 (at_ .ebx (256 + e)) .al, .shift .shr .eax 8,
   .store8 (at_ .ebx (512 + e)) .al, .shift .shr .eax 8, .store8 (at_ .ebx (768 + e)) .al]

/-- The output's two words into the S-box entries at the pointer, and the
next pair: past the other planes after an S-box's last entry. -/
def storeS : Prog isa :=
  .seq (.block ([.mov .ebx (.mem (at_ .ebp ptrOff)), .mov .edx (.mem (at_ .ebp cntOff)),
      .mov .eax (.mem (at_ .ebp xlOff))] ++ storeEntry 0 ++ [.mov .eax (.mem (at_ .ebp xrOff))] ++
      storeEntry 1 ++ [.alu .add .ebx (imm 2), .mov .ecx (.mem (at_ .esp 12)), .alu .sub .ecx (.reg .ebx),
      .alu .test .ecx (imm 255)]))
    (.seq (.ite .e (.block [.alu .add .ebx (imm 768)]) (.block []))
      (.block [.store (at_ .ebp ptrOff) .ebx, .alu .sub .edx (imm 1), .store (at_ .ebp cntOff) .edx]))

/-- The other 512 replace the S-boxes. -/
def encryptS : Prog isa :=
  .seq (.block [.mov .ebx (.mem (at_ .esp 12)), .store (at_ .ebp ptrOff) .ebx, .mov .ecx (imm 512),
      .store (at_ .ebp cntOff) .ecx])
    (.loop (.seq (cipher 12 true) storeS) .ne)

def expandKey : Prog isa :=
  .seq (.block (save ++ initSchedule))
    (.seq keyP
      (.seq (.block [.mov .eax (imm 0), .store (at_ .ebp xlOff) .eax, .store (at_ .ebp xrOff) .eax])
        (.seq encryptP (.seq encryptS (.block restore)))))

end VG.Impl.Blowfish.X86
