module

public import VerifiedGarbage.Impl.Words.RISCV64
public import VerifiedGarbage.Impl.Words.RISCV64.Loops
public import VerifiedGarbage.Impl.Blowfish.Table

/-!
# Blowfish on RISC-V

The algorithm of the PPC64LE implementation (`Impl/Blowfish/PPC64LE.lean`):
one block at a time in general-purpose registers, and an S-box lookup reads
every entry of the S-box's four byte planes, a row of eight entries of each
plane (a doubleword, `ld`) at a time. A row's mask is all ones in the byte
lane of the index's entry if the row holds it (`(q - 8k) >> 3` is zero, for
the index `q`), else zero, made without a comparison: `(v - 1) >> 63`,
arithmetically, is all ones exactly when `v < 2 ^ 63` is zero. The masked
doublewords are ORed into one accumulator, plane `b`'s rotated left by `8b`.
The accumulator then holds byte `b` of the entry in lane `L + b` (mod 8), for
the index's lane `L`, and rotating it right by `8L`, by three rotations
selected by masks of `L`'s bits, gives the entry in its low word. Every
address and branch is a public counter or pointer; the index is only ever
an operand of the masks' arithmetic. There are no rotate instructions: a
rotation is two shifts and an XOR.

The model faults on misaligned accesses, and the contracts state no
alignment for the schedule, so the code keeps it in a frame of 4176 bytes
on the stack, which is 16-byte aligned (three frames of 2032, 2032 and 112
bytes, as one `addi` allocates at most 2047): ECB copies the schedule there
a byte at a time, and key expansion builds it there and copies it out. Both
zero the frame before returning. The blocks and the key are accessed a
byte at a time.

The halves and F are 32-bit values in the low words of their registers;
their high words are whatever the arithmetic leaves, which nothing reads:
word shifts read the low word, word stores store it, and the index is taken
from it. The accumulator is a doubleword until the lookup's end, when its
low word is the entry.

Registers: the frame (the schedule) at `a7` (`sch`), the halves in `a3` (xL)
and `a4` (xR), F in `a5`, the P-array pointer in `a6`; during a lookup, the
index less four times the rows read so far in `t1` (`q`), the accumulator in
`t2`, the row's mask in `t3`, temporaries in `t4` and `t5`, the index's lane
mask in `t6` and the row pointer in `t0`. ECB keeps the data pointer in `a1`
and the blocks left in `a2`; key expansion, the schedule's pointer in `a2`,
the pointer to the next entries in `a1` and the encryptions left in `a0`.
Only temporaries and argument registers are used.
-/

@[expose] public section

namespace VG.Impl.Blowfish.RISCV64

open VG.RISCV64
open VG.Impl.Words.RISCV64 (loadBE32 storeBE li32 copyLoop fillLoop)

def sch : Reg := .a7
def xL : Reg := .a3
def xR : Reg := .a4
def fReg : Reg := .a5
def pPtr : Reg := .a6
def qReg : Reg := .t1
def acc : Reg := .t2
def mReg : Reg := .t3
def tmp : Reg := .t4
def tmp2 : Reg := .t5
def lane : Reg := .t6
def rowPtr : Reg := .t0
def ptr : Reg := .a1
def cnt : Reg := .a2

/-- The P-array's offset in the schedule. -/
def pOff : Nat := 4096

/-- The bytes of the frame holding the schedule: 4168, rounded up to 16. -/
def frameBytes : Nat := 4176

/-! ## Lookups -/

/-- The accumulator of plane `b`. -/
def accOf : Nat → Reg
  | 0 => .t2
  | 1 => .t5
  | 2 => .t6
  | _ => .t0

/-- `q` := the row of the byte of xL that indexes S-box `j`: byte `3 - j`,
shifted to the top of the doubleword and back, less its lane. -/
def index (j : Nat) : List Instr :=
  [.shift .sll .d qReg xL (32 + 8 * j), .shift .srl .d qReg qReg 59]

/-- Row `k`'s mask: all ones if `q` is `k` (`q XOR k` is zero, so less one
it is negative), else zero. -/
def rowMask (k : Nat) : List Instr :=
  [.logicImm .xor mReg qReg k, .addi mReg mReg (-1), .shift .sra .d mReg mReg 63]

/-- Plane `b`'s doubleword of row 0, masked, into its accumulator. -/
def firstPlane (b : Nat) : List Instr :=
  [.load .d (accOf b) sch (256 * b), .logic .and (accOf b) (accOf b) mReg]

/-- Plane `b`'s doubleword of row `k`, masked, ORed into its accumulator. -/
def plane (k b : Nat) : List Instr :=
  [.load .d tmp sch (256 * b + 8 * k), .logic .and tmp tmp mReg, .logic .or (accOf b) (accOf b) tmp]

/-- Row `k` (eight entries) of the S-box at `sch`: the mask and the four
planes. -/
def row (k : Nat) : List Instr :=
  rowMask k ++ if k = 0 then firstPlane 0 ++ firstPlane 1 ++ firstPlane 2 ++ firstPlane 3
    else plane k 0 ++ plane k 1 ++ plane k 2 ++ plane k 3

/-- Rows `0, …, n - 1`. -/
def rows (n : Nat) : List Instr := (List.range n).flatMap row

/-- `d := 2 ^ (8 * 2 ^ c)` if bit `c` of the lane (bit `56 + c` of `t3`'s
complement) is clear, else 1: the bit shifted to the top, arithmetically
down, logically down to `8 * 2 ^ c` ones, plus one. -/
def factor (d : Reg) (c : Nat) : List Instr :=
  [.shift .sll .d d mReg (7 - c), .shift .sra .d d d 63, .shift .srl .d d d (64 - 8 * 2 ^ c), .addi d d 1]

/-- Plane `b`'s byte of the entry from its accumulator: the accumulator
times `2 ^ (56 - 8L)` (in `q`), whose top byte is lane `L`'s, shifted down
to byte `b`. -/
def pick (b : Nat) : List Instr :=
  [.mul (accOf b) (accOf b) qReg, .shift .srl .d (accOf b) (accOf b) 56] ++
    if b = 0 then [] else [.shift .sll .d (accOf b) (accOf b) (8 * b)]

/-- The entry from the accumulators, into the low word of `acc`: `q :=
2 ^ (56 - 8L)` for the index's lane `L`, a product of three factors, then
each plane's byte and their OR. -/
def extract (j : Nat) : List Instr :=
  [.shift .sll .d mReg xL (32 + 8 * j), .logicImm .xor mReg mReg (-1)] ++ factor tmp 0 ++ factor qReg 1 ++
    [.mul tmp tmp qReg] ++ factor qReg 2 ++ [.mul qReg tmp qReg] ++ pick 0 ++ pick 1 ++ pick 2 ++ pick 3 ++
    [.logic .or acc acc (accOf 1), .logic .or (accOf 2) (accOf 2) (accOf 3), .logic .or acc acc (accOf 2)]

/-- The S-box at `sch` (`sch` is moved to S-box `j`), of xL's byte `3 - j`,
into the accumulator's low word. -/
def lookup (j : Nat) : Prog isa := .block (index j ++ rows 32 ++ extract j)

/-- F's accumulation of S-box `j`: S₁, then + S₂, XOR S₃, + S₄. -/
def combine (j : Nat) : Instr :=
  if j = 0 then .logic .or fReg acc acc
  else if j = 2 then .logic .xor fReg fReg acc
  else .add fReg fReg acc

/-- F of xL into `fReg`'s low word: `sch` moves to each S-box in turn, and
back. -/
def f : Prog isa :=
  .seq (lookup 0) (.seq (.block [combine 0, .addi sch sch 1024]) (.seq (lookup 1)
    (.seq (.block [combine 1, .addi sch sch 1024]) (.seq (lookup 2)
      (.seq (.block [combine 2, .addi sch sch 1024]) (.seq (lookup 3)
        (.block [combine 3, .addi sch sch (-2048), .addi sch sch (-1024)])))))))

/-! ## Rounds

`pPtr` is at the P-array entry of the round (`up`, encrypting), or four
bytes below it (decrypting): at `sch + 4096 + 4i`, or at
`sch + 4096 + 64 - 4i`, for round `i`. -/

/-- The offset from `pPtr` of the round's entry. -/
def pAt (up : Bool) : Nat := if up then 0 else 4

/-- `pPtr`'s offset in the schedule after the last round. -/
def pEnd (up : Bool) : Nat := if up then pOff + 64 else pOff

/-- `xL ^= P`, `xR ^= F(xL)`, the halves swapped, and `pPtr` to the next
entry; `tmp` is zero at the end. -/
def round (up : Bool) : Prog isa :=
  .seq (.block [.load .w tmp pPtr (pAt up), .logic .xor xL xL tmp])
    (.seq f
      (.block [.logic .xor xR xR fReg, .logic .or tmp xL xL, .logic .or xL xR xR,
        .logic .or xR tmp tmp, .addi pPtr pPtr (if up then 4 else -4),
        .sub tmp pPtr sch, .addi tmp tmp (-2047), .addi tmp tmp (-2047),
        .addi tmp tmp (-(pEnd up - 4094 : Nat))]))

/-- The block function: the sixteen rounds, then the last swap undone, xL
(in `xR`) ^= P₁₈ and xR (in `xL`) ^= P₁₇ when encrypting, P₁ and P₂ when
decrypting, into `xL` and `xR`. -/
def cipher (up : Bool) : Prog isa :=
  .seq (.block [.addi pPtr sch 2047, .addi pPtr pPtr 2047,
      .addi pPtr pPtr ((if up then pOff else pOff + 64) - 4094 : Nat)])
    (.seq (.loop (round up) (.nonzero tmp))
      (.block [.load .w tmp pPtr (pAt up), .logic .xor tmp xL tmp,
        .load .w xL pPtr (4 - pAt up), .logic .xor xL xL xR, .logic .or xR tmp tmp]))

/-! ## The frame -/

/-- The frame of `frameBytes`, around `body`. -/
def inFrame (body : Prog isa) : Prog isa :=
  .frame (.alloc 2032) (.frame (.alloc 2032) (.frame (.alloc 112) body (.free 112)) (.free 2032))
    (.free 2032)

/-- `t4 := 4168`. -/
def li4168 : List Instr := [.li tmp 1042, .shift .sll .d tmp tmp 2]

/-- Zero the frame at `sch`, a doubleword at a time. -/
def wipe : Prog isa :=
  .seq (.block [.li .t1 0, .addi rowPtr sch 0, .li tmp 522])
    (fillLoop .t1 rowPtr tmp)

/-! ## ECB

`vg_blowfish_ecb_{en,de}crypt(schedule = a0, data = a1, n = a2)`. -/

/-- The block at the data pointer into the halves, as big-endian words. -/
def loadBlock : List Instr := loadBE32 xL tmp ptr 0 ++ loadBE32 xR tmp ptr 4

/-- The halves to the block, and the next block. -/
def storeBlock : List Instr :=
  storeBE 4 xL tmp ptr 0 ++ storeBE 4 xR tmp ptr 4 ++ [.addi ptr ptr 8, .addi cnt cnt (-1)]

/-- In the frame: the schedule copied there, the blocks, and the frame zeroed. -/
def ecbMain (up : Bool) : Prog isa :=
  .seq (.block ([.addSp sch 0, .addi rowPtr sch 0] ++ li4168)) (.seq (copyLoop .t1 .a0 rowPtr tmp)
    (.seq (.loop (.seq (.block loadBlock) (.seq (cipher up) (.block storeBlock))) (.nonzero cnt))
      wipe))

def ecb (up : Bool) : Prog isa := .ite (.zero cnt) (.block []) (inFrame (ecbMain up))

def encrypt : Prog isa := ecb true
def decrypt : Prog isa := ecb false

/-! ## Key expansion

`vg_blowfish_expand_key(key = a0, key_len = a1, schedule = a2)`. -/

/-- Word `i` of the initial schedule in the layout of `scheduleAt`: bytes
`4 i`…`4 i + 3`, little-endian. -/
def initWord32 (i : Nat) : BitVec 32 :=
  (List.range 4).foldl (fun w b => w ||| (Impl.Blowfish.initByte (4 * i + b)).zeroExtend 32 <<< (8 * b)) 0

/-- Word `i` of the initial schedule, as an immediate, into the frame at
`t0`, which moves on to the next. -/
def initStep (i : Nat) : List Instr :=
  li32 tmp (initWord32 i) ++ ([.store .w tmp rowPtr 0, .addi rowPtr rowPtr 4] : List Instr)

/-- The initial schedule, a word at a time, as immediates, into the frame at
`sch`. -/
def initSchedule : List Instr := .addi rowPtr sch 0 :: (List.range 1042).flatMap initStep

/-- The next key byte into the low byte of `t2` (shifted up), cycling: the
byte at `a0 + t1`, then `t1 := t1 + 1`, or 0 at `key_len` (`a1`). -/
def keyByte : Prog isa :=
  .seq (.block [.add tmp .a0 .t1, .load .b .t3 tmp 0, .shift .sll .d .t2 .t2 8, .logic .or .t2 .t2 .t3,
      .addi .t1 .t1 1, .sub tmp .t1 .a1])
    (.ite (.zero tmp) (.block [.li .t1 0]) (.block []))

/-- The P-array entry at `a6` XORed with the next 32 bits of the key; the
next entry, and the entries left in `t5`. -/
def keyWord : Prog isa :=
  .seq (.block [.li .t2 0])
    (.seq keyByte (.seq keyByte (.seq keyByte (.seq keyByte
      (.block [.load .w .t3 .a6 0, .logic .xor .t3 .t3 .t2, .store .w .t3 .a6 0,
        .addi .a6 .a6 4, .addi .t5 .t5 (-1)])))))

/-- Pᵢ ^= the next 32 bits of the key, for the 18 entries. -/
def keyP : Prog isa :=
  .seq (.block [.li .t1 0, .addi .a6 sch 2047, .addi .a6 .a6 2047, .addi .a6 .a6 2, .li .t5 18])
    (.loop keyWord (.nonzero .t5))

/-- The output's two words into the P-array entries at `ptr`, and the next
pair. -/
def storeP : List Instr :=
  [.store .w xL .a1 0, .store .w xR .a1 4, .addi .a1 .a1 8, .addi .a0 .a0 (-1)]

/-- The first nine encryptions replace the P-array, a pair of entries each. -/
def encryptP : Prog isa :=
  .seq (.block [.addi .a1 sch 2047, .addi .a1 .a1 2047, .addi .a1 .a1 2, .li .a0 9])
    (.loop (.seq (cipher true) (.block storeP)) (.nonzero .a0))

/-- The bytes of the word in `x` into the planes of the S-box entry at
`a1 + e`. -/
def storeEntry (x : Reg) (e : Nat) : List Instr :=
  [.store .b x .a1 e, .shift .srl .w tmp x 8, .store .b tmp .a1 (256 + e), .shift .srl .w tmp x 16,
   .store .b tmp .a1 (512 + e), .shift .srl .w tmp x 24, .store .b tmp .a1 (768 + e)]

/-- The output's two words into the S-box entries at `a1`, and the next
pair: past the other planes after an S-box's last entry. -/
def storeS : Prog isa :=
  .seq (.block (storeEntry xL 0 ++ storeEntry xR 1 ++
      [.addi .a1 .a1 2, .sub tmp .a1 sch, .shift .sll .d tmp tmp 56]))
    (.seq (.ite (.zero tmp) (.block [.addi .a1 .a1 768]) (.block []))
      (.block [.addi .a0 .a0 (-1)]))

/-- The other 512 replace the S-boxes. -/
def encryptS : Prog isa :=
  .seq (.block [.addi .a1 sch 0, .li .a0 512]) (.loop (.seq (cipher true) storeS) (.nonzero .a0))

/-- In the frame: the schedule built there, copied to `a2`, and the frame
zeroed. -/
def expandMain : Prog isa :=
  .seq (.block (.addSp sch 0 :: initSchedule)) (.seq keyP
    (.seq (.block [.li xL 0, .li xR 0]) (.seq encryptP (.seq encryptS
      (.seq (.block ([.addi rowPtr sch 0] ++ li4168)) (.seq (copyLoop .t1 rowPtr .a2 tmp) wipe))))))

def expandKey : Prog isa := inFrame expandMain

end VG.Impl.Blowfish.RISCV64
