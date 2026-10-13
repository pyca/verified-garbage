module

public import VerifiedGarbage.Spec.Blowfish
public import VerifiedGarbage.TCB.X86_64.Isa
public import VerifiedGarbage.Impl.Blowfish.Table

/-!
# Blowfish on baseline x86-64

One block at a time, its halves in the low doublewords of `xmm0` (xL) and
`xmm1` (xR). An S-box lookup scans every entry of the S-box's four byte
planes in SSE2 registers, 16 entries (a row of each plane) at a time:
each row's bytes go to 16-bit lanes (the even entries and the odd ones),
and the lanes whose entry is the index are kept, by a mask that `x XOR k`
minus one is negative exactly when `x = k` (RC2's scans). Every address and
branch is a public counter or pointer; the index is only ever an operand
of the mask's arithmetic. ORing the lanes of each plane gives the entry's
bytes.

Registers: `xmm0`, `xmm1` the halves, `xmm2` F, `xmm3` the index in every
lane, `xmm4` the even entries' numbers in the current row, `xmm6` and
`xmm7` the even and odd masks, `xmm8`–`xmm11` the planes' accumulators,
`xmm5` and `xmm12` temporaries, and the constants 1, 16 and `0x00FF` in
every word in `xmm13`–`xmm15`. The schedule is at `sch`; `rax` holds the
offset of the next P-array entry, `r8` the row's offset and `r9` the rows
left, `r10` the rounds left, and `r11` is a temporary.
-/

@[expose] public section

namespace VG.Impl.Blowfish.X86_64

open VG.X86_64

def mem (base : Reg) (offset : Nat) : MemOp := { base, disp := Int.ofNat offset }

/-- The offset of byte plane `b` of S-box `j` in the schedule. -/
def planeOff (j b : Nat) : Nat := 1024 * j + 256 * b

/-- The P-array's offset in the schedule. -/
def pOff : Nat := 4096

def xL : XReg := .xmm0
def xR : XReg := .xmm1
def fReg : XReg := .xmm2
def idxReg : XReg := .xmm3
def kReg : XReg := .xmm4
def tmp2 : XReg := .xmm5
def mEven : XReg := .xmm6
def mOdd : XReg := .xmm7
def accReg (b : Nat) : XReg := [.xmm8, .xmm9, .xmm10, .xmm11].getD b .xmm8
def tmp : XReg := .xmm12
def onesReg : XReg := .xmm13
def sixteenReg : XReg := .xmm14
def lowReg : XReg := .xmm15

def bin (op : XBinOp) (d s : XReg) : Instr := .xop (.bin op d s)
def shift (op : XShiftOp) (d : XReg) (n : Nat) : Instr := .xop (.shift op d (BitVec.ofNat 8 n))

/-- The 128-bit constant `v` into `dst`, through `r11` and `tmp`. -/
def loadConst (dst : XReg) (v : BitVec 128) : List Instr :=
  [.movImm64 .r11 (v.extractLsb' 0 64), .xop (.movq dst .r11),
   .movImm64 .r11 (v.extractLsb' 64 64), .xop (.movq tmp .r11), bin .punpcklqdq dst tmp]

/-- `w` in every 16-bit lane. -/
def wordsOf (w : Nat) : BitVec 128 := ofWords fun _ => BitVec.ofNat 16 w

/-- The even entries' numbers in row 0: `0, 2, …, 14`. -/
def evenStart : BitVec 128 := ofWords fun i => BitVec.ofNat 16 (2 * i)

/-- The constants of the scans. -/
def constants : List Instr :=
  loadConst onesReg (wordsOf 1) ++ loadConst sixteenReg (wordsOf 16) ++
    loadConst lowReg (wordsOf 0xFF)

/-! ## F -/

/-- Byte `k` of xL (byte 0 the least significant) in every 16-bit lane of
`idxReg`. -/
def index (k : Nat) : List Instr :=
  [bin .movdqa idxReg xL, shift .pslld idxReg (24 - 8 * k), shift .psrld idxReg 24,
   bin .punpcklwd idxReg idxReg, .xop (.pshufd idxReg idxReg 0)]

/-- The masks of the row in `kReg`: all ones in the lanes of the even
(`mEven`) and odd (`mOdd`) entries that are the index. -/
def masks : List Instr :=
  [bin .movdqa mEven kReg, bin .pxor mEven idxReg, bin .psubw mEven onesReg,
   shift .psraw mEven 15,
   bin .movdqa mOdd kReg, bin .paddw mOdd onesReg, bin .pxor mOdd idxReg,
   bin .psubw mOdd onesReg, shift .psraw mOdd 15]

/-- The row at `r8` of plane `b` of S-box `j`. -/
def rowMem (sch : Reg) (j b : Nat) : MemOp := { base := sch, index := some .r8, disp := Int.ofNat (planeOff j b) }

/-- The row of plane `b` of S-box `j` at `sch + r8`, masked into `accReg b`. -/
def plane (sch : Reg) (j b : Nat) : List Instr :=
  [.movdquLoad tmp (rowMem sch j b),
   bin .movdqa tmp2 tmp, bin .pand tmp lowReg, shift .psrlw tmp2 8,
   bin .pand tmp mEven, bin .pand tmp2 mOdd, bin .por (accReg b) tmp, bin .por (accReg b) tmp2]

/-- One row of the four planes; the next row. -/
def row (sch : Reg) (j : Nat) : List Instr :=
  masks ++ (List.range 4).flatMap (plane sch j) ++
    [bin .paddw kReg sixteenReg, .alu .add .r8 (.imm 16), .alu .sub .r9 (.imm 1)]

/-- The OR of the lanes of `accReg b`, in its low doubleword (and nothing
else in it). -/
def reduce (b : Nat) : List Instr :=
  [.xop (.pshufd tmp (accReg b) 0x4E), bin .por (accReg b) tmp,
   .xop (.pshufd tmp (accReg b) 0xB1), bin .por (accReg b) tmp,
   bin .movdqa tmp (accReg b), shift .psrld tmp 16, bin .por (accReg b) tmp,
   shift .pslld (accReg b) 16, shift .psrld (accReg b) 16]

/-- S-box `j` at byte `3 - j` of xL, in the low doubleword of `accReg 0`. -/
def lookup (sch : Reg) (j : Nat) : Prog isa :=
  .seq (.block (index (3 - j) ++ loadConst kReg evenStart ++
      (List.range 4).map (fun b => bin .pxor (accReg b) (accReg b)) ++
      ([.mov32 .r8 (.imm 0), .mov32 .r9 (.imm 16)] : List Instr)))
    (.seq (.loop (.block (row sch j)) .ne)
      (.block ((List.range 4).flatMap reduce ++
        [shift .pslld (accReg 1) 8, shift .pslld (accReg 2) 16, shift .pslld (accReg 3) 24,
         bin .por (accReg 0) (accReg 1), bin .por (accReg 0) (accReg 2),
         bin .por (accReg 0) (accReg 3)])))

/-- F's accumulation of S-box `j`: S₁, then + S₂, XOR S₃, + S₄. -/
def combineX (j : Nat) : XOp :=
  if j = 0 then .bin .movdqa fReg (accReg 0)
  else if j = 2 then .bin .pxor fReg (accReg 0)
  else .bin .paddd fReg (accReg 0)

def combine (j : Nat) : Instr := .xop (combineX j)

/-- F of xL into `fReg`. -/
def f (sch : Reg) : Prog isa :=
  .seq (lookup sch 0) (.seq (.block [combine 0]) (.seq (lookup sch 1) (.seq (.block [combine 1])
    (.seq (lookup sch 2) (.seq (.block [combine 2]) (.seq (lookup sch 3) (.block [combine 3])))))))

/-! ## Rounds -/

/-- The P-array entry at `rax` into the low doubleword of `tmp`. -/
def loadP (sch : Reg) : List Instr :=
  [.mov32 .r11 (.mem { base := sch, index := some .rax, disp := Int.ofNat pOff }), .xop (.movq tmp .r11)]

/-- `xL ^= P` (the entry at `rax`), `xR ^= F(xL)`, the halves swapped; `rax`
moves to the next entry (`up`) or the previous one; `r10` counts down. -/
def round (sch : Reg) (up : Bool) : Prog isa :=
  .seq (.block (loadP sch ++ [bin .pxor xL tmp]))
    (.seq (f sch)
      (.block [bin .pxor xR fReg, bin .movdqa tmp xL, bin .movdqa xL xR, bin .movdqa xR tmp,
        if up then .alu .add .rax (.imm 4) else .alu .sub .rax (.imm 4), .alu .sub .r10 (.imm 1)]))

/-- The sixteen rounds, then the last swap undone: xL (in `xR`) ^= P₁₈ and
xR (in `xL`) ^= P₁₇ when encrypting, P₁ and P₂ when decrypting. -/
def cipher (sch : Reg) (up : Bool) : Prog isa :=
  .seq (.block [.mov32 .rax (.imm (if up then 0 else 68)), .mov32 .r10 (.imm 16)])
    (.seq (.loop (round sch up) .ne)
      (.block ([.mov32 .r11 (.mem (mem sch (pOff + 4 * (if up then 16 else 1)))), .xop (.movq tmp .r11),
          bin .pxor xL tmp,
          .mov32 .r11 (.mem (mem sch (pOff + 4 * (if up then 17 else 0)))), .xop (.movq tmp .r11),
          bin .pxor xR tmp] : List Instr)))

/-! ## ECB

`vg_blowfish_ecb_{en,de}crypt(schedule = rdi, data = rsi, n = rdx,
scratch = rcx)`: the 16 bytes at the working space carry the halves out of
the vector registers. -/

/-- The block at `rsi` into the halves, as big-endian words. -/
def loadBlock : List Instr :=
  [.mov32 .r11 (.mem (mem .rsi 0)), .bswap32 .r11, .xop (.movq xL .r11),
   .mov32 .r11 (.mem (mem .rsi 4)), .bswap32 .r11, .xop (.movq xR .r11)]

/-- The output block, xL (in `xR`) then xR (in `xL`), to `rsi`, through the
working space. -/
def storeBlock : List Instr :=
  [.movdquStore (mem .rcx 0) xR, .mov32 .r11 (.mem (mem .rcx 0)), .bswap32 .r11,
   .store32 (mem .rsi 0) .r11,
   .movdquStore (mem .rcx 0) xL, .mov32 .r11 (.mem (mem .rcx 0)), .bswap32 .r11,
   .store32 (mem .rsi 4) .r11]

def ecb (up : Bool) : Prog isa :=
  .seq (.block constants)
    (.seq (.block [.alu .test .rdx (.reg .rdx)])
      (.ite .e (.block [])
        (.loop (.seq (.block loadBlock) (.seq (cipher .rdi up)
            (.block (storeBlock ++ ([.alu .add .rsi (.imm 8), .alu .sub .rdx (.imm 1)] : List Instr))))) .ne)))

def encrypt : Prog isa := ecb true
def decrypt : Prog isa := ecb false

/-! ## Key expansion

`vg_blowfish_expand_key(key = rdi, key_len = rsi, schedule = rdx,
scratch = rcx)`: the 32 bytes at the working space carry each encryption's
output out of the vector registers. -/

/-- The initial schedule (`Impl.Blowfish.initWords`), a quadword at a time,
as immediates. -/
def initSchedule : List Instr :=
  (List.range 521).flatMap fun i => [.movImm64 .r11 (initWord i), .store (mem .rdx (8 * i)) .r11]

/-- The next key byte into the low byte of `r11` (shifted up), cycling: the
byte at `rdi + r10`, then `r10 := r10 + 1`, or 0 at `key_len`. -/
def keyByte : Prog isa :=
  .seq (.block [.movzx8 .rax { base := .rdi, index := some .r10 }, .shift32 .shl .r11 8,
      .alu32 .or .r11 (.reg .rax), .alu .add .r10 (.imm 1), .alu .cmp .r10 (.reg .rsi)])
    (.ite .e (.block [.mov32 .r10 (.imm 0)]) (.block []))

/-- The P-array entry at `rdx + 4096 + r8` XORed with the next 32 bits of
the key. -/
def keyWord : Prog isa :=
  .seq (.block [.mov32 .r11 (.imm 0)])
    (.seq keyByte (.seq keyByte (.seq keyByte (.seq keyByte
      (.block [.mov32 .rax (.mem { base := .rdx, index := some .r8, disp := Int.ofNat pOff }),
        .alu32 .xor .rax (.reg .r11), .store32 { base := .rdx, index := some .r8, disp := Int.ofNat pOff } .rax,
        .alu .add .r8 (.imm 4), .alu .cmp .r8 (.imm 72)])))))

/-- Pᵢ ^= the next 32 bits of the key, for the 18 entries. -/
def keyP : Prog isa :=
  .seq (.block [.mov32 .r10 (.imm 0), .mov32 .r8 (.imm 0)]) (.loop keyWord .ne)

/-- An encryption's output, xL (in `xR`) and xR (in `xL`), to the working
space, and back into the halves for the next. -/
def outWords : List Instr :=
  [.movdquStore (mem .rcx 0) xR, .movdquStore (mem .rcx 16) xL]

/-- The output's two words into P-array entries `rdi / 4` and `rdi / 4 + 1`. -/
def storeP : List Instr :=
  outWords ++
  ([.mov32 .r11 (.mem (mem .rcx 0)), .xop (.movq xL .r11),
   .store32 { base := .rdx, index := some .rdi, disp := Int.ofNat pOff } .r11,
   .mov32 .r11 (.mem (mem .rcx 16)), .xop (.movq xR .r11),
   .store32 { base := .rdx, index := some .rdi, disp := Int.ofNat (pOff + 4) } .r11] : List Instr)

/-- The bytes of the word in `r11` into the planes of the S-box entry at
`rdx + rdi + e`. -/
def storeEntry (e : Nat) : List Instr :=
  [.store8 { base := .rdx, index := some .rdi, disp := Int.ofNat e } .r11, .shift32 .shr .r11 8,
   .store8 { base := .rdx, index := some .rdi, disp := Int.ofNat (256 + e) } .r11, .shift32 .shr .r11 8,
   .store8 { base := .rdx, index := some .rdi, disp := Int.ofNat (512 + e) } .r11, .shift32 .shr .r11 8,
   .store8 { base := .rdx, index := some .rdi, disp := Int.ofNat (768 + e) } .r11]

/-- The output's two words into the S-box entries at `rdi` and `rdi + 1`. -/
def storeS : List Instr :=
  outWords ++ ([.mov32 .r11 (.mem (mem .rcx 0)), .xop (.movq xL .r11)] : List Instr) ++ storeEntry 0 ++
    ([.mov32 .r11 (.mem (mem .rcx 16)), .xop (.movq xR .r11)] : List Instr) ++ storeEntry 1

/-- The first nine encryptions replace the P-array, a pair of entries each;
`rsi` counts them. -/
def encryptP : Prog isa :=
  .seq (.block [.mov32 .rdi (.imm 0), .mov32 .rsi (.imm 9)])
    (.loop (.seq (cipher .rdx true) (.block (storeP ++ ([.alu .add .rdi (.imm 8),
        .alu .sub .rsi (.imm 1)] : List Instr))))
      .ne)

/-- The other 512 replace the S-boxes; `rdi` skips the other planes after
each S-box's last entry. -/
def encryptS : Prog isa :=
  .seq (.block [.mov32 .rdi (.imm 0), .mov32 .rsi (.imm 512)])
    (.loop (.seq (cipher .rdx true)
        (.seq (.block (storeS ++ ([.alu .add .rdi (.imm 2), .alu .test .rdi (.imm 255)] : List Instr)))
          (.seq (.ite .e (.block [.alu .add .rdi (.imm 768)]) (.block []))
            (.block [.alu .sub .rsi (.imm 1)]))))
      .ne)

def expandKey : Prog isa :=
  .seq (.block initSchedule)
    (.seq keyP
      (.seq (.block (constants ++ [bin .pxor xL xL, bin .pxor xR xR])) (.seq encryptP encryptS)))

end VG.Impl.Blowfish.X86_64
