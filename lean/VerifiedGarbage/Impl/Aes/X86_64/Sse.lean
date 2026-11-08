module

public import VerifiedGarbage.Impl.Aes.X86_64.Ctr32
public import VerifiedGarbage.Impl.TripleDes.X86_64.BitsliceAllocX

/-!
# AES counter mode, eight blocks at a time in SSE2 registers, on x86-64

`vg_aes_ctr32` (`Ctr32.lean`) bitslices four blocks into eight 64-bit
general-purpose registers. Here the same layout (BearSSL's `aes_ct64`,
Thomas Pornin, MIT licence) is in each quadword of eight 128-bit registers
`xmm0 … xmm7`: quadword 0 holds blocks 0–3 of a group of eight, quadword 1
blocks 4–7. Every layer acts on each quadword as `Ctr32.lean`'s acts on a
register, with SSE2's bitwise operations and shifts (`StraightX` checks
them quadword by quadword):

* the transposes swap bits within quadwords (`psrlq`, `psllq`), as
  `toBs` and `fromBs`, with the masks in `xmm8 … xmm13`;
* ShiftRows rotates each 16-bit row with `psrlw` and `psllw` (rows 1 and 3
  by 4 bits, then rows 2 and 3 by 8), blending with the masks at
  `[r11]`, `[r11 + 16]`;
* MixColumns rotates quadwords by 16 bits with two shifts, and by 32 with
  `pshufd` (dwords `1 0 3 2`);
* the S-box is `Circuit.sbox`, allocated to `xmm0 … xmm14` by the DES
  circuits' allocator (`BitsliceAllocX`), spilling to `[rcx + 16k]`, with
  all ones in `xmm15`;
* AddRoundKey loads 16 bytes from the 64-bit bitsliced round key word
  (`[rsi + 8j]`) and copies its low quadword to both (`punpcklqdq`).

The round keys are bitsliced once, by `Ctr32.lean`'s key loop, and the
callee-saved registers and the counter block are in its slots. A group of
eight blocks (`sseGroup`) runs while more than four are left; the last one
to four, if any, take `Ctr32.lean`'s group of four, which costs half as
much. Only public values choose branches and addresses, as there.
-/

@[expose] public section

namespace VG.Impl.Aes.X86_64.Sse

open VG.X86_64

def X : Nat → XReg
  | 0 => .xmm0 | 1 => .xmm1 | 2 => .xmm2 | 3 => .xmm3 | 4 => .xmm4 | 5 => .xmm5 | 6 => .xmm6
  | 7 => .xmm7 | 8 => .xmm8 | 9 => .xmm9 | 10 => .xmm10 | 11 => .xmm11 | 12 => .xmm12
  | 13 => .xmm13 | 14 => .xmm14 | _ => .xmm15

def bin (op : XBinOp) (d s : XReg) : Instr := .xop (.bin op d s)
def mova (d s : XReg) : Instr := bin .movdqa d s
def pxor (d s : XReg) : Instr := bin .pxor d s
def pand (d s : XReg) : Instr := bin .pand d s
def por (d s : XReg) : Instr := bin .por d s
def shx (op : XShiftOp) (d : XReg) (n : Nat) : Instr := .xop (.shift op d (BitVec.ofNat 8 n))
def ldx (d : XReg) (b : Reg) (o : Nat) : Instr := .movdquLoad d (at_ b o)
def stx (b : Reg) (o : Nat) (s : XReg) : Instr := .movdquStore (at_ b o) s

/-- Word `j` of the state. -/
def q (j : Nat) : XReg := X j
/-- Mask `k` (1 … 6) of the transposes. -/
def m (k : Nat) : XReg := X (7 + k)
def t0 : XReg := .xmm14
def t1 : XReg := .xmm15

/-- `d := (v, v)`, through `rax`. -/
def mkMask (d : XReg) (v : BitVec 64) : List Instr :=
  [.movImm64 .rax v, .xop (.movq d .rax), bin .punpcklqdq d d]

/-! ## Between blocks and the bitsliced state, quadword by quadword -/

def swapIn (x : XReg) (k s : Nat) : List Instr :=
  [mova t0 x, shx .psrlq t0 s, pxor t0 x, pand t0 (m k), pxor x t0, shx .psllq t0 s, pxor x t0]

def swapBetween (x y : XReg) (k s : Nat) : List Instr :=
  [mova t0 x, shx .psrlq t0 s, pxor t0 y, pand t0 (m k), pxor y t0, shx .psllq t0 s, pxor x t0]

def bsMasks : List Instr := Impl.Aes.X86_64.bsMasks.flatMap fun (k, v) => mkMask (m k) v
def zip1 : List Instr := (List.range 8).flatMap fun k => swapIn (q k) 1 16
def zip2 : List Instr := (List.range 8).flatMap fun k => swapIn (q k) 2 8
def swap8 : List Instr := (List.range 4).flatMap fun b => swapBetween (q b) (q (b + 4)) 3 8
def ortho : List Instr :=
  ([(0, 1), (2, 3), (4, 5), (6, 7)].flatMap fun (a, b) => swapBetween (q a) (q b) 4 1) ++
  ([(0, 2), (1, 3), (4, 6), (5, 7)].flatMap fun (a, b) => swapBetween (q a) (q b) 5 2) ++
  ([(0, 4), (1, 5), (2, 6), (3, 7)].flatMap fun (a, b) => swapBetween (q a) (q b) 6 4)

def toBs : List Instr := bsMasks ++ zip1 ++ zip2 ++ swap8 ++ ortho
def fromBs : List Instr := bsMasks ++ ortho ++ swap8 ++ zip2 ++ zip1

/-! ## The S-box -/

open Impl.Aes.Circuit in
/-- `Circuit.sbox` as the DES allocator's gates: `a ⊕ ¬b` is `t := a ⊕ b`
then `¬t`, with `t` a fresh variable from `n`. -/
def gates : List Gate → Nat → List Impl.TripleDes.Bitslice.Gate
  | [], _ => []
  | g :: gs, n => match g.op with
    | .xor => ⟨g.dst, .xor, g.a, g.b⟩ :: gates gs n
    | .and => ⟨g.dst, .and, g.a, g.b⟩ :: gates gs n
    | .xnor => ⟨n, .xor, g.a, g.b⟩ :: ⟨g.dst, .not, n, n⟩ :: gates gs (n + 1)

/-- The spill slots, `[rcx + 16k]`. -/
def spills : Nat := 15

open Impl.Aes.Circuit in
/-- The S-box on the state in `q 0 … q 7`, in place (`xᵢ`, `sᵢ` are bit `7 - i`). -/
def sboxCode : List Instr :=
  mkMask .xmm15 (BitVec.allOnes 64) ++
  Impl.TripleDes.X86_64.BitsliceSse.compile (gates sbox 200)
    ((List.range 8).map fun i => (x i, q (7 - i))) ((List.range 8).map fun i => (s i, q (7 - i)))
    ((List.range 7).map fun k => X (8 + k)) (List.range spills) .xmm15

/-! ## ShiftRows -/

/-- The masks of ShiftRows: rows 1 and 3, then rows 2 and 3, at `[r11]` and `[r11 + 16]`. -/
def srMasks : List (Nat × BitVec 64) := [(0, 0xFFFF0000FFFF0000), (1, 0xFFFFFFFF00000000)]

/-- Where the masks are, from `r9`. -/
def srOff : Nat := 464

/-- Store the masks (once, before the groups). -/
def srSetup : List Instr :=
  srMasks.flatMap fun (k, v) => mkMask t0 v ++ [.movdquStore (at_ .r9 (srOff + 16 * k)) t0]

/-- Rotate each 16-bit word of `x` right by `n` bits into `t0` (`t1` is clobbered); the
shifted halves share no bits, so XOR is OR. -/
def rotW (x : XReg) (n : Nat) : List Instr :=
  [mova t0 x, shx .psrlw t0 n, mova t1 x, shx .psllw t1 (16 - n), pxor t0 t1]

/-- `x := x` with the rows in mask `k` taken from `t0`. -/
def blend (x : XReg) (k : Nat) : List Instr := [pxor t0 x, pand t0 (m (1 + k)), pxor x t0]

def srWord (x : XReg) : List Instr := rotW x 4 ++ blend x 0 ++ rotW x 8 ++ blend x 1

/-- Load the masks into `m 1`, `m 2`. -/
def srLoad : List Instr := [ldx (m 1) .r11 0, ldx (m 2) .r11 16]

def srBody : List Instr := (List.range 8).flatMap fun j => srWord (q j)

def shiftRows : List Instr := srLoad ++ srBody

/-! ## MixColumns -/

def ta : XReg := .xmm8
def tb : XReg := .xmm9
def u7 : XReg := .xmm10

/-- `d := s ⋙ 16` in each quadword (`ta` is clobbered), XOR being OR. -/
def ror16 (d s : XReg) : List Instr :=
  [mova d s, shx .psrlq d 16, mova ta s, shx .psllq ta 48, pxor d ta]

/-- The register output word `j` is computed in. -/
def mcOut (j : Nat) : XReg := if j = 0 then t0 else if j = 1 then t1 else q (j - 2)

/-- Output word `j`, as `Ctr32.lean`'s `mcWord`: `q j` is left holding
`uⱼ = qⱼ ⊕ (qⱼ ⋙ 16)`, and `uⱼ ⋙ 32` is `pshufd` with `1 0 3 2`. -/
def mcWord (j : Nat) : List Instr :=
  ror16 (mcOut j) (q j) ++ [pxor (q j) (mcOut j)] ++
  (if j = 0 then [] else [pxor (mcOut j) (q (j - 1))]) ++
  (if j = 0 ∨ j = 1 ∨ j = 3 ∨ j = 4 then [pxor (mcOut j) u7] else []) ++
  [.xop (.pshufd tb (q j) 0xB1), pxor (mcOut j) tb]

def mixColumns : List Instr :=
  ror16 u7 (q 7) ++ [pxor u7 (q 7)] ++ (List.range 8).flatMap mcWord ++
    ((List.range 8).reverse.map fun j => mova (q j) (mcOut j))

/-! ## AddRoundKey -/

def kp : Reg := .rsi

/-- With the 64-bit bitsliced round key at `kp`, in both quadwords. -/
def addRoundKey : List Instr :=
  (List.range 8).flatMap fun j => [ldx ta kp (8 * j), bin .punpcklqdq ta ta, pxor (q j) ta]

/-! ## The rounds -/

open Impl.Aes.X86_64 (lastKey sb)

/-- A middle round, with `kp` at the previous round key; loops until `kp`
is at the last round key but one. -/
def roundBody : List Instr :=
  ([.alu .add kp (.imm 64)] : List Instr) ++ sboxCode ++ shiftRows ++ mixColumns ++ addRoundKey ++
  [.mov .rax (.reg sb), .alu .add .rax (.imm (BitVec.ofNat 32 (lastKey - 64))), .alu .cmp kp (.reg .rax)]

def lastRound : List Instr :=
  ([.alu .add kp (.imm 64)] : List Instr) ++ sboxCode ++ shiftRows ++ addRoundKey

/-- Encrypt the eight blocks in `q 0 … q 7`, the round keys from `rdi`. -/
def encrypt8 : Prog isa :=
  .seq (.block (toBs ++ [.mov kp (.reg .rdi)] ++ addRoundKey))
    (.seq (.loop (.block roundBody) .ne) (.block (lastRound ++ fromBs)))

/-! ## The counter blocks -/

open Impl.Aes.X86_64 (cHi cLo cNum slotAt)

/-- `r := bytes 8–15 of counter block c + b`. -/
def ctrWord (r : Reg) (b : Nat) : List Instr :=
  [.mov32 r (.mem (slotAt sb cNum)), .alu32 .add r (.imm (BitVec.ofNat 32 b)), .bswap32 r,
   .shift .ror r 32, .alu .xor r (.mem (slotAt sb cHi))]

/-- Block `b` of the group in quadword `b / 4` of `q (b % 4)` (bytes 0–7) and
`q (b % 4 + 4)` (bytes 8–15); and `c := c + 8`. -/
def ctrBlocks : List Instr :=
  [.mov .rax (.mem (slotAt sb cLo)), .xop (.movq (q 0) .rax), bin .punpcklqdq (q 0) (q 0),
   mova (q 1) (q 0), mova (q 2) (q 0), mova (q 3) (q 0)] ++
  ((List.range 4).flatMap fun b =>
    ctrWord .rax b ++ ctrWord .r10 (b + 4) ++
    [.xop (.movq (q (b + 4)) .rax), .xop (.movq ta .r10), bin .punpcklqdq (q (b + 4)) ta]) ++
  [.mov32 .rax (.mem (slotAt sb cNum)), .alu32 .add .rax (.imm 8), .store32 (slotAt sb cNum) .rax]

/-! ## XOR into the data -/

/-- Keystream block `b`: quadword `b / 4` of `q (b % 4)` and of `q (b % 4 + 4)`. -/
def ksBlock (b : Nat) : List Instr :=
  if b < 4 then [mova ta (q b), bin .punpcklqdq ta (q (b + 4))]
  else [mova ta (q (b - 4)), bin .punpckhqdq ta (q b)]

open Impl.Aes.X86_64 (dstR dstLoad dstAdv dstSave) in
/-- XOR keystream block `b` into data block `b`, stored at `dstR to`. -/
def xorBlockG (to : Bool) (b : Nat) : List Instr :=
  ksBlock b ++ [ldx tb .rdx (16 * b), pxor tb ta, stx (dstR to) (16 * b) tb]

def xorBlock : Nat → List Instr := xorBlockG false

open Impl.Aes.X86_64 (dstR dstLoad dstAdv dstSave) in
/-- Eight blocks, and on to the next (ZF is set when none are left). -/
def xorFullG (to : Bool) : List Instr :=
  (List.range 8).flatMap (xorBlockG to) ++ dstAdv to 128 ++ dstSave to ++
    ([.alu .add .rdx (.imm 128), .alu .sub .r8 (.imm 8)] : List Instr)

def xorFull : List Instr := xorFullG false

open Impl.Aes.X86_64 (dstR dstLoad dstAdv dstSave) in
/-- The last five to seven blocks (and ZF set). -/
def xorTailG (to : Bool) : Prog isa :=
  .seq (.block ((List.range 5).flatMap (xorBlockG to) ++ ([.alu .cmp .r8 (.imm 6)] : List Instr)))
    (.seq (.ite .ae (.seq (.block (xorBlockG to 5 ++ ([.alu .cmp .r8 (.imm 7)] : List Instr)))
        (.ite .ae (.block (xorBlockG to 6)) (.block [])))
      (.block []))
    (.block (dstSave to ++ [.alu .sub .r8 (.reg .r8)])))

def xorTail : Prog isa := xorTailG false

/-- The spill slots' base, and the masks' of ShiftRows. -/
def groupSetup : List Instr :=
  [.mov .rcx (.reg .r9), .mov .r11 (.reg .r9), .alu .add .r11 (.imm (BitVec.ofNat 32 srOff))]

open Impl.Aes.X86_64 (dstLoad) in
/-- A group of eight blocks, or the last five to seven. -/
def sseGroupG (to : Bool) : Prog isa :=
  .seq (.block (groupSetup ++ ctrBlocks))
    (.seq encrypt8
      (.seq (.block (dstLoad to ++ [.alu .cmp .r8 (.imm 8)])) (.ite .ae (.block (xorFullG to)) (xorTailG to))))

def sseGroup : Prog isa := sseGroupG false

/-- A group: of four blocks or fewer if at most four are left, else of eight
or the last five to seven. -/
def groupG (to : Bool) : Prog isa :=
  .seq (.block [.alu .cmp .r8 (.imm 5)]) (.ite .b (Impl.Aes.X86_64.groupG to) (sseGroupG to))

def group : Prog isa := groupG false

end VG.Impl.Aes.X86_64.Sse

namespace VG.Impl.Aes.X86_64

open VG.X86_64

/-- Out of place, keep the output pointer (`r11`) in `xmm15` through the key
loop, which writes every general-purpose register but no vector one. -/
def dstStash (to : Bool) : List Instr := if to then [.xop (.movq .xmm15 .r11)] else []

/-- Out of place, store the output pointer from `xmm15` to its slot. -/
def dstInit (to : Bool) : List Instr := if to then [.movqR t1 .xmm15, st dSlot t1] else []

/-- `vg_aes_ctr32(schedule = rdi, rounds = rsi, counter = rdx, data = rcx, n = r8, scratch = r9)`,
or, out of place (`to`), `vg_aes_ctr32_to`, which reads the data at `rcx` and
writes the result to `r11`. -/
def ctr32G (to : Bool) : Prog isa :=
  .seq (.block (dstStash to ++ saveRegs ++ ctrSetup ++ keySetup))
    (.seq (.loop (.block keyBody) .ae)
      (.seq (.block (dstInit to ++ Sse.srSetup ++ keyDone ++ ([.alu .test .r8 (.reg .r8)] : List Instr)))
        (.seq (.ite .e (.block []) (.loop (Sse.groupG to) .ne)) (.block restoreRegs))))

def ctr32 : Prog isa := ctr32G false

/-- `vg_aes_ctr32_to`. -/
def ctr32To : Prog isa := ctr32G true

end VG.Impl.Aes.X86_64
