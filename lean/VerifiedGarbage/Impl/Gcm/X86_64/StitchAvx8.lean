module

public import VerifiedGarbage.Impl.Gcm.X86_64.StitchZH

/-!
# Eight-block AES-NI/GHASH pipeline

AES stays in 128-bit registers. Eight independent AES states occupy xmm0,
xmm3–xmm6 and xmm13–xmm15. The round key shares xmm1 with GHASH's reduction
constant; the constant is reloaded only at reduction. Each key size has a
fixed AES loop, with GHASH work spread across its available rounds.

Scratch holds eight hash powers at 128–255, counters at 640–767, constants
at 768–799, the saved round count and data pointer at 800–815, and, out of
place, the saved `rbx` at 816–823. GHASH reads its inputs from the data,
byte-reversed by `vpshufb` with the mask at 768, since no register is free
to hold it.
Counter words are prepared early for the next batch, using full inc32
arithmetic with no counter-dependent branches. Encryption runs sixteen
blocks ahead of hashing; decryption hashes ciphertext before overwriting it.

Encryption takes any number of blocks from 16 on: once the pipeline stops,
with `t = n mod 8` blocks left, it encrypts the eight counters it prepared
next, stores their keystream at 832–959, and adds it to the `t` blocks one at
a time, hashing each with the power `H'ᵗ⁻ⁱ` (`StitchZH.remBody`). Decryption with a
prepared key context (`decR`) likewise takes any number of blocks from 16
on: after its last batch, it hashes each of the `t` blocks left before
decrypting it (`StitchZH.remBodyD`).

The entry and exit follow Stitch's internal interface; scratch fits its
1024-byte region, and the input data register r8 is restored on exit.
-/

@[expose] public section

namespace VG.Impl.Gcm.X86_64.StitchAvx8
open VG.X86_64
open VG.Impl.Gcm.X86_64.Pclmul (revMask poly xInv)
open VG.Impl.Aes.X86_64.AesNi (at_)

def aregs : List XReg := [.xmm0, .xmm3, .xmm4, .xmm5, .xmm6, .xmm13, .xmm14, .xmm15]

def zero : List Instr :=
  [.vop (.vbin .vpxor .l128 .xmm8 .xmm8 .xmm8), .vop (.vbin .vpxor .l128 .xmm9 .xmm9 .xmm9),
   .vop (.vbin .vpxor .l128 .xmm10 .xmm10 .xmm10)]

def acc (a b : XReg) : List Instr :=
  [.vop (.vpclmulqdq .l128 .xmm11 a b 0x00), .vop (.vbin .vpxor .l128 .xmm8 .xmm8 .xmm11),
   .vop (.vpclmulqdq .l128 .xmm11 a b 0x11), .vop (.vbin .vpxor .l128 .xmm10 .xmm10 .xmm11),
   .vop (.vpclmulqdq .l128 .xmm11 a b 0x01), .vop (.vbin .vpxor .l128 .xmm9 .xmm9 .xmm11),
   .vop (.vpclmulqdq .l128 .xmm11 a b 0x10), .vop (.vbin .vpxor .l128 .xmm9 .xmm9 .xmm11)]

def fold : List Instr :=
  [.vop (.vpclmulqdq .l128 .xmm11 .xmm8 .xmm1 0x10), .vop (.vpshufd .l128 .xmm8 .xmm8 0x4e),
   .vop (.vbin .vpxor .l128 .xmm8 .xmm8 .xmm11)]

def reduce (d : XReg) : List Instr :=
  ([.vop (.vshift .psrldq .l128 .xmm11 .xmm9 8), .vop (.vbin .vpxor .l128 .xmm10 .xmm10 .xmm11),
   .vop (.vshift .pslldq .l128 .xmm9 .xmm9 8), .vop (.vbin .vpxor .l128 .xmm8 .xmm8 .xmm9)] : List Instr) ++
  fold ++ fold ++ ([.vop (.vbin .vpxor .l128 d .xmm10 .xmm8)] : List Instr)

def mul (d a b : XReg) : List Instr := zero ++ acc a b ++ reduce d

def const (x : XReg) (c : BitVec 128) : List Instr :=
  [.movImm64 .rax (c.extractLsb' 0 64), .vop (.vmovq x .rax),
   .movImm64 .rax (c.extractLsb' 64 64), .vop (.vmovq .xmm12 .rax),
   .vop (.vbin .vpunpcklqdq .l128 x x .xmm12)]

def hInv : List Instr :=
  const .xmm13 xInv ++
  ([.movImm64 .rax 0xffffffffffffffff, .vop (.vmovq .xmm14 .rax),
   .vop (.vbin .vpunpcklqdq .l128 .xmm14 .xmm14 .xmm14),
   .vop (.vshift .psllq .l128 .xmm3 .xmm7 1),
   .vop (.vshift .psrlq .l128 .xmm11 .xmm7 63), .vop (.vshift .pslldq .l128 .xmm11 .xmm11 8),
   .vop (.vbin .vpor .l128 .xmm3 .xmm3 .xmm11),
   .vop (.vpshufd .l128 .xmm11 .xmm7 0xff), .vop (.vshift .psrld .l128 .xmm11 .xmm11 31),
   .vop (.vbin .vpaddd .l128 .xmm11 .xmm11 .xmm14),
   .vop (.vbin .vpandn .l128 .xmm11 .xmm11 .xmm13), .vop (.vbin .vpxor .l128 .xmm3 .xmm3 .xmm11)] : List Instr)

def preg : Nat → XReg
  | 0 => .xmm3 | 1 => .xmm4 | 2 => .xmm5 | 3 => .xmm6 | 4 => .xmm12 | 5 => .xmm13 | 6 => .xmm14
  | _ => .xmm15

def setupG : List Instr :=
  const .xmm0 revMask ++ const .xmm1 poly ++
  ([.vmovdquLoad .l128 .xmm7 (at_ .rdi 240), .vop (.vbin .vpshufb .l128 .xmm7 .xmm7 .xmm0)] : List Instr) ++ hInv ++
  mul .xmm4 .xmm3 .xmm3 ++ mul .xmm5 .xmm4 .xmm3 ++ mul .xmm6 .xmm4 .xmm4 ++ mul .xmm12 .xmm6 .xmm3 ++
  mul .xmm13 .xmm6 .xmm4 ++ mul .xmm14 .xmm6 .xmm5 ++ mul .xmm15 .xmm6 .xmm6

def lows (n : Nat) : List Instr :=
  (List.range n).map fun i => .vmovdquStore .l128 (at_ .r11 (16 * (15 - i))) (preg i)

def setupC : List Instr :=
  [.vmovdquLoad .l128 .xmm2 (at_ .rcx 0), .vop (.vbin .vpshufb .l128 .xmm2 .xmm2 .xmm0),
   .mov .r10 (.reg .rsi), .shift .shl .r10 4, .alu .add .r10 (.reg .rdi),
   .mov .rax (.reg .rdx), .mov .rdx (.reg .r8)]

def prepCounter (i : Nat) : List Instr :=
  [.mov32 .rax (.reg .r8), .alu32 .add .rax (.imm (BitVec.ofNat 32 i)), .bswap32 .rax,
   .store32 (at_ .r11 (652+16*i)) .rax]

def initCounter : List Instr :=
  ([.store (at_ .r11 808) .rdx, .store (at_ .r11 800) .rsi, .mov .rsi (.reg .rax),
   .vmovdquLoad .l128 .xmm7 (at_ .rax 0),
   .mov32 .r8 (.mem (at_ .rax 12)), .bswap32 .r8] : List Instr) ++
  (List.range 8).map (fun i => .vmovdquStore .l128 (at_ .r11 (640+16*i)) .xmm7) ++
  (List.range 8).flatMap prepCounter ++ ([.alu32 .add .r8 (.imm 8)] : List Instr)

def setup : List Instr := setupG ++ lows 8 ++ setupC ++
  ([.vmovdquStore .l128 (at_ .r11 768) .xmm0,
   .vmovdquStore .l128 (at_ .r11 784) .xmm1] : List Instr) ++ initCounter

/-- Where a prepared key context (`Spec.Gcm.PreparedPowersRepr`) holds `H'ⁿ`,
for `n` from 1 to 48: in pairs, the even power first. -/
def prepOff (n : Nat) : Nat := if n % 2 = 0 then 224 + 16 * n else 256 + 16 * n

/-- `setupG` for a prepared key context: the constants, and `H'` … `H'⁸`
loaded from it into the registers where `setupG` computes them. -/
def setupGR : List Instr :=
  const .xmm0 revMask ++ const .xmm1 poly ++
  (List.range 8).map fun i => .vmovdquLoad .l128 (preg i) (at_ .rdi (prepOff (i + 1)))

/-- `setup` for a prepared key context. -/
def setupR : List Instr := setupGR ++ lows 8 ++ setupC ++
  ([.vmovdquStore .l128 (at_ .r11 768) .xmm0,
   .vmovdquStore .l128 (at_ .r11 784) .xmm1] : List Instr) ++ initCounter

def reduceFinal : List Instr :=
  [.vmovdquLoad .l128 .xmm1 (at_ .r11 784),
   .vop (.vpclmulqdq .l128 .xmm11 .xmm8 .xmm1 0x10),
   .vop (.vpshufd .l128 .xmm8 .xmm8 0x4e),
   .vop (.vbin .vpxor .l128 .xmm9 .xmm9 .xmm8),
   .vop (.vbin .vpxor .l128 .xmm9 .xmm9 .xmm11),
   .vop (.vpclmulqdq .l128 .xmm11 .xmm9 .xmm1 0x10),
   .vop (.vpshufd .l128 .xmm9 .xmm9 0x4e),
   .vop (.vbin .vpxor .l128 .xmm2 .xmm10 .xmm9),
   .vop (.vbin .vpxor .l128 .xmm2 .xmm2 .xmm11)]

/-- Where the data at `rdx + d` is read from: there, or, out of place
(`ix`), at `rdx + rbx + d`, `rbx` holding `src - dst`. -/
def srcAt (ix : Bool) (d : Nat) : MemOp :=
  if ix then { base := .rdx, index := some .rbx, disp := d } else at_ .rdx d

/-- XOR block register `i` into the block read from `srcAt ix (16 (j + i))`,
and store it to `rdx + 16 (j + i)`. -/
def xorData (ix : Bool) : List XReg → Nat → List Instr
  | [], _ => []
  | b :: bs, j => ([.vbinLoad .vpxor .l128 b b (srcAt ix (16*j)),
      .vmovdquStore .l128 (at_ .rdx (16*j)) b] : List Instr) ++ xorData ix bs (j+1)

def aesFixed (nr : Nat) (regs : List XReg) (g : Nat → List Instr) : Prog isa :=
  .block (VG.Impl.Aes.X86_64.Vaes.keyOpL .l128 .xmm1 regs .vpxor (at_ .rdi 0) ++
    (List.range (nr-1)).flatMap (fun j => VG.Impl.Aes.X86_64.Vaes.roundL .l128 .xmm1 regs (j+1) ++ g (j+1)) ++
    VG.Impl.Aes.X86_64.Vaes.keyOpL .l128 .xmm1 regs .vaesenclast (at_ .r10 0))

/-- The first `n` counter blocks loaded from their templates. -/
def loads (n : Nat) : List Instr :=
  (List.range n).map (fun i => .vmovdquLoad .l128 (aregs.getD i .xmm3) (at_ .r11 (640+16*i)))

/-- A batch whose counter blocks `ld` puts in `aregs`, its data read from
`srcAt ix`. -/
def batchL (ld : List Instr) (nr n j : Nat) (g : Nat → List Instr) (ix : Bool := false) : Prog isa :=
  .seq (.block ld)
    (.seq (aesFixed nr (aregs.take n) (fun j => g j ++
       (if 1 ≤ j ∧ j ≤ 2 then (List.range 4).flatMap (fun i => prepCounter (4*(j-1)+i)) else [])))
     (.block (xorData ix (aregs.take n) j ++ ([.alu32 .add .r8 (.imm 8)] : List Instr))))

def batch (nr n j : Nat) (g : Nat → List Instr) (ix : Bool := false) : Prog isa :=
  batchL (loads n) nr n j g ix

/-- The first batch's eight counter blocks, from the counter block in `xmm7`
(as `initCounter` loaded it) rather than from the templates `initCounter`
has just written, whose 16-byte loads would wait for its 4-byte stores to
reach the cache: the block byte-reversed into `xmm11` (as `inc32` counts),
incremented by `xmm12 = 1` (doubleword 0) and byte-reversed back into each
register, and `xmm7` itself into `xmm0` last, once the mask is no longer
needed. -/
def regCounters : List Instr :=
  ([.vop (.vbin .vpshufb .l128 .xmm11 .xmm7 .xmm0), .movImm64 .rax 1, .vop (.vmovq .xmm12 .rax)] : List Instr) ++
  (List.range 7).flatMap (fun i => [.vop (.vbin .vpaddd .l128 .xmm11 .xmm11 .xmm12),
    .vop (.vbin .vpshufb .l128 (aregs.getD (i+1) .xmm3) .xmm11 .xmm0)]) ++
  ([.vop (.vbin .vpor .l128 .xmm0 .xmm7 .xmm7)] : List Instr)

def finish : List Instr :=
  ([.mov .rax (.reg .rsi), .alu32 .sub .r8 (.imm 8), .bswap32 .r8,
   .store32 (at_ .rax 12) .r8, .vmovdquLoad .l128 .xmm0 (at_ .r11 768)] : List Instr) ++ Stitch.storeY ++ ([.mov .r8 (.mem (at_ .r11 808)), .mov .rsi (.mem (at_ .r11 800))] : List Instr)

def accInit (a b : XReg) : List Instr :=
  [.vop (.vpclmulqdq .l128 .xmm8 a b 0x00),
   .vop (.vpclmulqdq .l128 .xmm10 a b 0x11),
   .vop (.vpclmulqdq .l128 .xmm9 a b 0x01),
   .vop (.vpclmulqdq .l128 .xmm11 a b 0x10),
   .vop (.vbin .vpxor .l128 .xmm9 .xmm9 .xmm11)]

/-- The product of the `k`-th block of eight from `rdx + d` (byte-reversed
with the mask at `r11 + 768`, since every block register holds an AES state)
with its power. -/
def gh8 (d k : Nat) : List Instr :=
  ([.vmovdquLoad .l128 .xmm12 (at_ .r11 (16*(8+k%8))),
   .vmovdquLoad .l128 .xmm7 (at_ .rdx (d+16*(k%8))),
   .vbinLoad .vpshufb .l128 .xmm7 .xmm7 (at_ .r11 768)] : List Instr) ++
   (if k % 8 = 0 then [.vop (.vbin .vpxor .l128 .xmm7 .xmm7 .xmm2)] else []) ++ (if k%8 = 1 then accInit .xmm7 .xmm12 else acc .xmm7 .xmm12)

def q8 (nr : Nat) (j : Nat) : List Instr :=
  if nr = 10 then
    if 1 ≤ j ∧ j ≤ 8 then gh8 0 (j%8)
    else if j = 9 then reduceFinal else []
  else if nr = 12 then
    if j = 1 then gh8 0 1 else
    if j = 2 then gh8 0 2 else
    if j = 3 then gh8 0 3 else
    if j = 5 then gh8 0 4 else
    if j = 6 then gh8 0 5 else
    if j = 7 then gh8 0 6 else
    if j = 9 then gh8 0 7 else
    if j = 10 then gh8 0 0 else
    if j = 11 then reduceFinal else []
  else
    if j = 1 then gh8 0 1 else
    if j = 2 then gh8 0 2 else
    if j = 4 then gh8 0 3 else
    if j = 6 then gh8 0 4 else
    if j = 8 then gh8 0 5 else
    if j = 10 then gh8 0 6 else
    if j = 11 then gh8 0 7 else
    if j = 12 then gh8 0 0 else
    if j = 13 then reduceFinal else []

/-- The eight blocks from `rdx + d` hashed, and the product reduced into `Y`. -/
def hash8 (d : Nat) : List Instr := (List.range 8).flatMap (fun i => gh8 d ((i+1)%8)) ++ reduceFinal

def encBody8 (nr : Nat) (ix : Bool := false) : Prog isa :=
  .seq (.block []) (.seq (batch nr 8 16 (q8 nr) ix)
    (.block [.alu .add .rdx (.imm 128), .alu .sub .r9 (.imm 8), .alu .cmp .r9 (.imm 24)]))

/-- The keystream of the eight counters prepared after the last batch,
stored to `scratch + off`. -/
def ksTail (nr : Nat) (off : Nat := 832) : Prog isa :=
  .seq (.block ((List.range 8).map (fun i => .vmovdquLoad .l128 (aregs.getD i .xmm3) (at_ .r11 (640+16*i)))))
    (.seq (aesFixed nr aregs (fun _ => []))
      (.block ((List.range 8).map (fun i => .vmovdquStore .l128 (at_ .r11 (off+16*i)) (aregs.getD i .xmm3)))))

/-- For the `t = r9 - 16` blocks after the pipeline's: the counter advanced
by `t`, the powers `H'ᵗ` … `H'` at `rax = scratch + 256 - 16 t`, `rdx` at
the `t` blocks, `r10 = 0`, the mask and the reduction constant loaded, and
`r11` moved up 64 bytes, so that the keystream is at `r11 + 768`, as
`StitchZH.remBody` reads it. -/
def tailSetup : List Instr :=
  [.mov .r10 (.reg .r9), .alu .sub .r10 (.imm 16), .alu32 .add .r8 (.reg .r10), .shift .shl .r10 4,
   .mov .rax (.reg .r11), .alu .add .rax (.imm 256), .alu .sub .rax (.reg .r10),
   .alu .add .rdx (.imm 256), .mov32 .r10 (.imm 0),
   .vmovdquLoad .l128 .xmm0 (at_ .r11 768), .vmovdquLoad .l128 .xmm1 (at_ .r11 784),
   .alu .add .r11 (.imm 64)]

/-- After the `t` blocks: `r11` back (by `back`), their products reduced
into `Y`, and the last round key's address back in `r10`. -/
def tailEnd (nr : Nat) (back : Instr := .alu .sub .r11 (.imm 64)) : List Instr :=
  ([back] : List Instr) ++ StitchAvx.reduceHash ++
  ([.mov .r10 (.reg .rdi), .alu .add .r10 (.imm (BitVec.ofNat 32 (16 * nr)))] : List Instr)

/-- The blocks after the pipeline's, if any: `r9 - 16` of them, at
`rdx + 256`, read there or, out of place (`ix`), at `rbx` moved to
`rdx + rbx` for the loop. -/
def tailT (nr : Nat) (ix : Bool := false) : Prog isa :=
  .seq (.block [.alu .cmp .r9 (.imm 16)])
    (.ite .e (.block [])
      (.seq (ksTail nr)
        (.seq (.block (tailSetup ++ (if ix then [.alu .add .rbx (.reg .rdx)] else []) ++ StitchAvx.zero))
          (.seq (.loop (.block (StitchZH.remBody (if ix then .rbx else .rdx) ++ StitchZH.remNext)) .ne)
            (.block ((if ix then [.alu .sub .rbx (.reg .rdx)] else []) ++ tailEnd nr))))))

/-- Encryption, after the setup, of the data read from `srcAt ix`. -/
def encRest (nr : Nat) (ix : Bool := false) : Prog isa :=
  .seq (batchL regCounters nr 8 0 (fun _ => []) ix) (.seq (batch nr 8 8 (fun _ => []) ix)
    (.seq (.block [.alu .cmp .r9 (.imm 24)])
      (.seq (.ite .b (.block []) (.loop (encBody8 nr ix) .ae))
        (.seq (.block (hash8 0 ++ hash8 128))
          (.seq (tailT nr ix) (.block finish))))))

def decBody8 (nr : Nat) : Prog isa :=
  .seq (.block []) (.seq (batch nr 8 0 (q8 nr))
    (.block [.alu .add .rdx (.imm 128), .alu .sub .r9 (.imm 8), .alu .cmp .r9 (.imm 16)]))

/-- The blocks after the last batch of decryption, if any: `r9 - 8` of them,
at `rdx + 128`, as `tailT` takes them once `r9` and `rdx` are moved to where
encryption leaves them (`16` more blocks and `256` bytes before them), each
hashed before it is decrypted (`StitchZH.remBodyD`). -/
def tailD (nr : Nat) : Prog isa :=
  .seq (.block [.alu .add .r9 (.imm 8), .alu .sub .rdx (.imm 128), .alu .cmp .r9 (.imm 16)])
    (.ite .e (.block [])
      (.seq (ksTail nr)
        (.seq (.block (tailSetup ++ StitchAvx.zero))
          (.seq (.loop (.block (StitchZH.remBodyD .rdx ++ StitchZH.remNext)) .ne)
            (.block (tailEnd nr))))))

/-- Decryption, after the setup: of any number of blocks from 16 on with
`rem`, and of a multiple of 16 without it. -/
def decRest (nr : Nat) (rem : Bool) : Prog isa :=
  .seq (.block []) (.seq (.loop (decBody8 nr) .ae) (.seq (.block [])
    (.seq (batch nr 8 0 (q8 nr)) (.seq (if rem then tailD nr else .block []) (.block finish)))))

/-! ## Fewer blocks than the pipeline takes

With a prepared key context, `encRS` and `decRS` take fewer than 16 blocks,
from 1 on, without the pipeline: as `tailT` takes the blocks after it, but
for all `t = r9` blocks from the start, with the keystream of up to 16
counters at `scratch + 384` and the powers `H'ᵗ` … `H'` below `H'⁸`. -/

/-- The powers `H'⁹` … `H'¹⁵`, loaded from the prepared key context and
stored below the setup's `H'⁸` … `H'`: `H'ᵏ` at `scratch + 256 - 16 k`. -/
def highs : List Instr :=
  (List.range 7).flatMap fun i =>
    [.vmovdquLoad .l128 .xmm12 (at_ .rdi (prepOff (i + 9))), .vmovdquStore .l128 (at_ .r11 (112 - 16 * i)) .xmm12]

/-- For the `t = r9` blocks: the counter advanced by `t`, the powers `H'ᵗ`
… `H'` at `rax = scratch + 256 - 16 t`, `r9 = 16 + t`, `r10 = 0`, the mask
and the reduction constant loaded, and `r11` moved down 384 bytes, so that
the keystream at `scratch + 384` is at `r11 + 768`, as `StitchZH.remBody`
reads it. -/
def smallSetup : List Instr :=
  [.mov .r10 (.reg .r9), .alu32 .add .r8 (.reg .r10), .shift .shl .r10 4,
   .mov .rax (.reg .r11), .alu .add .rax (.imm 256), .alu .sub .rax (.reg .r10),
   .alu .add .r9 (.imm 16), .mov32 .r10 (.imm 0),
   .vmovdquLoad .l128 .xmm0 (at_ .r11 768), .vmovdquLoad .l128 .xmm1 (at_ .r11 784),
   .alu .sub .r11 (.imm 384)]

/-- Encryption (decryption with `dec`) of the `r9` blocks, 1 to 15, after
the setup: the keystream of the eight counters it prepared stored at
`scratch + 384`; from 9 blocks on, that of the next eight at `scratch + 512`
and the powers `H'⁹` … `H'¹⁵`; then each block encrypted and hashed
(`StitchZH.remBody`), or hashed and decrypted (`StitchZH.remBodyD`), and
their products reduced into `Y`. -/
def small (nr : Nat) (dec : Bool) : Prog isa :=
  .seq (ksTail nr 384)
    (.seq (.block [.alu .cmp .r9 (.imm 9)])
      (.seq (.ite .b (.block [])
          (.seq (.block ((List.range 8).flatMap prepCounter)) (.seq (ksTail nr 512) (.block highs))))
        (.seq (.block (smallSetup ++ StitchAvx.zero))
          (.seq (.loop (.block ((if dec then StitchZH.remBodyD .rdx else StitchZH.remBody .rdx) ++
              StitchZH.remNext)) .ne)
            (.block (tailEnd nr (.alu .add .r11 (.imm 384)) ++ finish))))))

/-- The setup `su`, which does not depend on the key size, then the complete
loop for the key size, chosen once from the public AES round count `nr`: the
setup leaves the end of the key schedule, `rdi + 16 nr`, in `r10`. -/
def dispatch (su : List Instr) (a b c : Prog isa) : Prog isa :=
  .seq (.block (su ++ ([.mov .rax (.reg .rdi), .alu .add .rax (.imm 160), .alu .cmp .r10 (.reg .rax)] : List Instr)))
    (.ite .e a (.seq (.block [.alu .add .rax (.imm 32), .alu .cmp .r10 (.reg .rax)]) (.ite .e b c)))

def enc : Prog isa := dispatch setup (encRest 10) (encRest 12) (encRest 14)
/-- Encryption with a prepared key context: the powers loaded from it. -/
def encR : Prog isa := dispatch setupR (encRest 10) (encRest 12) (encRest 14)
/-- Encryption with a prepared key context of 1 to 15 blocks, `small`, which
`Blocks.fullBody` runs on fewer than 16 blocks only, after `encR`'s code,
which keeps the addresses of `encR`'s loops wherever it runs from 16 blocks
on. -/
def encRS : Prog isa := dispatch setupR (small 10 false) (small 12 false) (small 14 false)
def dec : Prog isa := dispatch setup (decRest 10 false) (decRest 12 false) (decRest 14 false)
/-- Decryption with a prepared key context: the powers loaded from it. -/
def decR : Prog isa := dispatch setupR (decRest 10 true) (decRest 12 true) (decRest 14 true)
/-- Decryption with a prepared key context of 1 to 15 blocks (see `encRS`). -/
def decRS : Prog isa := dispatch setupR (small 10 true) (small 12 true) (small 14 true)

/-! ## Out of place

`vg_aes_gcm_encrypt_blocks_to`'s loops (`Stitch.SPreTo`: `src` in `r8`,
`dst` in `r10`): `rbx` is kept at `scratch + 816`, which nothing else
uses, and holds `src - dst`; `r8` holds `dst`, where the loop writes the
ciphertext and the hash reads it back, as in place. Each batch reads its
data at `rdx + rbx` (`srcAt`), and so do the blocks after the pipeline's.
-/

/-- `rbx` kept, `src - dst` in `rbx` and `dst` in `r8`. -/
def toEntry : List Instr :=
  [.store (at_ .r11 816) .rbx, .mov .rbx (.reg .r8), .alu .sub .rbx (.reg .r10), .mov .r8 (.reg .r10)]

/-- `rbx` restored. -/
def toExit : List Instr := [.mov .rbx (.mem (at_ .r11 816))]

/-- Encryption out of place, after the setup `su`. -/
def encToWith (su : List Instr) : Prog isa :=
  .seq (.block toEntry)
    (.seq (dispatch su (encRest 10 true) (encRest 12 true) (encRest 14 true)) (.block toExit))

def encTo : Prog isa := encToWith setup
/-- Encryption out of place with a prepared key context. -/
def encToR : Prog isa := encToWith setupR
end VG.Impl.Gcm.X86_64.StitchAvx8
