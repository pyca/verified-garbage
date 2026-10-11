module

public import VerifiedGarbage.Impl.Gcm.X86_64.StitchAvx
public import VerifiedGarbage.Impl.Gcm.X86_64.StitchZH

/-!
# Eight-block AES-NI/GHASH pipeline

AES stays in 128-bit registers. Eight independent AES states occupy xmm0,
xmm3–xmm6 and xmm13–xmm15. The round key shares xmm1 with GHASH's reduction
constant; the constant is reloaded only at reduction. Each key size has a
fixed AES loop, with GHASH work spread across its available rounds.

Scratch holds eight hash powers at 128–255, reversed hash inputs at
512–639, counters at 640–767, constants at 768–799, and the saved round count and data pointer at
800–815. Integer loads and byte swaps prepare hash inputs one batch ahead.
Counter words are prepared early for the next batch, using full inc32
arithmetic with no counter-dependent branches. Encryption runs sixteen
blocks ahead of hashing; decryption hashes ciphertext before overwriting it.

Encryption takes any number of blocks from 16 on: once the pipeline stops,
with `t = n mod 8` blocks left, it encrypts the eight counters it prepared
next, stores their keystream at 832–959, and adds it to the `t` blocks one at
a time, hashing each with the power `H'ᵗ⁻ⁱ` (`StitchZH.remBody`).

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

def xorData : List XReg → Nat → List Instr
  | [], _ => []
  | b :: bs, j => ([.vbinLoad .vpxor .l128 b b (at_ .rdx (16*j)),
      .vmovdquStore .l128 (at_ .rdx (16*j)) b] : List Instr) ++ xorData bs (j+1)

def aesFixed (nr : Nat) (regs : List XReg) (g : Nat → List Instr) : Prog isa :=
  .block (VG.Impl.Aes.X86_64.Vaes.keyOpL .l128 .xmm1 regs .vpxor (at_ .rdi 0) ++
    (List.range (nr-1)).flatMap (fun j => VG.Impl.Aes.X86_64.Vaes.roundL .l128 .xmm1 regs (j+1) ++ g (j+1)) ++
    VG.Impl.Aes.X86_64.Vaes.keyOpL .l128 .xmm1 regs .vaesenclast (at_ .r10 0))

def batch (nr n j : Nat) (g : Nat → List Instr) : Prog isa :=
  .seq (.block ((List.range n).map (fun i => .vmovdquLoad .l128 (aregs.getD i .xmm3) (at_ .r11 (640+16*i)))))
    (.seq (aesFixed nr (aregs.take n) (fun j => g j ++
       (if 1 ≤ j ∧ j ≤ 2 then (List.range 4).flatMap (fun i => prepCounter (4*(j-1)+i)) else [])))
     (.block (xorData (aregs.take n) j ++ ([.alu32 .add .r8 (.imm 8)] : List Instr))))

def finish : List Instr :=
  ([.mov .rax (.reg .rsi), .alu32 .sub .r8 (.imm 8), .bswap32 .r8,
   .store32 (at_ .rax 12) .r8, .vmovdquLoad .l128 .xmm0 (at_ .r11 768)] : List Instr) ++ Stitch.storeY ++ ([.mov .r8 (.mem (at_ .r11 808)), .mov .rsi (.mem (at_ .r11 800))] : List Instr)

def prepare (k : Nat) : List Instr :=
  [.mov .rax (.mem (at_ .rdx (16*k+8))), .bswap .rax,
   .store (at_ .r11 (512+16*(k%8))) .rax,
   .mov .rax (.mem (at_ .rdx (16*k))), .bswap .rax,
   .store (at_ .r11 (520+16*(k%8))) .rax]

def accInit (a b : XReg) : List Instr :=
  [.vop (.vpclmulqdq .l128 .xmm8 a b 0x00),
   .vop (.vpclmulqdq .l128 .xmm10 a b 0x11),
   .vop (.vpclmulqdq .l128 .xmm9 a b 0x01),
   .vop (.vpclmulqdq .l128 .xmm11 a b 0x10),
   .vop (.vbin .vpxor .l128 .xmm9 .xmm9 .xmm11)]

def gh8 (k : Nat) : List Instr :=
  ([.vmovdquLoad .l128 .xmm12 (at_ .r11 (16*(8+k%8))),
   .vmovdquLoad .l128 .xmm7 (at_ .r11 (512+16*(k%8)))] : List Instr) ++
   (if k % 8 = 0 then [.vop (.vbin .vpxor .l128 .xmm7 .xmm7 .xmm2)] else []) ++ (if k%8 = 1 then accInit .xmm7 .xmm12 else acc .xmm7 .xmm12)

def q8 (nr : Nat) (more : Bool) (j : Nat) : List Instr :=
  if nr = 10 then
    if 1 ≤ j ∧ j ≤ 8 then gh8 (j%8) ++ (if more then prepare (8+j%8) else [])
    else if j = 9 then reduceFinal else []
  else if nr = 12 then
    if j = 1 then gh8 1 ++ (if more then prepare 9 else []) else
    if j = 2 then gh8 2 ++ (if more then prepare 10 else []) else
    if j = 3 then gh8 3 ++ (if more then prepare 11 else []) else
    if j = 5 then gh8 4 ++ (if more then prepare 12 else []) else
    if j = 6 then gh8 5 ++ (if more then prepare 13 else []) else
    if j = 7 then gh8 6 ++ (if more then prepare 14 else []) else
    if j = 9 then gh8 7 ++ (if more then prepare 15 else []) else
    if j = 10 then gh8 0 ++ (if more then prepare 8 else []) else
    if j = 11 then reduceFinal else []
  else
    if j = 1 then gh8 1 ++ (if more then prepare 9 else []) else
    if j = 2 then gh8 2 ++ (if more then prepare 10 else []) else
    if j = 4 then gh8 3 ++ (if more then prepare 11 else []) else
    if j = 6 then gh8 4 ++ (if more then prepare 12 else []) else
    if j = 8 then gh8 5 ++ (if more then prepare 13 else []) else
    if j = 10 then gh8 6 ++ (if more then prepare 14 else []) else
    if j = 11 then gh8 7 ++ (if more then prepare 15 else []) else
    if j = 12 then gh8 0 ++ (if more then prepare 8 else []) else
    if j = 13 then reduceFinal else []

def hash8 : List Instr := (List.range 8).flatMap (fun i => gh8 ((i+1)%8)) ++ reduceFinal

def encBody8 (nr : Nat) : Prog isa :=
  .seq (.block []) (.seq (batch nr 8 16 (q8 nr true))
    (.block [.alu .add .rdx (.imm 128), .alu .sub .r9 (.imm 8), .alu .cmp .r9 (.imm 24)]))

/-- The keystream of the eight counters prepared after the last batch,
stored to `scratch + 832`. -/
def ksTail (nr : Nat) : Prog isa :=
  .seq (.block ((List.range 8).map (fun i => .vmovdquLoad .l128 (aregs.getD i .xmm3) (at_ .r11 (640+16*i)))))
    (.seq (aesFixed nr aregs (fun _ => []))
      (.block ((List.range 8).map (fun i => .vmovdquStore .l128 (at_ .r11 (832+16*i)) (aregs.getD i .xmm3)))))

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

/-- After the `t` blocks: `r11` back, their products reduced into `Y`, and
the last round key's address back in `r10`. -/
def tailEnd (nr : Nat) : List Instr :=
  ([.alu .sub .r11 (.imm 64)] : List Instr) ++ StitchAvx.reduceHash ++
  ([.mov .r10 (.reg .rdi), .alu .add .r10 (.imm (BitVec.ofNat 32 (16 * nr)))] : List Instr)

/-- The blocks after the pipeline's, if any: `r9 - 16` of them, at
`rdx + 256`. -/
def tailT (nr : Nat) : Prog isa :=
  .seq (.block [.alu .cmp .r9 (.imm 16)])
    (.ite .e (.block [])
      (.seq (ksTail nr)
        (.seq (.block (tailSetup ++ StitchAvx.zero))
          (.seq (.loop (.block (StitchZH.remBody .rdx ++ StitchZH.remNext)) .ne) (.block (tailEnd nr))))))

def encFor (nr : Nat) : Prog isa :=
  .seq (.block setup) (.seq (batch nr 8 0 (fun _ => [])) (.seq (batch nr 8 8 (fun _ => []))
    (.seq (.block ((List.range 8).flatMap prepare ++ ([.alu .cmp .r9 (.imm 24)] : List Instr)))
      (.seq (.ite .b (.block []) (.loop (encBody8 nr) .ae))
        (.seq (.block (hash8 ++ (List.range 8).flatMap (fun i => prepare (8+i)) ++ hash8))
          (.seq (tailT nr) (.block finish)))))))

def decBody8 (nr : Nat) : Prog isa :=
  .seq (.block []) (.seq (batch nr 8 0 (q8 nr true))
    (.block [.alu .add .rdx (.imm 128), .alu .sub .r9 (.imm 8), .alu .cmp .r9 (.imm 16)]))

def decFor (nr : Nat) : Prog isa :=
  .seq (.block (setup ++ (List.range 8).flatMap prepare))
    (.seq (.loop (decBody8 nr) .ae) (.seq (.block [])
      (.seq (batch nr 8 0 (q8 nr false)) (.block finish))))

/-- Choose the complete loop once, from the public AES round count. -/
def dispatch (a b c : Prog isa) : Prog isa :=
  .seq (.block [.alu .cmp .rsi (.imm 10)])
    (.ite .e a (.seq (.block [.alu .cmp .rsi (.imm 12)]) (.ite .e b c)))

def enc : Prog isa := dispatch (encFor 10) (encFor 12) (encFor 14)
def dec : Prog isa := dispatch (decFor 10) (decFor 12) (decFor 14)
end VG.Impl.Gcm.X86_64.StitchAvx8
