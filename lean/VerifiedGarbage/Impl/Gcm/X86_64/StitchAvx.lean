module

public import VerifiedGarbage.Impl.Gcm.X86_64.Stitch

/-!
# AES-GCM's counter mode and GHASH, interleaved, with AES-NI and PCLMULQDQ in AVX

The loops of `Impl.Gcm.X86_64.Stitch` for CPUs with AES-NI, PCLMULQDQ and
AVX but not VAES or VPCLMULQDQ, on 128-bit registers (`VEX.128`, whose three
operands save the copies of the SSE forms): `(ctx = rdi, rounds = rsi,
counter = rdx, y = rcx, data = r8, n = r9, scratch = r11)`, `n` a multiple of
16.

The setup computes `H'`–`H'¹⁶` (`H'ᵏ = Hᵏ · x⁻¹`, as `vg_ghash_pclmul` does)
from the hash subkey at `ctx + 240` in a tree of depth four (`H'²`; `H'³`,
`H'⁴`; `H'⁵`–`H'⁸` from `H'⁴`; `H'⁹`–`H'¹⁶` from `H'⁸`), so that the products
overlap, and stores `H'¹⁶⁻ᵏ` to `scratch + 16 k`, the power that the `k`-th
GHASH load of a group multiplies. A group of sixteen blocks is four batches
of four blocks, in `xmm3`–`xmm6`; the GHASH load of one block of the
previous group (encrypting) or of the batch's own blocks, before they are
overwritten (decrypting), follows each of rounds 1–4 of a batch, and the
reduction round 5 of the last batch, so that the counter mode and the hash,
which are independent, share the CPU. When encrypting, the first group is
encrypted alone and the last one hashed alone.

Registers: `xmm0` the byte-reversal mask, `xmm1` the reduction constant,
`xmm2` `Y`, `xmm3`–`xmm6` four blocks being encrypted, `xmm7` a block being
hashed, `xmm8`–`xmm11` the product (`lo`, `mid`, `hi`) and a temporary,
`xmm12` a power, `xmm13` a round key, `xmm14` the counter and `xmm15` 1, its
increment. `rdx` points to the group being hashed, `rax` to the counter,
`r10` to the last round key, `r11` to `scratch`.
-/

@[expose] public section

namespace VG.Impl.Gcm.X86_64.StitchAvx

open VG.X86_64
open VG.Impl.Aes.X86_64.Vaes (aesL)
open VG.Impl.Gcm.X86_64.Pclmul (at_ revMask poly xInv)

def aregs : List XReg := [.xmm3, .xmm4, .xmm5, .xmm6]

/-! ## `vg_ghash_pclmul`'s instructions in `VEX.128` -/

/-- Clear the product. -/
def zero : List Instr :=
  [.vop (.vbin .vpxor .l128 .xmm8 .xmm8 .xmm8), .vop (.vbin .vpxor .l128 .xmm9 .xmm9 .xmm9),
   .vop (.vbin .vpxor .l128 .xmm10 .xmm10 .xmm10)]

/-- Add the carry-less product of `a` and `b` to `lo`, `mid`, `hi`. -/
def acc (a b : XReg) : List Instr :=
  [.vop (.vpclmulqdq .l128 .xmm11 a b 0x00), .vop (.vbin .vpxor .l128 .xmm8 .xmm8 .xmm11),
   .vop (.vpclmulqdq .l128 .xmm11 a b 0x11), .vop (.vbin .vpxor .l128 .xmm10 .xmm10 .xmm11),
   .vop (.vpclmulqdq .l128 .xmm11 a b 0x01), .vop (.vbin .vpxor .l128 .xmm9 .xmm9 .xmm11),
   .vop (.vpclmulqdq .l128 .xmm11 a b 0x10), .vop (.vbin .vpxor .l128 .xmm9 .xmm9 .xmm11)]

/-- One step of the reduction of `lo`. -/
def fold : List Instr :=
  [.vop (.vpclmulqdq .l128 .xmm11 .xmm8 .xmm1 0x10), .vop (.vpshufd .l128 .xmm8 .xmm8 0x4e),
   .vop (.vbin .vpxor .l128 .xmm8 .xmm8 .xmm11)]

/-- The product, reduced, into `d`. -/
def reduce (d : XReg) : List Instr :=
  ([.vop (.vshift .psrldq .l128 .xmm11 .xmm9 8), .vop (.vbin .vpxor .l128 .xmm10 .xmm10 .xmm11),
   .vop (.vshift .pslldq .l128 .xmm9 .xmm9 8), .vop (.vbin .vpxor .l128 .xmm8 .xmm8 .xmm9)] : List Instr) ++
  fold ++ fold ++ ([.vop (.vbin .vpxor .l128 d .xmm10 .xmm8)] : List Instr)

/-- Fold `lo` into `mid`, then `mid` into `hi`, for the running hash.
This needs two carry-less multiplies and avoids packing the middle word. -/
def reduceHash : List Instr :=
  [.vop (.vpclmulqdq .l128 .xmm11 .xmm8 .xmm1 0x10),
   .vop (.vpshufd .l128 .xmm8 .xmm8 0x4e),
   .vop (.vbin .vpxor .l128 .xmm9 .xmm9 .xmm8),
   .vop (.vbin .vpxor .l128 .xmm9 .xmm9 .xmm11),
   .vop (.vpclmulqdq .l128 .xmm11 .xmm9 .xmm1 0x10),
   .vop (.vpshufd .l128 .xmm9 .xmm9 0x4e),
   .vop (.vbin .vpxor .l128 .xmm2 .xmm10 .xmm9),
   .vop (.vbin .vpxor .l128 .xmm2 .xmm2 .xmm11)]

/-- `d ← mul(a, b)`. -/
def mul (d a b : XReg) : List Instr := zero ++ acc a b ++ reduce d

/-- The 128-bit constant `c` into `x`, through `rax` and `xmm12`. -/
def const (x : XReg) (c : BitVec 128) : List Instr :=
  [.movImm64 .rax (c.extractLsb' 0 64), .vop (.vmovq x .rax),
   .movImm64 .rax (c.extractLsb' 64 64), .vop (.vmovq .xmm12 .rax),
   .vop (.vbin .vpunpcklqdq .l128 x x .xmm12)]

/-- `H' = H · x⁻¹` into `xmm3`, from `H` in `xmm7`. -/
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

/-! ## The setup -/

/-- The register of `H'ⁱ⁺¹` (`i < 8`) after `setupG`. -/
def preg : Nat → XReg
  | 0 => .xmm3 | 1 => .xmm4 | 2 => .xmm5 | 3 => .xmm6 | 4 => .xmm12 | 5 => .xmm13 | 6 => .xmm14
  | _ => .xmm15

/-- The constants, `H'` from the hash subkey at `ctx + 240`, and `H'²`–`H'⁸`. -/
def setupG : List Instr :=
  const .xmm0 revMask ++ const .xmm1 poly ++
  ([.vmovdquLoad .l128 .xmm7 (at_ .rdi 240), .vop (.vbin .vpshufb .l128 .xmm7 .xmm7 .xmm0)] : List Instr) ++ hInv ++
  mul .xmm4 .xmm3 .xmm3 ++ mul .xmm5 .xmm4 .xmm3 ++ mul .xmm6 .xmm4 .xmm4 ++ mul .xmm12 .xmm6 .xmm3 ++
  mul .xmm13 .xmm6 .xmm4 ++ mul .xmm14 .xmm6 .xmm5 ++ mul .xmm15 .xmm6 .xmm6

/-- `H'ⁱ⁺¹` (`i < n`) stored to `scratch + 16 (15 − i)`. -/
def lows (n : Nat) : List Instr :=
  (List.range n).map fun i => .vmovdquStore .l128 (at_ .r11 (16 * (15 - i))) (preg i)

/-- `H'⁹⁺ⁱ = mul(H'⁸, H'ⁱ⁺¹)` (`i < n`) stored to `scratch + 16 (7 − i)`. -/
def highs (n : Nat) : List Instr :=
  (List.range n).flatMap fun i =>
    mul .xmm7 .xmm15 (preg i) ++ ([.vmovdquStore .l128 (at_ .r11 (16 * (7 - i))) .xmm7] : List Instr)

/-- `Y`, the counter, the increment, the last round key's address, and the
pointers of the loop. -/
def setupC : List Instr :=
  [.vmovdquLoad .l128 .xmm2 (at_ .rcx 0), .vop (.vbin .vpshufb .l128 .xmm2 .xmm2 .xmm0),
   .movImm64 .rax 1, .vop (.vmovq .xmm15 .rax),
   .vmovdquLoad .l128 .xmm14 (at_ .rdx 0), .vop (.vbin .vpshufb .l128 .xmm14 .xmm14 .xmm0),
   .mov .r10 (.reg .rsi), .alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .r10),
   .alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .rdi),
   .mov .rax (.reg .rdx), .mov .rdx (.reg .r8)]

def setup : List Instr := setupG ++ lows 8 ++ highs 8 ++ setupC

/-! ## The loops -/

/-- The power of the `k`-th load of a group, from `scratch`, into `xmm12`;
block `k` at `rdx + 16 k` into `xmm7`, as a field element (with `Y` added to
block 0); and their product added to the product. -/
def ghLoad (k : Nat) : List Instr :=
  ([.vmovdquLoad .l128 .xmm12 (at_ .r11 (16 * k)), .vmovdquLoad .l128 .xmm7 (at_ .rdx (16 * k)),
   .vop (.vbin .vpshufb .l128 .xmm7 .xmm7 .xmm0)] : List Instr) ++
  (if k = 0 then [.vop (.vbin .vpxor .l128 .xmm7 .xmm7 .xmm2)] else []) ++ acc .xmm7 .xmm12

/-- The counter blocks: each block register gets the counter, byte-reversed,
and the counter is incremented (`inc₃₂`). -/
def ctrs : List XReg → List Instr
  | [] => []
  | b :: bs => ([.vop (.vbin .vpshufb .l128 b .xmm14 .xmm0), .vop (.vbin .vpaddd .l128 .xmm14 .xmm14 .xmm15)] : List Instr) ++
      ctrs bs

/-- XOR block register `i` into the data block `rdx + 16 (j + i)`. -/
def xorData : List XReg → Nat → List Instr
  | [], _ => []
  | b :: bs, j => ([.vbinLoad .vpxor .l128 b b (at_ .rdx (16 * j)),
      .vmovdquStore .l128 (at_ .rdx (16 * j)) b] : List Instr) ++ xorData bs (j + 1)

/-- Four blocks encrypted into the data blocks `j`… at `rdx + 16 j`, the
GHASH work `g i` after round `i`. -/
def batch (j : Nat) (g : Nat → List Instr) : Prog isa :=
  .seq (.block (ctrs aregs)) (.seq (aesL .l128 .xmm13 aregs g) (.block (xorData aregs j)))

/-- The order of the GHASH loads of an encryption group: the product with `Y`
last. -/
def ordE (i : Nat) : Nat := (i + 1) % 16

/-- The order of the GHASH loads of a decryption group: each batch's own
blocks, the product with `Y` last of the first batch. -/
def ordD (i : Nat) : Nat := if i < 3 then i + 1 else if i = 3 then 0 else i

/-- The GHASH work between the rounds of a batch: loads `base … base + 3` of
the order `ord` after rounds 1–4, and, if `fin`, the reduction into `Y`
after round 5. -/
def gq (ord : Nat → Nat) (base : Nat) (fin : Bool) (j : Nat) : List Instr :=
  if 1 ≤ j ∧ j ≤ 4 then ghLoad (ord (base + j - 1))
  else if fin ∧ j = 5 then reduceHash else []

/-- Four batches, the GHASH work of the order `ord` between their rounds,
encrypting the blocks `j`… at `rdx + 16 j`. -/
def group (ord : Nat → Nat) (j : Nat) : Prog isa :=
  .seq (batch j (gq ord 0 false))
    (.seq (batch (j + 4) (gq ord 4 false))
      (.seq (batch (j + 8) (gq ord 8 false)) (batch (j + 12) (gq ord 12 true))))

/-- The first group, encrypted only. -/
def first : Prog isa :=
  .seq (batch 0 fun _ => []) (.seq (batch 4 fun _ => []) (.seq (batch 8 fun _ => []) (batch 12 fun _ => [])))

/-- A group encrypted (at `rdx + 256`) and the previous one hashed (at `rdx`). -/
def body : Prog isa :=
  .seq (.block zero)
    (.seq (group ordE 16)
      (.block [.alu .add .rdx (.imm 256), .alu .sub .r9 (.imm 16), .alu .cmp .r9 (.imm 32)]))

/-- The last group hashed, at `rdx`. -/
def lastG : List Instr :=
  zero ++ (List.range 16).flatMap (fun i => ghLoad (ordE i)) ++ reduceHash

/-- `n` (a multiple of 16, at least 16) blocks. -/
def enc : Prog isa :=
  .seq (.block setup)
    (.seq first
      (.seq (.block [.alu .cmp .r9 (.imm 32)])
        (.seq (.ite .b (.block []) (.loop body .ae))
          (.block (Stitch.storeCtr ++ lastG ++ Stitch.storeY)))))

/-- A group hashed and decrypted, at `rdx`. -/
def dbody : Prog isa :=
  .seq (.block zero)
    (.seq (group ordD 0)
      (.block [.alu .add .rdx (.imm 256), .alu .sub .r9 (.imm 16), .alu .cmp .r9 (.imm 16)]))

/-- `n` (a multiple of 16, at least 16) blocks. -/
def dec : Prog isa :=
  .seq (.block setup) (.seq (.loop dbody .ae) (.block (Stitch.storeCtr ++ Stitch.storeY)))

end VG.Impl.Gcm.X86_64.StitchAvx
