import VerifiedGarbage.Impl.Gcm.X86_64.Stitch
import VerifiedGarbage.Impl.Aes.X86_64.VaesZ

/-!
# AES-GCM's counter mode and GHASH, interleaved, with AVX-512 VAES and VPCLMULQDQ

The loops of `vg_aes_gcm_encrypt_blocks` and `_decrypt_blocks` for CPUs with
AVX-512 (AVX512F and AVX512BW), VAES and VPCLMULQDQ, on groups of sixteen
blocks: `(ctx = rdi, rounds = rsi, counter = rdx, y = rcx, data = r8, n = r9,
scratch = r11)`, as `Impl.Gcm.X86_64.Stitch` does with 256-bit registers.

The setup is `Stitch.setup`: the powers `H'`–`H'¹⁶`, stored to `scratch` in
pairs (`H'¹⁶⁻²ᵏ`, `H'¹⁵⁻²ᵏ` at `scratch + 32 k`), so that the 64 bytes at
`scratch + 64 k` are the four powers `H'¹⁶⁻⁴ᵏ` … `H'¹³⁻⁴ᵏ` that the `k`-th
512-bit load of a group multiplies; then (`setupZ`) the counter pair
becomes four counters in the lanes of `zmm14`, the increment 4 in each lane
of `zmm15`, and the byte-reversal mask is copied to the four lanes of `zmm0`.

A group is one batch of sixteen blocks in the four lanes of `zmm3`–`zmm6`.
The GHASH of the previous group (when encrypting) or of the group itself
(when decrypting, before the blocks are overwritten) is placed between its
rounds: four 512-bit loads, of blocks `4k`–`4k + 3` with their powers in
`zmm12`, after rounds 1–4 (the product with `Y` last); each lane accumulates
its products in `zmm8`–`zmm10` with the EVEX.512 forms of `vg_ghash_pclmul`'s
instructions. After round 5 the four lanes are added into two (`foldLanes`,
whose VEX.256 `vpxor` clears the upper lanes) and reduced as
`vg_ghash_vpclmul` reduces its two (`Vpclmul.reduce`, `Vpclmul.combine`).

Registers: `zmm0` the byte-reversal mask, `ymm1` the reduction constant,
`xmm2` `Y`, `zmm3`–`zmm6` sixteen blocks being encrypted, `zmm7` four blocks
being hashed, `zmm8`–`zmm11` the products and a temporary, `zmm12` four
powers, `zmm13` a round key, `zmm14` the four counters and `zmm15` the
increment. `rdx` points to the group being hashed, `rax` to the counter,
`r10` to the last round key, `r11` to `scratch`. `vzeroupper` clears the
upper lanes at the end.
-/

namespace VG.Impl.Gcm.X86_64.StitchZ

open VG.X86_64
open VG.Impl.Gcm.X86_64.Pclmul (at_)
open VG.Impl.Gcm.X86_64.Vpclmul (zero reduce combine)
open VG.Impl.Gcm.X86_64.Stitch (aregs storeCtr storeY)
open VG.Impl.Aes.X86_64.VaesZ (aesZ ctrsZ xorDataZ)

/-- Sixteen blocks encrypted into the data blocks at `rdx + 64 j`, the GHASH
work `g i` after round `i`. -/
def batch (j : Nat) (g : Nat → List Instr) : Prog isa :=
  .seq (.block (ctrsZ .xmm14 .xmm0 .xmm15 aregs)) (.seq (aesZ .xmm13 aregs g) (.block (xorDataZ .xmm13 .rdx aregs j)))

/-- Add the carry-less products of the lanes of `a` and `b` to `lo`, `mid`,
`hi`. -/
def acc (a b : XReg) : List Instr :=
  [.zop (.vpclmulqdq .xmm11 a b 0x00), .zop (.zbin .vpxord .xmm8 .xmm8 .xmm11),
   .zop (.vpclmulqdq .xmm11 a b 0x11), .zop (.zbin .vpxord .xmm10 .xmm10 .xmm11),
   .zop (.vpclmulqdq .xmm11 a b 0x01), .zop (.zbin .vpxord .xmm9 .xmm9 .xmm11),
   .zop (.vpclmulqdq .xmm11 a b 0x10), .zop (.zbin .vpxord .xmm9 .xmm9 .xmm11)]

/-- The `k`-th load of a group: four powers from `scratch + 64 k` into
`zmm12`, blocks `4k`–`4k + 3` at `rdx + 64 k` into the lanes of `zmm7` as
field elements (with `Y` added to block 0), and their products. -/
def ghLoad (k : Nat) : List Instr :=
  [.vmovdqu32Load .xmm12 (at_ .r11 (64 * k)), .vmovdqu32Load .xmm7 (at_ .rdx (64 * k)),
   .zop (.zbin .vpshufb .xmm7 .xmm7 .xmm0)] ++
  (if k = 0 then [.zop (.zbin .vpxord .xmm7 .xmm7 .xmm2)] else []) ++ acc .xmm7 .xmm12

/-- The order of the loads: the product with `Y` last. -/
def ord : Nat → Nat
  | 0 => 1 | 1 => 2 | 2 => 3 | _ => 0

/-- Lanes 2 and 3 of the products added to lanes 0 and 1 (`VEX.256`, which
clears the upper lanes). -/
def foldLanes : List Instr :=
  [.zop (.vshufi32x4 .xmm11 .xmm8 .xmm8 0x0e), .vop (.vbin .vpxor .l256 .xmm8 .xmm8 .xmm11),
   .zop (.vshufi32x4 .xmm11 .xmm9 .xmm9 0x0e), .vop (.vbin .vpxor .l256 .xmm9 .xmm9 .xmm11),
   .zop (.vshufi32x4 .xmm11 .xmm10 .xmm10 0x0e), .vop (.vbin .vpxor .l256 .xmm10 .xmm10 .xmm11)]

/-- The sum of the four lanes' products, reduced, into `Y`. -/
def fin : List Instr := foldLanes ++ reduce .xmm7 ++ combine

/-- The GHASH work between the rounds of a group: the loads after rounds
1–4, the reduction after round 5. -/
def gq (j : Nat) : List Instr :=
  if 1 ≤ j ∧ j ≤ 4 then ghLoad (ord (j - 1)) else if j = 5 then fin else []

/-- Four counters, the increment and the mask in the four lanes, from the
two of `Stitch.setupC`, and the upper lanes of `Y` cleared. -/
def setupZ : List Instr :=
  [.vop (.vbin .vpaddd .l256 .xmm13 .xmm14 .xmm15), .zop (.vshufi32x4 .xmm14 .xmm14 .xmm13 0x44),
   .vop (.vbin .vpaddd .l256 .xmm15 .xmm15 .xmm15), .zop (.vshufi32x4 .xmm15 .xmm15 .xmm15 0x44),
   .zop (.vshufi32x4 .xmm0 .xmm0 .xmm0 0x44), .vop (.vmovdqa .l128 .xmm2 .xmm2)]

def setup : List Instr := Stitch.setup ++ setupZ

/-- The first group, encrypted only. -/
def first : Prog isa := batch 0 fun _ => []

/-- A group encrypted (at `rdx + 256`) and the previous one hashed (at `rdx`). -/
def body : Prog isa :=
  .seq (.block zero)
    (.seq (batch 4 gq) (.block [.alu .add .rdx (.imm 256), .alu .sub .r9 (.imm 16), .alu .cmp .r9 (.imm 32)]))

/-- The last group hashed, at `rdx`. -/
def lastG : List Instr := zero ++ (List.range 4).flatMap (fun i => ghLoad (ord i)) ++ fin

/-- `n` (a multiple of 16, at least 16) blocks. -/
def enc : Prog isa :=
  .seq (.block setup)
    (.seq first
      (.seq (.block [.alu .cmp .r9 (.imm 32)])
        (.seq (.ite .b (.block []) (.loop body .ae))
          (.block (storeCtr ++ lastG ++ storeY)))))

/-- A group hashed and decrypted, at `rdx`. -/
def dbody : Prog isa :=
  .seq (.block zero)
    (.seq (batch 0 gq) (.block [.alu .add .rdx (.imm 256), .alu .sub .r9 (.imm 16), .alu .cmp .r9 (.imm 16)]))

/-- `n` (a multiple of 16, at least 16) blocks. -/
def dec : Prog isa :=
  .seq (.block setup)
    (.seq (.loop dbody .ae)
      (.block (storeCtr ++ storeY)))

end VG.Impl.Gcm.X86_64.StitchZ
