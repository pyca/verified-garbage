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
of `zmm15`, and the byte-reversal mask and the reduction constant are copied
to the four lanes of `zmm0` and `zmm1`.

A group is one batch of sixteen blocks in the four lanes of `zmm3`–`zmm6`.
The GHASH of the previous group (when encrypting) or of the group itself
(when decrypting, before the blocks are overwritten) is placed between its
rounds: four 512-bit loads, of blocks `4k`–`4k + 3` with their powers in
`zmm12`, after rounds 1–4 (the product with `Y` last); each lane's products
go to `zmm8`–`zmm10` (`lo`, `mid`, `hi`): the first load's are written there
(`accInit`), the others' added (`acc`, which adds both middle products with
one `vpternlogd`). After round 5 each lane's product is reduced (`reduceZ`:
`lo` folded into `mid` and `mid` into `hi`, each by one step of
`vg_ghash_pclmul`'s reduction, `Pclmul.reduceB`), lanes 2 and 3 are added to
0 and 1 (whose VEX.256 `vpxor` clears the upper lanes) and those two into
`Y` (`combine10`).

Registers: `zmm0` the byte-reversal mask, `zmm1` the reduction constant,
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
open VG.Impl.Gcm.X86_64.Stitch (aregs storeCtr storeY)
open VG.Impl.Aes.X86_64.VaesZ (aesZ ctrsZ xorDataZ)

/-- Sixteen blocks encrypted into the data blocks at `rdx + 64 j`, the GHASH
work `g i` after round `i`. -/
def batch (j : Nat) (g : Nat → List Instr) : Prog isa :=
  .seq (.block (ctrsZ .xmm14 .xmm0 .xmm15 aregs)) (.seq (aesZ .xmm13 aregs g) (.block (xorDataZ .xmm13 .rdx aregs j)))

/-- The carry-less products of the lanes of `a` and `b`, written to `lo`,
`mid`, `hi`. -/
def accInit (a b : XReg) : List Instr :=
  [.zop (.vpclmulqdq .xmm8 a b 0x00), .zop (.vpclmulqdq .xmm10 a b 0x11),
   .zop (.vpclmulqdq .xmm9 a b 0x01), .zop (.vpclmulqdq .xmm11 a b 0x10),
   .zop (.zbin .vpxord .xmm9 .xmm9 .xmm11)]

/-- Add the carry-less products of the lanes of `a` and `b` to `lo`, `mid`,
`hi` (overwriting `a` with the last one). -/
def acc (a b : XReg) : List Instr :=
  [.zop (.vpclmulqdq .xmm11 a b 0x00), .zop (.zbin .vpxord .xmm8 .xmm8 .xmm11),
   .zop (.vpclmulqdq .xmm11 a b 0x11), .zop (.zbin .vpxord .xmm10 .xmm10 .xmm11),
   .zop (.vpclmulqdq .xmm11 a b 0x01), .zop (.vpclmulqdq a a b 0x10),
   .zop (.vpternlogd .xmm9 .xmm11 a 0x96)]

/-- The order of the loads: the product with `Y` last. -/
def ord : Nat → Nat
  | 0 => 1 | 1 => 2 | 2 => 3 | _ => 0

/-- The `k`-th load of a group: four powers from `scratch + 64 k` into
`zmm12`, blocks `4k`–`4k + 3` at `rdx + 64 k` into the lanes of `zmm7` as
field elements (with `Y` added to block 0), and their products (written, for
the first load, `ord 0`). -/
def ghLoad (k : Nat) : List Instr :=
  ([.vmovdqu32Load .xmm12 (at_ .r11 (64 * k)), .vmovdqu32Load .xmm7 (at_ .rdx (64 * k)),
   .zop (.zbin .vpshufb .xmm7 .xmm7 .xmm0)] : List Instr) ++
  (if k = 0 then [.zop (.zbin .vpxord .xmm7 .xmm7 .xmm2)] else []) ++
  (if k = ord 0 then accInit .xmm7 .xmm12 else acc .xmm7 .xmm12)

/-- Each lane's product reduced into `hi` (`Pclmul.reduceB`): `lo` folded
into `mid`, then `mid` into `hi`. -/
def reduceZ : List Instr :=
  [.zop (.vpclmulqdq .xmm11 .xmm8 .xmm1 0x10), .zop (.vpshufd .xmm8 .xmm8 0x4e),
   .zop (.vpternlogd .xmm9 .xmm8 .xmm11 0x96),
   .zop (.vpclmulqdq .xmm11 .xmm9 .xmm1 0x10), .zop (.vpshufd .xmm9 .xmm9 0x4e),
   .zop (.vpternlogd .xmm10 .xmm9 .xmm11 0x96)]

/-- Lanes 2 and 3 of `zmm10` added to lanes 0 and 1 (`VEX.256`, which clears
the upper lanes). -/
def foldLanes : List Instr :=
  [.zop (.vshufi32x4 .xmm11 .xmm10 .xmm10 0x0e), .vop (.vbin .vpxor .l256 .xmm10 .xmm10 .xmm11)]

/-- The two lanes of `ymm10` added into `Y` (`VEX.128`). -/
def combine10 : List Instr :=
  [.vop (.vextracti128 .xmm11 .xmm10 1), .vop (.vbin .vpxor .l128 .xmm2 .xmm10 .xmm11)]

/-- The four lanes' products, reduced and added, into `Y`. -/
def fin : List Instr := reduceZ ++ foldLanes ++ combine10

/-- The GHASH work between the rounds of a group: the loads after rounds
1–4, the reduction after round 5. -/
def gq (j : Nat) : List Instr :=
  if 1 ≤ j ∧ j ≤ 4 then ghLoad (ord (j - 1)) else if j = 5 then fin else []

/-- Four counters, the increment, the mask and the reduction constant in the
four lanes, from the two of `Stitch.setupC`, and the upper lanes of `Y`
cleared. -/
def setupZ : List Instr :=
  [.vop (.vbin .vpaddd .l256 .xmm13 .xmm14 .xmm15), .zop (.vshufi32x4 .xmm14 .xmm14 .xmm13 0x44),
   .vop (.vbin .vpaddd .l256 .xmm15 .xmm15 .xmm15), .zop (.vshufi32x4 .xmm15 .xmm15 .xmm15 0x44),
   .zop (.vshufi32x4 .xmm0 .xmm0 .xmm0 0x44), .zop (.vshufi32x4 .xmm1 .xmm1 .xmm1 0x44),
   .vop (.vmovdqa .l128 .xmm2 .xmm2)]

def setup : List Instr := Stitch.setup ++ setupZ

/-- The first group, encrypted only. -/
def first : Prog isa := batch 0 fun _ => []

/-- A group encrypted (at `rdx + 256`) and the previous one hashed (at `rdx`). -/
def body : Prog isa :=
  .seq (batch 4 gq) (.block [.alu .add .rdx (.imm 256), .alu .sub .r9 (.imm 16), .alu .cmp .r9 (.imm 32)])

/-- The last group hashed, at `rdx`. -/
def lastG : List Instr := (List.range 4).flatMap (fun i => ghLoad (ord i)) ++ fin

/-! ## Forty-eight blocks at a time

From 256 blocks on, the loops do three groups at a time: the GHASH of each
group is added (not reduced) to the products of the two before, with the
powers `H'⁴⁸`–`H'³³`, `H'³²`–`H'¹⁷` and `H'¹⁶`–`H'` (at `scratch + 512`,
`+ 256` and `+ 0`, `pow48` computes the first two from the third), and the
sum is reduced once, after the third group's round 6 (`gq48`). The loads go
in pairs (`pair`), whose products are added with one `vpternlogd` each:
`zmm1` and `zmm13` (which the next round reloads) hold the second load and
its powers, and `zmm2` a product, so `Y` is added to the first pair of the
first group, and the reduction constant is reloaded from `scratch + 832`
before the reduction. When encrypting, the groups hashed are
the three encrypted in the iteration before (`body48`), so that their
ciphertext is not read back right after it is written: the two groups after
the first are encrypted first (`big`), and the two still to be hashed after
the loop are hashed one at a time (`lastG`), leaving one, as the 16-block
loop does. -/

/-- The offset in `scratch` of the powers of group `g` of three. -/
def tab (g : Nat) : Nat := 512 - 256 * g

/-- The products of a pair into `lo` (`zmm8`), `mid` (`zmm9`) and `hi`
(`zmm10`): `sel` picks the halves, through `zmm11` and `zmm2`; the first
pair (`first`) writes them, the others add both with one `vpternlogd`. -/
def prodPair (first : Bool) (d : XReg) (selA selB : BitVec 8) (a pa b pb : XReg) : List Instr :=
  [.zop (.vpclmulqdq .xmm11 a pa selA), .zop (.vpclmulqdq .xmm2 b pb selB),
   if first then .zop (.zbin .vpxord d .xmm11 .xmm2) else .zop (.vpternlogd d .xmm11 .xmm2 0x96)]

/-- The lane-wise instructions of a pair: both loads byte-reversed (with `Y`
added to the first, for the first pair), and the products of `zmm7` with
`zmm12` and of `zmm1` with `zmm13`. -/
def pairZ (first : Bool) : List Instr :=
  ([.zop (.zbin .vpshufb .xmm7 .xmm7 .xmm0)] : List Instr) ++ (if first then [.zop (.zbin .vpxord .xmm7 .xmm7 .xmm2)] else []) ++
  ([.zop (.zbin .vpshufb .xmm1 .xmm1 .xmm0)] : List Instr) ++
  prodPair first .xmm8 0x00 0x00 .xmm7 .xmm12 .xmm1 .xmm13 ++
  prodPair first .xmm10 0x11 0x11 .xmm7 .xmm12 .xmm1 .xmm13 ++
  prodPair first .xmm9 0x01 0x10 .xmm7 .xmm12 .xmm7 .xmm12 ++
  prodPair false .xmm9 0x01 0x10 .xmm1 .xmm13 .xmm1 .xmm13

/-- Loads `ka` and `kb` of group `g` (at `rdx + 256 g`) into `zmm7` and
`zmm1`, their powers into `zmm12` and `zmm13`, and their products. -/
def pair (ka kb g : Nat) (first : Bool) : List Instr :=
  ([.vmovdqu32Load .xmm12 (at_ .r11 (tab g + 64 * ka)), .vmovdqu32Load .xmm7 (at_ .rdx (256 * g + 64 * ka)),
   .vmovdqu32Load .xmm13 (at_ .r11 (tab g + 64 * kb)), .vmovdqu32Load .xmm1 (at_ .rdx (256 * g + 64 * kb))] : List Instr) ++
  pairZ first

/-- The reduction constant reloaded, and the reduction into `Y`. -/
def fin48 : List Instr := .vmovdqu32Load .xmm1 (at_ .r11 832) :: fin

/-- The GHASH work after round `j` of group `b` of three. -/
def gq48 (b j : Nat) : List Instr :=
  if j = 1 then pair 0 1 b (decide (b = 0)) else if j = 3 then pair 2 3 b false
  else if b = 2 ∧ j = 6 then fin48 else []

/-- The powers of `zmm7` (four, from `scratch + 64 k`) times `zmm12`, in
each lane, stored to `scratch + d + 64 k`. -/
def powLoad (d k : Nat) : List Instr :=
  .vmovdqu32Load .xmm7 (at_ .r11 (64 * k)) :: (accInit .xmm7 .xmm12 ++ reduceZ ++
    ([.vmovdqu32Store (at_ .r11 (d + 64 * k)) .xmm10] : List Instr))

/-- `H'³²`–`H'¹⁷` and `H'⁴⁸`–`H'³³`: the powers at `scratch` times `H'¹⁶`
(lane 0 of the first load), then times `H'³²`; and the reduction
constant, saved. -/
def pow48 : List Instr :=
  ([.vbroadcasti32x4 .xmm12 (at_ .r11 0)] : List Instr) ++ (List.range 4).flatMap (powLoad 256) ++
  ([.vbroadcasti32x4 .xmm12 (at_ .r11 256)] : List Instr) ++ (List.range 4).flatMap (powLoad 512) ++
  ([.vmovdqu32Store (at_ .r11 832) .xmm1] : List Instr)

/-- Three groups encrypted (at `rdx + 768`) and the three before hashed (at
`rdx`). -/
def body48 : Prog isa :=
  .seq (batch 12 (gq48 0)) (.seq (batch 16 (gq48 1)) (.seq (batch 20 (gq48 2))
    (.block [.alu .add .rdx (.imm 768), .alu .sub .r9 (.imm 48), .alu .cmp .r9 (.imm 96)])))

/-- The next group. -/
def adv : List Instr := [.alu .add .rdx (.imm 256), .alu .sub .r9 (.imm 16)]

/-- At least 256 blocks, the first group encrypted: the powers, the next two
groups, the loop, and two of the three groups left to hash. -/
def big : Prog isa :=
  .seq (.block pow48) (.seq (batch 4 fun _ => []) (.seq (batch 8 fun _ => [])
    (.seq (.loop body48 .ae) (.block (.vmovdqu32Load .xmm1 (at_ .r11 832) :: (lastG ++ adv ++ lastG ++ adv))))))

/-- `n` (a multiple of 16, at least 16) blocks. -/
def enc : Prog isa :=
  .seq (.block setup)
    (.seq first
      (.seq (.block [.alu .cmp .r9 (.imm 256)])
        (.seq (.ite .b (.block []) big)
          (.seq (.block [.alu .cmp .r9 (.imm 32)])
            (.seq (.ite .b (.block []) (.loop body .ae))
              (.block (storeCtr ++ lastG ++ storeY)))))))

/-- A group hashed and decrypted, at `rdx`. -/
def dbody : Prog isa :=
  .seq (batch 0 gq) (.block [.alu .add .rdx (.imm 256), .alu .sub .r9 (.imm 16), .alu .cmp .r9 (.imm 16)])

/-- Three groups hashed and decrypted, at `rdx`. -/
def dbody48 : Prog isa :=
  .seq (batch 0 (gq48 0)) (.seq (batch 4 (gq48 1)) (.seq (batch 8 (gq48 2))
    (.block [.alu .add .rdx (.imm 768), .alu .sub .r9 (.imm 48), .alu .cmp .r9 (.imm 48)])))

/-- At least 256 blocks: the powers, the loop, and the reduction constant
reloaded. -/
def bigD : Prog isa :=
  .seq (.block pow48) (.seq (.loop dbody48 .ae) (.block [.vmovdqu32Load .xmm1 (at_ .r11 832)]))

/-- `n` (a multiple of 16, at least 16) blocks. -/
def dec : Prog isa :=
  .seq (.block setup)
    (.seq (.block [.alu .cmp .r9 (.imm 256)])
      (.seq (.ite .b (.block []) bigD)
        (.seq (.block [.alu .cmp .r9 (.imm 16)])
          (.seq (.ite .b (.block []) (.loop dbody .ae))
            (.block (storeCtr ++ storeY))))))

end VG.Impl.Gcm.X86_64.StitchZ
