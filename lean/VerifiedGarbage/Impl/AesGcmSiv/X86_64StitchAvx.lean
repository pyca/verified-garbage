module

public import VerifiedGarbage.Impl.AesGcmSiv.X86_64Stitch
public import VerifiedGarbage.Impl.Gcm.X86_64.StitchAvx8

/-!
# AES-GCM-SIV's loops on the groups with AES-NI, PCLMULQDQ and AVX

The loops `Impl.AesGcmSiv.X86_64Stitch.«open»` and `«seal»` run on the
data's 256-byte groups (`X86_64Stitch.Loops`), on 128-bit registers
(`VEX.128`), for CPUs without VAES or VPCLMULQDQ, with the registers and
contracts of the 256-bit ones (`X86_64Stitch.dec`, `hash`, `ctr`):

* `dec`: each group of sixteen blocks deciphered in counter mode, eight
  blocks a batch, while the plaintext of the group before is absorbed into
  `Y` between the rounds of the batches, eight blocks a batch (`batch`,
  `body`), as `X86_64Stitch.dec` does; the last group's plaintext then alone
  (`lastG`).
* `hash`: the groups absorbed, eight blocks at a time (`hbody`).
* `ctr`: the groups enciphered, eight blocks at a time (`cbody`).

Eight blocks are hashed with the powers `H'⁸ … H'` (`x · H'ᵏ = Hᵏ`, as
AES-GCM's eight-state loop, `Impl.Gcm.X86_64.StitchAvx8`, computes them,
`setupG`) and one reduction into `Y`. POLYVAL is GHASH with the key `H · x`
on blocks in the other byte order (`Proof.GcmSiv.Polyval`), and GHASH's
loads reverse each block's bytes into the register form, so POLYVAL's loads
are the data's 16 bytes as they are (`ghA`). The counter block of RFC 8452
§4 increments its first 32-bit word, little-endian: `vpaddd` of 1 on the
block as it is (`ctrs`).

Registers: `xmm0`, `xmm3`–`xmm6` and `xmm13`–`xmm15` the eight blocks being
deciphered (`StitchAvx8.aregs`), `xmm1` the round key, `xmm2` `Y` (in
GHASH's order), `xmm7` a block being hashed, `xmm8`–`xmm10` the products,
`xmm11` a temporary, `xmm12` a power (and the reduction constant, and 1 for
the counters). `rdi` points to the key schedule, `rsi` holds `rounds`,
`r10` the last round key's address; `rdx` points to the counter block at
entry, then to the group being hashed, and `rax` to the counter block,
which each batch reads and advances; `rcx` to `Y`, `r8` to `H`, `r11` to the
working space (256 bytes: the powers from `r11`, `H'⁸` first, 1 at
`r11 + 128` and the reduction constant at `r11 + 144`), `r9` counts the
blocks.
-/

@[expose] public section

namespace VG.Impl.AesGcmSiv.X86_64StitchAvx

open VG.X86_64
open VG.Impl.Gcm.X86_64.Pclmul (at_ revMask poly constImm hInvImm mul)
open VG.Impl.Gcm.X86_64.StitchAvx8 (aregs accInit acc xorData)

/-- Where 1 (in the first 32-bit word) is, in the working space. -/
def oneO : Nat := 128

/-- Where the reduction constant is, in the working space. -/
def polyO : Nat := 144

/-- The register of `H'ⁱ⁺¹` after `setupG`. -/
abbrev preg : Nat → XReg := VG.Impl.Gcm.X86_64.StitchAvx.preg

/-! ## The setup -/

/-- The mask into `xmm0`, the reduction constant into `xmm1`, `H` from `r8`
into GHASH's order, and `H'` … `H'⁸` into `preg 0` … `preg 7` (the SSE
code of `StitchAvx8.setupG`, from `r8`). -/
def setupG : List Instr :=
  constImm .xmm0 revMask ++ constImm .xmm1 poly ++
  [.movdquLoad .xmm7 (at_ .r8 0), .xop (.bin .pshufb .xmm7 .xmm0)] ++ hInvImm ++
  mul (preg 1) (preg 0) (preg 0) ++ mul (preg 2) (preg 1) (preg 0) ++
  mul (preg 3) (preg 1) (preg 1) ++ mul (preg 4) (preg 3) (preg 0) ++
  mul (preg 5) (preg 3) (preg 1) ++ mul (preg 6) (preg 3) (preg 2) ++
  mul (preg 7) (preg 3) (preg 3)

/-- The powers stored, `H'⁸⁻ᵏ` at `r11 + 16 k`, and the reduction constant
at `r11 + polyO`. -/
def stores : List Instr :=
  (List.range 8).map (fun k => .movdquStore (at_ .r11 (16 * k)) (preg (7 - k))) ++
  [.movdquStore (at_ .r11 polyO) .xmm1]

/-- 1 stored at `r11 + oneO`, through `r10` and `xmm11`. -/
def storeOne : List Instr :=
  [.mov32 .r10 (.imm 1), .xop (.movq .xmm11 .r10), .movdquStore (at_ .r11 oneO) .xmm11]

/-- `Y` from `rcx` into GHASH's order. -/
def loadY : List Instr := [.movdquLoad .xmm2 (at_ .rcx 0), .xop (.bin .pshufb .xmm2 .xmm0)]

/-- The last round key's address, the counter block's address in `rax` and
the data's in `rdx`. -/
def setupC : List Instr :=
  [.mov .r10 (.reg .rsi), .shift .shl .r10 4, .alu .add .r10 (.reg .rdi),
   .mov .rax (.reg .rdx), .mov .rdx (.reg .r12)]

def setup : List Instr := setupG ++ stores ++ storeOne ++ loadY ++ setupC

/-! ## A batch -/

/-- The counter blocks: each block register gets the counter `c` as it is,
and the counter advances by `i` (1 in its first word). -/
def ctrsR (c i : XReg) : List XReg → List Instr
  | [] => []
  | b :: bs => ([.vop (.vmovdqa .l128 b c), .vop (.vbin .vpaddd .l128 c c i)] : List Instr) ++ ctrsR c i bs

/-- The eight counter blocks of a batch from the counter block at `rax`, which
is advanced by eight. -/
def ctrs : List Instr :=
  [.vmovdquLoad .l128 .xmm11 (at_ .rax 0), .vmovdquLoad .l128 .xmm12 (at_ .r11 oneO)] ++
  ctrsR .xmm11 .xmm12 aregs ++ [.vmovdquStore .l128 (at_ .rax 0) .xmm11]

/-- Eight blocks deciphered at `rdx + 16 j`, the instructions `g i` after
round `i`. -/
def batch (j : Nat) (g : Nat → List Instr) : Prog isa :=
  .seq (.block ctrs) (.seq (Aes.X86_64.Vaes.aesL .l128 .xmm1 aregs g) (.block (xorData false aregs j)))

/-! ## POLYVAL -/

/-- Block `k` of the eight at `rdx + d`, as it is, with `Y` added to block 0,
into `xmm7`, and its product with the power `H'⁸⁻ᵏ` added to the
accumulators (which block 1, the first, starts). -/
def ghA (d k : Nat) : List Instr :=
  [.vmovdquLoad .l128 .xmm12 (at_ .r11 (16 * k)), .vmovdquLoad .l128 .xmm7 (at_ .rdx (d + 16 * k))] ++
  (if k = 0 then [.vop (.vbin .vpxor .l128 .xmm7 .xmm7 .xmm2)] else []) ++
  (if k = 1 then accInit .xmm7 .xmm12 else acc .xmm7 .xmm12)

/-- The products reduced into `Y` (`StitchAvx8.reduceFinal`, with the
reduction constant in `xmm12`). -/
def red : List Instr :=
  [.vmovdquLoad .l128 .xmm12 (at_ .r11 polyO),
   .vop (.vpclmulqdq .l128 .xmm11 .xmm8 .xmm12 0x10),
   .vop (.vpshufd .l128 .xmm8 .xmm8 0x4e),
   .vop (.vbin .vpxor .l128 .xmm9 .xmm9 .xmm8),
   .vop (.vbin .vpxor .l128 .xmm9 .xmm9 .xmm11),
   .vop (.vpclmulqdq .l128 .xmm11 .xmm9 .xmm12 0x10),
   .vop (.vpshufd .l128 .xmm9 .xmm9 0x4e),
   .vop (.vbin .vpxor .l128 .xmm2 .xmm10 .xmm9),
   .vop (.vbin .vpxor .l128 .xmm2 .xmm2 .xmm11)]

/-- The POLYVAL work after round `j` of a batch, on the eight blocks at
`rdx + d`: their loads in the order 1, …, 7, 0 after rounds 1 to 8, the
reduction after round 9. -/
def q (d j : Nat) : List Instr :=
  if 1 ≤ j ∧ j ≤ 8 then ghA d (j % 8) else if j = 9 then red else []

/-- The eight blocks at `rdx + d` absorbed. -/
def hash8 (d : Nat) : List Instr := (List.range 8).flatMap (fun i => ghA d ((i + 1) % 8)) ++ red

/-! ## `dec` -/

/-- The first group, deciphered only. -/
def first : Prog isa := .seq (batch 0 fun _ => []) (batch 8 fun _ => [])

/-- A group deciphered (at `rdx + 256`) and the previous one hashed (at
`rdx`). -/
def body : Prog isa :=
  .seq (batch 16 (q 0))
    (.seq (batch 24 (q 128))
      (.block [.alu .add .rdx (.imm 256), .alu .sub .r9 (.imm 16), .alu .cmp .r9 (.imm 32)]))

/-- The last group, at `rdx`, hashed. -/
def lastG : List Instr := hash8 0 ++ hash8 128

/-- `Y` stored in GHASH's order (the mask into `xmm0`, through `rax`). -/
def storeY : List Instr :=
  constImm .xmm0 revMask ++ [.vop (.vbin .vpshufb .l128 .xmm2 .xmm2 .xmm0), .vmovdquStore .l128 (at_ .rcx 0) .xmm2]

/-- `r9` (a multiple of 16, at least 16) blocks at `r12` deciphered and their
plaintext absorbed into `Y`. -/
def dec : Prog isa :=
  .seq (.block setup)
    (.seq first
      (.seq (.block [.alu .cmp .r9 (.imm 32)])
        (.seq (.ite .b (.block []) (.loop body .ae))
          (.block (lastG ++ storeY)))))

/-! ## `hash` -/

/-- A group of sixteen blocks at `rdx` absorbed; `rdx` on, `r9` down. -/
def hbody : List Instr := lastG ++ ([.alu .add .rdx (.imm 256), .alu .sub .r9 (.imm 16)] : List Instr)

/-- `r9` (a multiple of 16, at least 16) blocks at `rdx` absorbed into `Y` at
`rcx`, with the powers of `H` at `r8` in the working space at `r11`. -/
def hash : Prog isa :=
  .seq (.block (setupG ++ stores ++ loadY)) (.seq (.loop (.block hbody) .ne) (.block storeY))

/-! ## `ctr` -/

/-- A group of sixteen blocks at `rdx` enciphered; `rdx` on, `r9` down. -/
def cbody : Prog isa :=
  .seq (batch 0 fun _ => []) (.seq (batch 8 fun _ => [])
    (.block [.alu .add .rdx (.imm 256), .alu .sub .r9 (.imm 16)]))

/-- `r9` (a multiple of 16, at least 16) blocks at `r12` enciphered in counter
mode from the counter block at `rdx`, which is advanced. -/
def ctr : Prog isa :=
  .seq (.block (storeOne ++ setupC)) (.loop cbody .ne)

/-- The loops with AES-NI, PCLMULQDQ and AVX. -/
def loops : X86_64Stitch.Loops := ⟨dec, hash, ctr⟩

end VG.Impl.AesGcmSiv.X86_64StitchAvx
