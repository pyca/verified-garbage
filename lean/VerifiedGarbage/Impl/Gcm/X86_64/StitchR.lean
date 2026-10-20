module

public import VerifiedGarbage.Impl.Gcm.X86_64.StitchTo
public import VerifiedGarbage.Impl.Gcm.X86_64.StitchZH

/-!
# The 256-bit interleaved loops, with the prepared powers of the hash subkey

`Stitch.enc`, `Stitch.dec` and `StitchTo.enc` for a prepared key context
(`VG.Spec.Gcm.PreparedPowersRepr`), which holds the powers `H'¹ … H'⁴⁸`
already in the representation the loops multiply by, in pairs: instead of
computing `H'`–`H'¹⁶` on every call (`Stitch.setupG`), the setup loads the
eight pairs `ymm3`–`ymm6`, `ymm12`–`ymm15` with one 256-bit load each
(`StitchZR.setupGP`, which needs no AVX-512). The rest is the loops'.
-/

@[expose] public section

namespace VG.Impl.Gcm.X86_64.StitchR

open VG.X86_64
open VG.Impl.Gcm.X86_64.Stitch (aregs storesK pregs setupC first body dbody storeCtr lastG storeY)
open VG.Impl.Aes.X86_64.Vaes (aesK ctrsK)
open VG.Impl.Gcm.X86_64.StitchZTo (setupCTo)

/-- `Stitch.setup` with the powers loaded. -/
def setup : List Instr := StitchZR.setupGP ++ storesK .r11 pregs 0 ++ setupC

/-- `Stitch.enc` with the powers loaded. -/
def enc : Prog isa :=
  .seq (.block setup)
    (.seq first
      (.seq (.block [.alu .cmp .r9 (.imm 32)])
        (.seq (.ite .b (.block []) (.loop body .ae))
          (.block (storeCtr ++ lastG ++ storeY)))))

/-- `Stitch.dec` with the powers loaded. -/
def dec : Prog isa :=
  .seq (.block setup)
    (.seq (.loop dbody .ae)
      (.block (storeCtr ++ storeY)))

/-- `StitchTo.setup` with the powers loaded. -/
def setupTo : List Instr := StitchZR.setupGP ++ storesK .r11 pregs 0 ++ setupCTo

/-- `StitchTo.enc` with the powers loaded. -/
def encTo : Prog isa :=
  .seq (.block setupTo)
    (.seq StitchTo.firstTo
      (.seq (.block [.alu .cmp .r9 (.imm 32)])
        (.seq (.ite .b (.block []) (.loop StitchTo.bodyTo .ae))
          (.block (storeCtr ++ lastG ++ storeY)))))

/-- `encTo` in one pass over the blocks at `src` (`r9` of them, a multiple of
16) and then, in place, over the whole groups after them at `dst`: after the
loop at `src`, `r8 ← rbx` (`dst`) and `r9 += rbp` (the number of blocks
after them at `dst`, a multiple of 16), and the in-place loop (`Stitch.body`) goes on from
the group the out-of-place one encrypted last, with one setup and one last
reduction for both. -/
def encN : Prog isa :=
  .seq (.block setupTo)
    (.seq StitchTo.firstTo
      (.seq (.block [.alu .cmp .r9 (.imm 32)])
        (.seq (.ite .b (.block []) (.loop StitchTo.bodyTo .ae))
          (.seq (.block [.mov .r8 (.reg .rbx), .alu .add .r9 (.reg .rbp), .alu .cmp .r9 (.imm 32)])
            (.seq (.ite .b (.block []) (.loop body .ae))
              (.block (storeCtr ++ lastG ++ storeY)))))))

/-! ## Decryption: the blocks after the last group -/

/-- The keystream of eight blocks, the next counters' in the lanes of
`ymm3`–`ymm6`, stored to `scratch + 32 j`. -/
def ks (j : Nat) : Prog isa :=
  .seq (.block (ctrsK .xmm14 .xmm0 .xmm15 aregs)) (.seq (aesK .xmm13 aregs) (.block (storesK .r11 aregs j)))

/-- `r10` at the last round key, `rdi + 16 rounds`, as `Stitch.setupC` sets it. -/
def keyEnd : List Instr :=
  [.mov .r10 (.reg .rsi), .alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .r10),
   .alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .rdi)]

/-- The keystream of the `r` blocks after the last group (`r10 = 16 r`), of
eight blocks, or sixteen if `r > 8`, to `scratch + 256`, with `r10` at the
last round key again for the rounds. -/
def ksSel : Prog isa :=
  .seq (.block [.alu .cmp .r10 (.imm 129)])
    (.ite .b (.seq (.block keyEnd) (ks 8)) (.seq (.block keyEnd) (.seq (ks 8) (ks 12))))

/-- Blocks `r10 / 16` and the next, as `StitchZH.remBodyD .rdx` does one, in
the two lanes: read at `rdx + r10`, their keystream added from
`r11 + r10 + 768` and stored back, and the blocks as read, byte-reversed and
with the lanes of `ymm2` added, multiplied by the powers at `rax + r10` and
added to the products in each lane of `ymm8`–`ymm10`; `ymm2` cleared. -/
def remPairD : List Instr :=
  ([.vmovdquLoad .l256 .xmm13 (StitchZTo.atIx .rdx .r10 0), .vmovdquLoad .l256 .xmm12 (StitchZTo.atIx .r11 .r10 768),
    .vop (.vbin .vpxor .l256 .xmm12 .xmm12 .xmm13), .vmovdquStore .l256 (StitchZTo.atIx .rdx .r10 0) .xmm12,
    .vmovdquLoad .l256 .xmm12 (StitchZTo.atIx .rax .r10 0),
    .vop (.vbin .vpshufb .l256 .xmm13 .xmm13 .xmm0), .vop (.vbin .vpxor .l256 .xmm13 .xmm13 .xmm2),
    .vop (.vbin .vpxor .l256 .xmm2 .xmm2 .xmm2)] : List Instr) ++ Vpclmul.acc .xmm13 .xmm12

/-- The next pair, and whether it is the last. -/
def remNextPair : List Instr := [.alu .add .r10 (.imm 32), .alu .sub .r9 (.imm 2), .alu .cmp .r9 (.imm 16)]

/-- The upper lanes of the products added into the lower lanes. -/
def foldLanes : List Instr :=
  [.vop (.vextracti128 .xmm11 .xmm8 1), .vop (.vbin .vpxor .l128 .xmm8 .xmm8 .xmm11),
   .vop (.vextracti128 .xmm11 .xmm9 1), .vop (.vbin .vpxor .l128 .xmm9 .xmm9 .xmm11),
   .vop (.vextracti128 .xmm11 .xmm10 1), .vop (.vbin .vpxor .l128 .xmm10 .xmm10 .xmm11)]

/-- The `r9 - 16` blocks at `rdx` after the last group, which the loop has
already hashed and decrypted: the counter after them stored and `rax` at
their powers (`StitchZH.remSetup`), their keystream (`ksSel`), then each
block hashed as read and decrypted in place with its keystream, read at
`r11 + r10 + 768` with `r11` lowered by 512: the first alone if `r` is odd
(`StitchZH.remBodyD`, in the lower lanes), then two at a time (`remPairD`),
after which the products of the two lanes are added (`foldLanes`); then the
products are reduced into `Y`, and `Y` stored. -/
def remD : Prog isa :=
  .seq (.block StitchZH.remSetup)
    (.seq ksSel
      (.seq (.block (([.alu .sub .r11 (.imm 512), .mov32 .r10 (.imm 0)] : List Instr) ++ StitchAvx.zero ++
          ([.alu .test .r9 (.imm 1)] : List Instr)))
        (.seq (.ite .e (.block [.alu .cmp .r9 (.imm 16)]) (.block (StitchZH.remBodyD .rdx ++ StitchZH.remNext)))
          (.seq (.ite .e (.block []) (.seq (.loop (.block (remPairD ++ remNextPair)) .ne) (.block foldLanes)))
            (.block (StitchAvx.reduceHash ++ ([.alu .add .r11 (.imm 512)] : List Instr) ++ storeY))))))

/-- `dec`, for any number of blocks from 16 on: the blocks after the last
group, if any, by `remD`. -/
def decR : Prog isa :=
  .seq (.block setup)
    (.seq (.loop dbody .ae)
      (.seq (.block [.alu .test .r9 (.reg .r9)])
        (.ite .e (.block (storeCtr ++ storeY)) (.seq (.block [.alu .add .r9 (.imm 16)]) remD))))

end VG.Impl.Gcm.X86_64.StitchR
