module

public import VerifiedGarbage.Impl.Gcm.X86_64.StitchZR
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

/-- The `r9 - 16` blocks at `rdx` after the last group, which the loop has
already hashed and decrypted: the counter after them stored and `rax` at
their powers (`StitchZH.remSetup`), their keystream (`ksSel`), then each
block hashed as read and decrypted in place with its keystream, read at
`r11 + r10 + 768` with `r11` lowered by 512 (`StitchZH.remBodyD`), the
products added in the lower lanes of `xmm8`–`xmm10`, reduced into `Y`, and
`Y` stored. -/
def remD : Prog isa :=
  .seq (.block StitchZH.remSetup)
    (.seq ksSel
      (.seq (.block (([.alu .sub .r11 (.imm 512), .mov32 .r10 (.imm 0)] : List Instr) ++ StitchAvx.zero))
        (.seq (.loop (.block (StitchZH.remBodyD .rdx ++ StitchZH.remNext)) .ne)
          (.block (StitchAvx.reduceHash ++ ([.alu .add .r11 (.imm 512)] : List Instr) ++ storeY)))))

/-- `dec`, for any number of blocks from 16 on: the blocks after the last
group, if any, by `remD`. -/
def decR : Prog isa :=
  .seq (.block setup)
    (.seq (.loop dbody .ae)
      (.seq (.block [.alu .test .r9 (.reg .r9)])
        (.ite .e (.block (storeCtr ++ storeY)) (.seq (.block [.alu .add .r9 (.imm 16)]) remD))))

end VG.Impl.Gcm.X86_64.StitchR
