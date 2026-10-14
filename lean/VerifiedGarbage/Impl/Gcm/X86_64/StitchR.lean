module

public import VerifiedGarbage.Impl.Gcm.X86_64.StitchZR
public import VerifiedGarbage.Impl.Gcm.X86_64.StitchTo

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
open VG.Impl.Gcm.X86_64.Stitch (storesK pregs setupC first body dbody storeCtr lastG storeY)
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

end VG.Impl.Gcm.X86_64.StitchR
