import VerifiedGarbage.Impl.Gcm.X86_64.StitchZTo

/-!
# AVX-512 GCM loops reading prepared GHASH powers

The context stores the converted powers once at key setup. Each pair is
loaded directly, eliminating the byte reversal, shift and reduction from
each record. The arithmetic loops and working-space layout are unchanged.
-/

namespace VG.Impl.Gcm.X86_64.StitchZR

open VG.X86_64
open VG.Impl.Gcm.X86_64.Pclmul (at_ revMask poly)
open VG.Impl.Gcm.X86_64.Stitch (storesK pregs setupC storeCtr storeY)
open VG.Impl.Gcm.X86_64.Vpclmul (preg16)
open VG.Impl.Gcm.X86_64.StitchZ (first body dbody lastG adv batch body48 dbody48 setupZ tab)

/-- A prepared pair: for odd `j` in `1 … 47`, the encoded `H^(j+1)`
and `H^j` occupy the two lanes at `ctx + 240 + 16*j`. -/
def cvtPair (j : Nat) (d : XReg) : List Instr :=
  [.vmovdquLoad .l256 d (at_ .rdi (240 + 16 * j))]

/-- The constants in both lanes of `ymm0` and `ymm1`, and
`H'¹⁶`–`H'` in the pairs `ymm3`–`ymm6`, `ymm12`–`ymm15` (`preg16`), as
`Stitch.setupG` leaves them. -/
def setupGP : List Instr :=
  Pclmul.const .xmm0 revMask ++ Pclmul.const .xmm1 poly ++
  ([.vop (.vinserti128 .xmm0 .xmm0 .xmm0 1), .vop (.vinserti128 .xmm1 .xmm1 .xmm1 1)] : List Instr) ++
  (List.range 8).flatMap fun k => cvtPair (15 - 2 * k) (preg16 k)

/-- `Stitch.setup` with the powers loaded, then `StitchZ.setupZ`. -/
def setupP : List Instr := setupGP ++ storesK .r11 pregs 0 ++ setupC ++ setupZ

/-- The pair of table `g` at `scratch + tab g + 32 m` (`tab g = 32 (16 - 8 g)`):
`H'ᴱ⁻²ᵐ` and `H'ᴱ⁻²ᵐ⁻¹`, where `E = 48 - 16 g`. -/
def powPair (g m : Nat) : List Instr :=
  cvtPair (48 - 16 * g - 2 * m - 1) .xmm12 ++ storesK .r11 [.xmm12] (16 - 8 * g + m)

/-- The tables of `StitchZ.pow48` (`H'³²`–`H'¹⁷` at `scratch + 256`,
`H'⁴⁸`–`H'³³` at `scratch + 512`), loaded, and the reduction constant
saved. -/
def powP48 : List Instr :=
  (List.range 8).flatMap (powPair 1) ++ (List.range 8).flatMap (powPair 0) ++
  ([.vmovdqu32Store (at_ .r11 832) .xmm1] : List Instr)

/-- `StitchZ.big` with the tables loaded. -/
def bigP : Prog isa :=
  .seq (.block powP48) (.seq (batch 4 fun _ => []) (.seq (batch 8 fun _ => [])
    (.seq (.loop body48 .ae) (.block (.vmovdqu32Load .xmm1 (at_ .r11 832) :: (lastG ++ adv ++ lastG ++ adv))))))

/-- `StitchZ.bigD` with the tables loaded. -/
def bigDP : Prog isa :=
  .seq (.block powP48) (.seq (.loop dbody48 .ae) (.block [.vmovdqu32Load .xmm1 (at_ .r11 832)]))

/-- `StitchZ.enc` with the powers loaded. -/
def enc : Prog isa :=
  .seq (.block setupP)
    (.seq first
      (.seq (.block [.alu .cmp .r9 (.imm 256)])
        (.seq (.ite .b (.block []) bigP)
          (.seq (.block [.alu .cmp .r9 (.imm 32)])
            (.seq (.ite .b (.block []) (.loop body .ae))
              (.block (storeCtr ++ lastG ++ storeY)))))))

/-- `StitchZ.dec` with the powers loaded. -/
def dec : Prog isa :=
  .seq (.block setupP)
    (.seq (.block [.alu .cmp .r9 (.imm 256)])
      (.seq (.ite .b (.block []) bigDP)
        (.seq (.block [.alu .cmp .r9 (.imm 16)])
          (.seq (.ite .b (.block []) (.loop dbody .ae))
            (.block (storeCtr ++ storeY))))))

end VG.Impl.Gcm.X86_64.StitchZR

namespace VG.Impl.Gcm.X86_64.StitchZRTo
open VG.X86_64
open VG.Impl.Gcm.X86_64.Stitch (storesK pregs)
open VG.Impl.Gcm.X86_64.StitchZ (setupZ)
open VG.Impl.Gcm.X86_64.StitchZTo (setupCTo bigRestTo encWith)

/-- Prepared-power setup for out-of-place encryption. -/
def setupP : List Instr := StitchZR.setupGP ++ storesK .r11 pregs 0 ++ setupCTo ++ setupZ

/-- The larger prepared tables followed by the existing out-of-place loop. -/
def bigPTo : Prog isa := .seq (.block StitchZR.powP48) bigRestTo

/-- Out-of-place encryption using the prepared context. -/
def encP : Prog isa := encWith setupP bigPTo

end VG.Impl.Gcm.X86_64.StitchZRTo
