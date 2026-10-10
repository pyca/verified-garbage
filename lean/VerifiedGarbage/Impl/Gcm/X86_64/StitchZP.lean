import VerifiedGarbage.Impl.Gcm.X86_64.StitchZ

/-!
# The AVX-512 interleaved loops, with the powers of the hash subkey in the key context

`StitchZ.enc` and `StitchZ.dec` for a key context of
`vg_aes_gcm_init_precomputed` (`Spec/Gcm/Precomputed.lean`), which holds the
powers `H¹ … H⁴⁸` of the hash subkey at `ctx + 256`: instead of computing
`H'`–`H'¹⁶` (and, from 256 blocks on, `H'¹⁷`–`H'⁴⁸`) by multiplications, one
after the other, they load them and convert each to the representation
the loops multiply by (`H'ʲ = Hʲ · x⁻¹`, `Pclmul.hInv`), two at a time in
the lanes of a 256-bit register (`cvtPair`): the byte order reversed, a
shift left by one bit, and the reduction constant `x⁻¹` added if the bit
shifted out was set. The rest is `StitchZ`'s.

`setupP` leaves the registers and `scratch` as `Stitch.setup` does (the
pairs `H'¹⁶⁻²ᵏ`, `H'¹⁵⁻²ᵏ` in `ymm3`–`ymm6`, `ymm12`–`ymm15`, stored at
`scratch + 32 k`), and `powP48` the tables of `StitchZ.pow48`.
-/

namespace VG.Impl.Gcm.X86_64.StitchZP

open VG.X86_64
open VG.Impl.Gcm.X86_64.Pclmul (at_ revMask poly)
open VG.Impl.Gcm.X86_64.Stitch (storesK pregs setupC storeCtr storeY)
open VG.Impl.Gcm.X86_64.Vpclmul (preg16)
open VG.Impl.Gcm.X86_64.StitchZ (first body dbody lastG adv batch body48 dbody48 setupZ tab)

/-- `ymm9` all ones and `ymm8` `x⁻¹` (`Pclmul.xInv`, the reduction constant
in `ymm1` with its lowest bit set), in both lanes. -/
def cvtConsts : List Instr :=
  [.vop (.vbin .vpcmpeqd .l256 .xmm9 .xmm9 .xmm9), .vop (.vshift .psrlq .l256 .xmm8 .xmm9 63),
   .vop (.vshift .pslldq .l256 .xmm8 .xmm8 8), .vop (.vshift .psrldq .l256 .xmm8 .xmm8 8),
   .vop (.vbin .vpxor .l256 .xmm8 .xmm8 .xmm1)]

/-- `d ← a · x⁻¹` in each lane (`Pclmul.hInv`, after its constants), with
the temporary `t`: `a` shifted left by one bit, and `x⁻¹` added if its top
bit was set. -/
def hInvY (d a t : XReg) : List Instr :=
  [.vop (.vshift .psllq .l256 d a 1), .vop (.vshift .psrlq .l256 t a 63),
   .vop (.vshift .pslldq .l256 t t 8), .vop (.vbin .vpor .l256 d d t),
   .vop (.vpshufd .l256 t a 0xff), .vop (.vshift .psrld .l256 t t 31),
   .vop (.vbin .vpaddd .l256 t t .xmm9), .vop (.vbin .vpandn .l256 t t .xmm8),
   .vop (.vbin .vpxor .l256 d d t)]

/-- `H'ʲ⁺¹` and `H'ʲ` in the lanes of `d`, from `Hʲ⁺¹` and `Hʲ` at
`ctx + 256 + 16 j` and `ctx + 240 + 16 j`, through `ymm7` and `ymm10`. -/
def cvtPair (j : Nat) (d : XReg) : List Instr :=
  ([.vmovdquLoad .l128 .xmm7 (at_ .rdi (256 + 16 * j)), .vmovdquLoad .l128 .xmm10 (at_ .rdi (240 + 16 * j)),
   .vop (.vinserti128 .xmm7 .xmm7 .xmm10 1), .vop (.vbin .vpshufb .l256 .xmm7 .xmm7 .xmm0)] : List Instr) ++
  hInvY d .xmm7 .xmm10

/-- The constants in both lanes of `ymm0` and `ymm1`, `ymm8` and `ymm9`, and
`H'¹⁶`–`H'` in the pairs `ymm3`–`ymm6`, `ymm12`–`ymm15` (`preg16`), as
`Stitch.setupG` leaves them. -/
def setupGP : List Instr :=
  Pclmul.const .xmm0 revMask ++ Pclmul.const .xmm1 poly ++
  ([.vop (.vinserti128 .xmm0 .xmm0 .xmm0 1), .vop (.vinserti128 .xmm1 .xmm1 .xmm1 1)] : List Instr) ++
  cvtConsts ++ (List.range 8).flatMap fun k => cvtPair (15 - 2 * k) (preg16 k)

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
  cvtConsts ++ (List.range 8).flatMap (powPair 1) ++ (List.range 8).flatMap (powPair 0) ++
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

end VG.Impl.Gcm.X86_64.StitchZP
