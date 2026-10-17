module

public import VerifiedGarbage.Impl.AesGcm.X86_64
public import VerifiedGarbage.Impl.Gcm.X86_64.StitchZP
public import VerifiedGarbage.Impl.Gcm.X86_64.StitchZ

/-! # Preparing GHASH powers once at key setup -/

@[expose] public section

namespace VG.Impl.AesGcm.X86_64.Prepared
open VG.X86_64
open VG.Impl.Gcm.X86_64.Pclmul (at_ revMask poly)
open VG.Impl.Gcm.X86_64.Stitch (storesK pregs setupG)
open VG.Impl.Gcm.X86_64.StitchZ (pow48)
open VG.Impl.Gcm.X86_64.StitchZP (cvtPair cvtConsts)

/-- Convert raw powers `2*k+1` and `2*k+2` in place, even power first. -/
def pair (k : Nat) : List Instr :=
  cvtPair (2*k+1) .xmm12 ++ storesK .rdi [.xmm12] (8+k)

/-- The constants of the conversion, and `rax` at the end of the table. -/
def convertSetup : List Instr :=
  Gcm.X86_64.Pclmul.const .xmm0 revMask ++ Gcm.X86_64.Pclmul.const .xmm1 poly ++
  ([.vop (.vinserti128 .xmm0 .xmm0 .xmm0 1),
    .vop (.vinserti128 .xmm1 .xmm1 .xmm1 1)] : List Instr) ++
  cvtConsts ++ ptr .rax .rdi 768

/-- Convert the 48 raw powers in the context at `rdi` to prepared pairs, one
pair per iteration, advancing `rdi` until it reaches `rax`. -/
def convert : Prog isa :=
  .seq (.block convertSetup)
    (.loop (.block (pair 0 ++ ([.alu .add .rdi (imm 32), .alu .cmp .rdi (.reg .rax)] : List Instr))) .ne)

/-- Key setup and raw powers as before, then conversion before restoring the ABI registers. -/
def init (c : Callees) : Prog isa :=
  initWith c (.seq (.block (([.mov .rax (.mem (at_ .r13 240)), .store (at_ .r13 256) .rax,
      .mov .rax (.mem (at_ .r13 248)), .store (at_ .r13 264) .rax] : List Instr) ++ ptr .rbp .r13 272))
    (.seq (powLoop c) (.seq (.block [.mov .rdi (.reg .r13)]) (.seq convert (.block restore)))))

/-! ## With 512-bit registers

`StitchZ`'s own powers: `H'`–`H'¹⁶` (`Stitch.setupG`), stored to
`scratch = W + 1024`, and `H'¹⁷`–`H'⁴⁸` from them (`StitchZ.pow48`), each
already in the prepared form, then copied to their pairs in the context. -/

/-- Pair `q` of the tables at `scratch + 32 q` (`H'¹⁶ᵗ⁺¹⁶⁻²ᵐ` and the power
below it, for `q = 8 t + m`), copied to its pair `8 t + 7 - m` in the
context. -/
def copyPair (q : Nat) : List Instr :=
  .vmovdquLoad .l256 .xmm12 (at_ .r11 (32 * q)) :: storesK .r13 [.xmm12] (8 * (q / 8) + 15 - q % 8)

/-- The 48 powers, prepared, into the context at `r13`, with `W` at `r15`. -/
def powersZ : List Instr :=
  ([.mov .rdi (.reg .r13)] : List Instr) ++ ptr .r11 .r15 1024 ++ setupG ++ storesK .r11 pregs 0 ++
  ([.zop (.vshufi32x4 .xmm1 .xmm1 .xmm1 0x44)] : List Instr) ++ pow48 ++
  (List.range 24).flatMap copyPair

/-- Key setup, then the powers on 512-bit registers. -/
def initZ (c : Callees) : Prog isa := initWith c (.block (powersZ ++ restore))
end VG.Impl.AesGcm.X86_64.Prepared
