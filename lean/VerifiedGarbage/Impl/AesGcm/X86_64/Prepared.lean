module

public import VerifiedGarbage.Impl.AesGcm.X86_64
public import VerifiedGarbage.Impl.Gcm.X86_64.StitchZP

/-! # Preparing GHASH powers once at key setup -/

@[expose] public section

namespace VG.Impl.AesGcm.X86_64.Prepared
open VG.X86_64
open VG.Impl.Gcm.X86_64.Pclmul (at_ revMask poly)
open VG.Impl.Gcm.X86_64.Stitch (storesK)
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
end VG.Impl.AesGcm.X86_64.Prepared
