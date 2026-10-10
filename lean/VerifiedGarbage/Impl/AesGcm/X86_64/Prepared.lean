import VerifiedGarbage.Impl.AesGcm.X86_64
import VerifiedGarbage.Impl.Gcm.X86_64.StitchZP

/-! # Preparing GHASH powers once at key setup -/

namespace VG.Impl.AesGcm.X86_64.Prepared
open VG.X86_64
open VG.Impl.Gcm.X86_64.Pclmul (at_ revMask poly)
open VG.Impl.Gcm.X86_64.Stitch (storesK)
open VG.Impl.Gcm.X86_64.StitchZP (cvtPair cvtConsts)

/-- Convert raw powers `2*k+1` and `2*k+2` in place, even power first. -/
def pair (k : Nat) : List Instr :=
  cvtPair (2*k+1) .xmm12 ++ storesK .rdi [.xmm12] (8+k)

/-- Convert the 48 raw powers in the context at `rdi` to prepared pairs. -/
def convert : List Instr :=
  Gcm.X86_64.Pclmul.const .xmm0 revMask ++ Gcm.X86_64.Pclmul.const .xmm1 poly ++
  ([.vop (.vinserti128 .xmm0 .xmm0 .xmm0 1),
    .vop (.vinserti128 .xmm1 .xmm1 .xmm1 1)] : List Instr) ++
  cvtConsts ++ (List.range 24).flatMap pair

/-- Key setup and raw powers as before, then conversion before restoring the ABI registers. -/
def init (c : Callees) : Prog isa :=
  initWith c (.seq (.block (([.mov .rax (.mem (at_ .r13 240)), .store (at_ .r13 256) .rax,
      .mov .rax (.mem (at_ .r13 248)), .store (at_ .r13 264) .rax] : List Instr) ++ ptr .rbp .r13 272))
    (.seq (powSteps c 47) (.block (([.mov .rdi (.reg .r13)] : List Instr) ++ convert ++ restore))))
end VG.Impl.AesGcm.X86_64.Prepared
