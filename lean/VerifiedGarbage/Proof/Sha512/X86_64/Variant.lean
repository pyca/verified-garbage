module

public import VerifiedGarbage.Proof.Sha512.X86_64.Stream.Md
public import VerifiedGarbage.Proof.Framework.X86_64.Depth
import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Lit
public import VerifiedGarbage.Impl.Sha512.X86_64.Avx512
import VerifiedGarbage.Proof.Sha512.X86_64.Avx512.Pair
import VerifiedGarbage.Proof.Sha512.X86_64.Avx512.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# Implementations of the SHA-512 compression function on x86-64

A `Compress` is what a function that calls the compression function needs
of it, so that its proof holds for every implementation: each makes each
member of the SHA-512 family a variant of the interface `MdHash` on x86-64
(`Variants/MdHash/X86_64/Sha384*.lean`, …,
`Proof/Pbkdf2/Md/X86_64/Hashes/Sha512.lean`), and each function built on it
(in `Generic/MdHash/X86_64/`) is emitted once for each of them (see
`TCB/Emit.lean`). The four members share the implementations, so they are
here: `scalar`, `avx2` and `shani`, and `avx512`, which is `avx2` with a
function that compresses two blocks at once (`Pair`), for HMAC's two padded
keys.
-/

@[expose] public section

namespace VG.Proof.Sha512.X86_64

open VG.X86_64

/-- A function that compresses two blocks into two hash values at once
(`MdStream.X86_64.compress2K`), for a caller with two blocks that do not
depend on each other. -/
structure Pair where
  /-- Its symbol and code. -/
  name : String
  code : Prog isa
  /-- It is correct and constant time, and calls nothing. -/
  ok : MdStream.X86_64.PairOk (P := Stream.params) md code
  /-- It never loads MXCSR, or writes the stack pointer. -/
  mxcsr : code.allInstrs (fun i => !loadsMxcsr i) = true
  spSafe : code.allInstrs (fun i => !isa.writesSp i) = true
  noSp : code.allInstrs (fun i => !Taint.clobbers i .rsp) = true
  /-- It uses no stack. -/
  noStack : code.x86_64Depth = 0

/-- An implementation of the SHA-512 compression function on x86-64. -/
structure Compress where
  /-- Its symbol and code. -/
  callee : Impl.Sha512.X86_64.Stream.Callee
  /-- It is correct and constant time, and keeps what callers need. -/
  ok : MdStream.X86_64.CalleeOk (P := Stream.params) md callee.code
  /-- It never loads MXCSR. -/
  mxcsr : callee.code.allInstrs (fun i => !loadsMxcsr i) = true
  /-- It never writes the stack pointer. -/
  spSafe : callee.code.all (fun i => !isa.writesSp i) = true
  /-- It uses no stack, so that the streaming functions calling it can keep
  their working space in a frame of their own (`Verified.stackScratch`). -/
  noStack : callee.code.x86_64Depth = 0 := by lit_decide
  /-- What the names of its callers' instances end with (e.g. `_avx2`;
  nothing for the baseline implementation). -/
  suffix : String
  /-- The CPU features its code requires, which its callers require too. -/
  features : List String
  /-- What the names of its callers' instances that do not run `pair` end
  with: `suffix`, unless the implementation is another one with a `pair`,
  whose instances those are. -/
  baseSuffix : String := suffix
  /-- A function that compresses two blocks at once, if the implementation
  has one: HMAC's `init` then calls it once for its two padded keys. -/
  pair : Option Pair := none

namespace Compress

/-- The scalar implementation, `vg_sha512_compress`, in the baseline ISA. -/
def scalar : Compress where
  callee := .scalar
  ok := Stream.scalar_ok
  mxcsr := by change Impl.Sha512.X86_64.Rolled.compress.allInstrs _ = true; lit_decide
  spSafe := Code.all_of_allInstrs (by change Impl.Sha512.X86_64.Rolled.compress.allInstrs _ = true; lit_decide)
  suffix := ""
  features := []

/-- `vg_sha512_compress_avx2`, which needs AVX, AVX2, BMI1 and BMI2. -/
def avx2 : Compress where
  callee := .avx2
  ok := Stream.avx2_ok
  mxcsr := by change Impl.Sha512.X86_64.Avx2Rolled.compress.allInstrs _ = true; lit_decide
  spSafe := Code.all_of_allInstrs (by change Impl.Sha512.X86_64.Avx2Rolled.compress.allInstrs _ = true; lit_decide)
  suffix := "_avx2"
  features := ["avx", "avx2", "bmi1", "bmi2"]

/-- `vg_sha512_compress_shani`, which needs the SHA512 extension, AVX and AVX2. -/
def shani : Compress where
  callee := .shani
  ok := Stream.shani_ok
  mxcsr := by change Impl.Sha512.X86_64.ShaNi.compress.allInstrs _ = true; lit_decide
  spSafe := Code.all_of_allInstrs (by change Impl.Sha512.X86_64.ShaNi.compress.allInstrs _ = true; lit_decide)
  suffix := "_shani"
  features := ["avx", "avx2", "sha512"]

/-- `vg_sha512_compress2_avx512`, which needs AVX512F and AVX512VL. -/
theorem compress2_ok : MdStream.X86_64.PairOk (P := Stream.params) md Impl.Sha512.X86_64.Avx512.compress2 :=
  ⟨Avx512.compress2_verified.1, Avx512.compress2_verified.2.1,
    fun i hi => by
      have h : Impl.Sha512.X86_64.Avx512.compress2.allInstrs (fun i => !Taint.clobbers i .rsp) = true := by lit_decide
      rw [Code.allInstrs_eq] at h
      simpa using List.all_eq_true.mp h i hi,
    by change Impl.Sha512.X86_64.Avx512.compress2.depth = 0; lit_decide⟩

/-- `avx2` with `vg_sha512_compress2_avx512`, which needs AVX512F and
AVX512VL too. -/
def avx512 : Compress :=
  { avx2 with
    suffix := "_avx512"
    baseSuffix := avx2.suffix
    features := ["avx", "avx2", "bmi1", "bmi2", "avx512f", "avx512vl"]
    pair := some
      { name := "vg_sha512_compress2_avx512"
        code := Impl.Sha512.X86_64.Avx512.compress2
        ok := compress2_ok
        mxcsr := by lit_decide
        spSafe := by lit_decide
        noSp := by lit_decide
        noStack := by lit_decide } }

end Compress

end VG.Proof.Sha512.X86_64
