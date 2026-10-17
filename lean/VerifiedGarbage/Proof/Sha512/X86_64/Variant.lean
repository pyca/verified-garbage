module

public import VerifiedGarbage.Proof.Sha512.X86_64.Stream.Md
public import VerifiedGarbage.Proof.Framework.X86_64.Depth
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
public import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Lit
public import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Lit
public import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Avx

/-!
# Implementations of the SHA-512 compression function on x86-64

A `Compress` is what a function that calls the compression function needs
of it, so that its proof holds for every implementation: each makes each
member of the SHA-512 family a variant of the interface `MdHash` on x86-64
(`Variants/MdHash/X86_64/Sha384*.lean`, …,
`Proof/Pbkdf2/Md/X86_64/Hashes/Sha512.lean`), and each function built on it
(in `Generic/MdHash/X86_64/`) is emitted once for each of them (see
`TCB/Emit.lean`). The four members share the implementations, so they are
here: `scalar`, `avx2` and `shani`.
-/

@[expose] public section

namespace VG.Proof.Sha512.X86_64

open VG.X86_64

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
  /-- The 16-byte words at the start of its working space in which it may
  leave the message schedule, which is secret when the block is (HMAC's
  padded keys): callers that keep the working space in a frame of their own
  zero them (`withStackScratchWipedX`, HMAC's `init`). What it saves there
  of its caller's registers (pointers and lengths) is not counted. -/
  wipe : Nat
  /-- They are within its working space. -/
  wipe_le : 16 * wipe ≤ 1328 := by decide

namespace Compress

/-- The scalar implementation, `vg_sha512_compress`, in the baseline ISA. -/
def scalar : Compress where
  callee := .scalar
  ok := Stream.scalar_ok
  mxcsr := by change Impl.Sha512.X86_64.Rolled.compress.allInstrs _ = true; lit_decide
  spSafe := Code.all_of_allInstrs (by change Impl.Sha512.X86_64.Rolled.compress.allInstrs _ = true; lit_decide)
  suffix := ""
  features := []
  -- The 16-word window of the schedule, `scratch[0..128)` (`Impl.Sha512.X86_64`).
  wipe := 8

/-- `vg_sha512_compress_avx2`, which needs AVX, AVX2, BMI1 and BMI2. -/
def avx2 : Compress where
  callee := .avx2
  ok := Stream.avx2_ok
  mxcsr := by change Impl.Sha512.X86_64.Avx2Rolled.compress.allInstrs _ = true; lit_decide
  spSafe := Code.all_of_allInstrs (by change Impl.Sha512.X86_64.Avx2Rolled.compress.allInstrs _ = true; lit_decide)
  suffix := "_avx2"
  features := ["avx", "avx2", "bmi1", "bmi2"]
  -- `Wₜ + Kₜ` of both blocks for all 80 rounds, `scratch[0..1280)`
  -- (`Impl.Sha512.X86_64.Avx2`).
  wipe := 80

/-- `vg_sha512_compress_shani`, which needs the SHA512 extension, AVX and AVX2. -/
def shani : Compress where
  callee := .shani
  ok := Stream.shani_ok
  mxcsr := by change Impl.Sha512.X86_64.ShaNi.compress.allInstrs _ = true; lit_decide
  spSafe := Code.all_of_allInstrs (by change Impl.Sha512.X86_64.ShaNi.compress.allInstrs _ = true; lit_decide)
  suffix := "_shani"
  features := ["avx", "avx2", "sha512"]
  -- `scratch` is not used (`Impl.Sha512.X86_64.ShaNi`).
  wipe := 0

end Compress

end VG.Proof.Sha512.X86_64
