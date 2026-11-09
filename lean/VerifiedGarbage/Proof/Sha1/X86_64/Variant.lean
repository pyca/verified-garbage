module

public import VerifiedGarbage.Proof.Sha1.X86_64.Stream.Md
public import VerifiedGarbage.Proof.Framework.X86_64.Depth
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# Implementations of the SHA-1 compression function on x86-64

A `Compress` is what a function that calls the compression function needs
of it, so that its proof holds for every implementation: each makes
SHA-1 a variant of the interface `MdHash` on x86-64
(`Variants/MdHash/X86_64/Sha1*.lean`, `Proof/Pbkdf2/Md/X86_64/Hashes/Sha1.lean`),
and each function built on it (in `Generic/MdHash/X86_64/`) is emitted once
for each of them (see `TCB/Emit.lean`). The streaming functions made with any of them are
verified, and have
what callers of those need (their call depth, that they keep `rsp` and never
load MXCSR), so that a caller of them is proven once for every
implementation.
-/

@[expose] public section

namespace VG.Proof.Sha1.X86_64

open VG.X86_64

/-- An implementation of the SHA-1 compression function on x86-64. -/
structure Compress where
  /-- Its symbol and code. -/
  callee : Impl.Sha1.X86_64.Stream.Callee
  /-- It is correct and constant time, and keeps what callers need. -/
  ok : MdStream.X86_64.CalleeOk (P := Stream.params) md callee.code
  /-- It never loads MXCSR. -/
  mxcsr : callee.code.allInstrs (fun i => !loadsMxcsr i) = true
  /-- It never writes the stack pointer. -/
  spSafe : callee.code.all (fun i => !isa.writesSp i) = true
  /-- It uses no stack, so that the streaming functions calling it can keep
  their working space in a frame of their own (`Verified.stackScratch`). -/
  noStack : callee.code.x86_64Depth = 0 := by lit_decide
  /-- What the names of its callers' instances end with (e.g. `_shani`;
  nothing for the baseline implementation). -/
  suffix : String
  /-- The CPU features its code requires, which its callers require too. -/
  features : List String

namespace Compress

/-- The scalar implementation, `vg_sha1_compress`, in the baseline ISA
(`Variants/MdHash/X86_64/Sha1.lean`). -/
def scalar : Compress where
  callee := .scalar
  ok := Stream.scalar_ok
  mxcsr := by decide +kernel
  spSafe := Code.all_of_allInstrs (by lit_decide)
  suffix := ""
  features := []

open VG.Impl.Sha1.X86_64.Stream (update finalize)

variable (v : Compress)

theorem callee_nosp : (v.callee.code.allInstrs fun i => !Taint.clobbers i .rsp) = true := by
  rw [Code.allInstrs_eq]; exact List.all_eq_true.mpr fun i hi => by simp [v.ok.nosp i hi]

end Compress

end VG.Proof.Sha1.X86_64
