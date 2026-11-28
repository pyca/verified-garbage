module

public import VerifiedGarbage.Proof.SlhDsa.X86_64.Thash4Contract
public import VerifiedGarbage.Proof.Framework.X86_64.Call
public import VerifiedGarbage.Proof.Framework.X86_64.CalleeSide
public import VerifiedGarbage.Impl.Scrub.X86_64

/-!
# SLH-DSA on x86-64: an implementation of `thash4`

What the code above `thash4` needs of an implementation of it, for outputs
of `n` bytes: its code, the stack its calls take, its proof against
`thash4Contract`, and the facts a call of it needs (`WP.call`,
`RelCT.call`). The functions above it (`Impl/SlhDsa/X86_64/`) are proven
once for any implementation; the implementations are the elements of
`Proof/Variants/SlhDsaThash4/X86_64.lean`.
-/

@[expose] public section

namespace VG.Proof.SlhDsa.X86_64

open VG VG.X86_64

/-- An implementation of `thash4` for outputs of `n` bytes: the suffix of
the names of the functions emitted with it (`""` for the baseline,
`"_avx2"`, …), its code, and the bytes of stack below the stack pointer
its own calls take (`stack`; a call of it takes 8 more, for its return
address), and what the cleanup of its callers needs of it. -/
structure Thash4Impl (n : Nat) where
  sfx : String
  code : Prog isa
  stack : Nat
  verified : Verified X86_64.target code (thash4Contract n stack)
  nosp : NoSp code
  depth_le : code.depth ≤ 1
  stack_le : stack ≤ 16
  /-- It never loads MXCSR. -/
  nomx : code.allInstrs (fun i => !loadsMxcsr i) = true
  /-- The level of its vector instructions. -/
  level : Impl.Scrub.X86_64.VecLevel
  /-- What the cleanup of a function that calls it needs of its code, at
  that level, with 16 bytes of stack (`X86_64.Scrub.calleeSide`). -/
  side : X86_64.Scrub.calleeSide code level.level 16 = true

end VG.Proof.SlhDsa.X86_64
