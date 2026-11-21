module

public import VerifiedGarbage.Impl.Blake2.X86.Stream
public import VerifiedGarbage.Impl.Blake2.X86.CompressB
public import VerifiedGarbage.Impl.StackScratch.X86
public import VerifiedGarbage.Impl.Scrub.X86

/-!
# BLAKE2's streaming functions on x86 (32-bit), as emitted

Each function's body and then its cleanup (`Impl.Scrub.X86`): `init`, which
calls nothing and has no frame, clears the registers it may leave secret
(`scrub`); `update` and `finalize`, which run in a frame that allocates their
scratch space and call the compression function, also zero the stack they use
below `esp` (`scrubAll`), the 32 bytes of the compression function's calls and
the bytes of their scratch frame.
-/

@[expose] public section

namespace VG.Impl.Blake2.X86.Fn

open VG.X86

/-- `vg_blake2{b,s}_init`. -/
def init {w : Nat} (P : Spec.Blake2.Params w) : Prog isa := Impl.Scrub.X86.scrub 0 (Stream.init P)

/-- `vg_blake2b_update`. -/
def updateB : Prog isa :=
  Impl.Scrub.X86.scrubAll 0 636
    (Impl.StackScratch.X86.withStackScratch 604 5 (Stream.update 64 "vg_blake2b_compress" CompressB.compress))

/-- `vg_blake2b_finalize`. -/
def finalizeB : Prog isa :=
  Impl.Scrub.X86.scrubAll 0 632
    (Impl.StackScratch.X86.withStackScratch 600 4 (Stream.finalize 64 "vg_blake2b_compress" CompressB.compress))

/-- `vg_blake2s_update`. -/
def updateS : Prog isa :=
  Impl.Scrub.X86.scrubAll 0 636
    (Impl.StackScratch.X86.withStackScratch 604 5 (Stream.update 32 "vg_blake2s_compress" CompressS.compress))

/-- `vg_blake2s_finalize`. -/
def finalizeS : Prog isa :=
  Impl.Scrub.X86.scrubAll 0 632
    (Impl.StackScratch.X86.withStackScratch 600 4 (Stream.finalize 32 "vg_blake2s_compress" CompressS.compress))

end VG.Impl.Blake2.X86.Fn
