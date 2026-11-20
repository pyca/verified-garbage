module

public import VerifiedGarbage.Impl.Blake2.PPC64LE.Stream
public import VerifiedGarbage.Impl.Scrub.PPC64LE
public import VerifiedGarbage.Impl.StackScratch.PPC64LE
public import VerifiedGarbage.Spec.Blake2

/-!
# Blake2 on PPC64LE: the functions as emitted

Each function followed by its cleanup (`Impl.Scrub.PPC64LE.scrub`): the
result's bits, the bytes of stack its frames use, which the cleanup zeroes
(none for a function that wipes its own frame before it releases it), and the
volatile registers it writes, which the cleanup clears, so that it returns
without secret residue (`Proof/Blake2/PPC64LE/Scrub.lean`).
-/

@[expose] public section

namespace VG.Impl.Blake2.PPC64LE.Fn

open VG.PPC64LE
open VG.Impl.Scrub.PPC64LE (scrub)

/-- `vg_blake2b_init`, as emitted. -/
def initB : Prog isa :=
  scrub 0 0 ⟨false, false, [.r5, .r6, .r9, .r10, .r12], false, []⟩
    (Impl.Blake2.PPC64LE.Stream.init Spec.Blake2.b)

/-- `vg_blake2b_update`, as emitted. -/
def updateB : Prog isa :=
  scrub 0 656 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (Impl.StackScratch.PPC64LE.withStackScratch 608 .r7 (Impl.Blake2.PPC64LE.Stream.update Spec.Blake2.b))

/-- `vg_blake2b_finalize`, as emitted. -/
def finalizeB : Prog isa :=
  scrub 0 656 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (Impl.StackScratch.PPC64LE.withStackScratch 608 .r6 (Impl.Blake2.PPC64LE.Stream.finalize Spec.Blake2.b))

/-- `vg_blake2s_init`, as emitted. -/
def initS : Prog isa :=
  scrub 0 0 ⟨false, false, [.r5, .r6, .r9, .r10, .r12], false, []⟩
    (Impl.Blake2.PPC64LE.Stream.init Spec.Blake2.s)

/-- `vg_blake2s_update`, as emitted. -/
def updateS : Prog isa :=
  scrub 0 656 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (Impl.StackScratch.PPC64LE.withStackScratch 608 .r7 (Impl.Blake2.PPC64LE.Stream.update Spec.Blake2.s))

/-- `vg_blake2s_finalize`, as emitted. -/
def finalizeS : Prog isa :=
  scrub 0 656 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (Impl.StackScratch.PPC64LE.withStackScratch 608 .r6 (Impl.Blake2.PPC64LE.Stream.finalize Spec.Blake2.s))

end VG.Impl.Blake2.PPC64LE.Fn
