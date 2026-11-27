module

public import VerifiedGarbage.Impl.CmacTripleDes.Stream.PPC64LE
public import VerifiedGarbage.Impl.Scrub.PPC64LE
public import VerifiedGarbage.Impl.StackScratch.PPC64LE

/-!
# CmacTripleDes Stream on PPC64LE: the functions as emitted

Each function followed by its cleanup (`Impl.Scrub.PPC64LE.scrubAll`): the
result's bits, the bytes of stack its frames use, which the cleanup zeroes
(none for a function that wipes its own frame before it releases it), and the
volatile registers it writes, which the cleanup clears, so that it returns
without secret residue (`Proof/CmacTripleDes/Stream/PPC64LE/Scrub.lean`).
-/

@[expose] public section

namespace VG.Impl.CmacTripleDes.Stream.PPC64LE.Fn

open VG.PPC64LE
open VG.Impl.Scrub.PPC64LE (scrubAll)

/-- `vg_cmac_triple_des_stream_init`, as emitted. -/
def init : Prog isa :=
  scrubAll 0 672 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (Impl.StackScratch.PPC64LE.withStackScratch 672 .r6 Impl.CmacTripleDes.Stream.PPC64LE.streamInit)

/-- `vg_cmac_triple_des_absorb`, as emitted. -/
def absorb : Prog isa :=
  scrubAll 0 720 ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (Impl.StackScratch.PPC64LE.withStackScratch 720 .r7 Impl.CmacTripleDes.Stream.PPC64LE.absorb)

/-- `vg_cmac_triple_des_finish`, as emitted. -/
def finish : Prog isa :=
  scrubAll 0 672 ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (Impl.StackScratch.PPC64LE.withStackScratch 672 .r6 Impl.CmacTripleDes.Stream.PPC64LE.finish)

end VG.Impl.CmacTripleDes.Stream.PPC64LE.Fn
