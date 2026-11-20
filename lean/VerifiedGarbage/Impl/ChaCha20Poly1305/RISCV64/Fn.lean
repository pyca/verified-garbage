module

public import VerifiedGarbage.Impl.ChaCha20Poly1305.RISCV64.SealGather
public import VerifiedGarbage.Impl.StackScratch.RISCV64.Args
public import VerifiedGarbage.Impl.Scrub.RISCV64

/-!
# ChaCha20-Poly1305 on RISC-V, as emitted

`vg_chacha20_poly1305_seal`, `…_open`, `…_open_to` and `…_seal_gather`, each
followed by its cleanup (`Impl.Scrub.RISCV64.scrubSel`): the caller-saved
registers cleared but the result's bits, and, of the stack its frames used,
only the runs of doublewords `fs` states, those the residue analysis
(`RISCV64.rtaint`) finds may differ between two runs. `seal` and `open` wipe
their working space themselves, which leaves none; `open_to` and
`seal_gather` leave two doublewords of their frame.
-/

@[expose] public section

namespace VG.Impl.ChaCha20Poly1305.RISCV64.Fn

open VG.RISCV64 VG.Impl.Scrub.RISCV64 VG.Impl.StackScratch.RISCV64

/-- `vg_chacha20_poly1305_seal`, then its cleanup. -/
def «seal» : Prog isa :=
  scrubSel 0 [] (withStackScratchWiped 624 .a7 78 (inPlace VG.Impl.ChaCha20Poly1305.RISCV64.«seal»))

/-- `vg_chacha20_poly1305_open`, then its cleanup. -/
def «open» : Prog isa :=
  scrubSel 32 [] (withStackScratchWiped 624 .a7 78 (inPlace VG.Impl.ChaCha20Poly1305.RISCV64.«open»))

/-- `vg_chacha20_poly1305_open_to`, then its cleanup. -/
def openTo : Prog isa :=
  scrubSel 32 [(640, [(0, 2)])] (withStackScratchArgsWiped 640 1 78 VG.Impl.ChaCha20Poly1305.RISCV64.openTo)

/-- `vg_chacha20_poly1305_seal_gather`, then its cleanup. -/
def sealGather : Prog isa := scrubSel 0 [(640, [(78, 2)])] SealGather.sealGather

end VG.Impl.ChaCha20Poly1305.RISCV64.Fn
