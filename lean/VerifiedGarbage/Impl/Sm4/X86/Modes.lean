import VerifiedGarbage.Impl.Sm4.X86.Ecb
import VerifiedGarbage.Impl.Modes.X86.Seq

/-!
# SM4's core for the modes on x86 (32-bit)

`dirCore d`: the bitsliced ECB's pieces (`Ecb.lean`) as a core for the
modes (`Impl/Modes/X86/Seq.lean`): `prepare` builds the table of round keys
in the order of the direction `d` from the schedule (the first stack
argument), and `crypt` runs the 32 rounds on the eight blocks of the tail
buffer. The modes' slots follow the table, in place of ECB's saved
registers and data pointer: 362 slots in all (`[u64; 181]`).
-/

namespace VG.Impl.Sm4.X86

open VG.X86

/-- SM4's core for the direction `d`. -/
def dirCore (d : Dir) : Modes.X86.Core where
  prepare := keys d
  crypt := crypt8
  slots := tableEnd
  total := tableEnd + 10
  buf := tailSlot
  G := 8
  bw := 4

/-- `vg_sm4_cbc_encrypt`, with its scratch buffer as the fifth argument. -/
def cbcEncrypt : Prog isa := (dirCore .encrypt).seq (Modes.Mode.cbcEnc 4)

/-- `vg_sm4_cbc_decrypt`, with its scratch buffer as the fifth argument. -/
def cbcDecrypt : Prog isa := (dirCore .decrypt).seq (Modes.Mode.cbcDec 4)

end VG.Impl.Sm4.X86
