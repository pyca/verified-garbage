module

public import VerifiedGarbage.Impl.Sm4.X86.Prepared
public import VerifiedGarbage.Impl.Modes.X86.Seq
public import VerifiedGarbage.Impl.Modes.CbcChained

/-!
# SM4's core for the modes on x86 (32-bit)

`dirCore d`: ECB's two halves as functions (`Prepared.lean`), called as a
core for the modes (`Impl/Modes/X86/Seq.lean`): `prepare` calls
`vg_sm4_prepare_keys`, which builds the table of round keys in the order of
the direction `d` from the schedule (the first stack argument), and
`crypt` calls `vg_sm4_crypt_prepared`, which runs the 32 rounds on the
eight blocks of the tail buffer. The core's slots are the functions'
working space, ECB's 358; the modes' follow: 368 slots in all
(`[u64; 184]`), and 20 bytes of stack for the calls.
-/

@[expose] public section

namespace VG.Impl.Sm4.X86

open VG.X86

/-- SM4's core for the direction `d`. -/
def dirCore (d : Dir) : Modes.X86.Core where
  prepare := prepareCall d
  crypt := cryptCall
  slots := slots
  total := slots + 10
  buf := tailSlot
  G := 8
  bw := 4
  stack := 20

/-- `vg_sm4_cbc_encrypt_chained`, with its scratch buffer as the fifth argument. -/
def cbcEncryptChained : Prog isa := (dirCore .encrypt).seq (Modes.Mode.cbcEncChained 4)

/-- `vg_sm4_cbc_decrypt_chained`, with its scratch buffer as the fifth argument. -/
def cbcDecryptChained : Prog isa := (dirCore .decrypt).seq (Modes.Mode.cbcDecChained 4)

end VG.Impl.Sm4.X86
