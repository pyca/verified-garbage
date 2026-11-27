module

public import VerifiedGarbage.Impl.Sm4.X86.Prepared
public import VerifiedGarbage.Impl.Modes.X86.Wide
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

The modes whose blocks can be enciphered independently (CBC and CFB128
decryption, and counter mode: `Fb.lean`, `Ctr.lean`, `Ctr32.lean`) take the
blocks in groups (`Impl/Modes/X86/Wide.lean`): of eight, the core's buffer,
while eight are left, then of four and of two (`levels`), then one, each
group one call of `vg_sm4_crypt_prepared`, which costs the same for any
number of the buffer's blocks. The other modes, whose blocks each need the
one before, call it once a block.
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

/-- The sizes of the groups of blocks the modes whose blocks are independent
take, in turn, before single blocks. -/
def levels : List Nat := [8, 4, 2]

/-- `vg_sm4_cbc_encrypt_chained`, with its scratch buffer as the fifth argument. -/
def cbcEncryptChained : Prog isa := (dirCore .encrypt).seq (Modes.Mode.cbcEncChained 4)

/-- `vg_sm4_cbc_decrypt_chained`, with its scratch buffer as the fifth argument. -/
def cbcDecryptChained : Prog isa :=
  (dirCore .decrypt).seqLevels (Modes.Mode.cbcDecWide 4) levels (Modes.Mode.cbcDecChained 4)

end VG.Impl.Sm4.X86
