module

public import VerifiedGarbage.Impl.Camellia.X86.Ecb
public import VerifiedGarbage.Impl.Modes.X86.Wide
public import VerifiedGarbage.Impl.Modes.CbcChained

/-!
# Camellia's core for the modes on x86 (32-bit)

`dirCore d`: the bitsliced ECB's pieces (`Ecb.lean`) as a core for the
modes (`Impl/Modes/X86/Seq.lean`), whose key is two arguments: the schedule
and the number of rounds. `prepare` builds the table of subkeys in the order
of the direction `d` for 18 rounds or 24, and `crypt` calls
`vg_camellia_crypt_prepared` (`Prepared.lean`), which runs the eight blocks
of the tail buffer through the code written out for that number of rounds,
its arguments pushed in a frame (16 bytes of stack with the return address);
each reads the number of rounds from its stack argument (the analysis of
constant time takes what the scratch buffer holds as secret once the modes
store through the data pointer). The modes' slots follow ECB's 672: 682
slots in all (`[u64; 341]`).

CBC runs in the core's direction; OFB and CFB128 run the cipher forwards
(encryption) in both directions. The number of rounds is public, as in ECB.

CBC and CFB128 decryption, whose blocks can be deciphered independently,
take the blocks in groups (`Impl/Modes/X86/Wide.lean`): of eight, the
core's buffer, while eight are left, then of four and of two (`levels`),
then one, each group one call of `vg_camellia_crypt_prepared`, which costs
the same for any number of the buffer's blocks. The other modes, whose
blocks each need the one before, call it once a block.
-/

@[expose] public section

namespace VG.Impl.Camellia.X86

open VG.X86 VG.Impl.Aes.X86

/-- Camellia's core for the direction `d`. -/
def dirCore (d : Dir) : Modes.X86.Core where
  prepare := prepareCall d 5
  crypt := cryptCall
  slots := slots
  total := slots + 10
  buf := tailSlot
  G := 8
  bw := 4
  stack := 16
  ka := 2

/-- The sizes of the groups of blocks the modes whose blocks are independent
take, in turn, before single blocks. -/
def levels : List Nat := [8, 4, 2]

/-- `vg_camellia_cbc_encrypt_chained`, with its scratch buffer as the sixth argument. -/
def cbcEncryptChained : Prog isa := (dirCore .encrypt).seq (Modes.Mode.cbcEncChained 4)

/-- `vg_camellia_cbc_decrypt_chained`, with its scratch buffer as the sixth argument. -/
def cbcDecryptChained : Prog isa :=
  (dirCore .decrypt).seqLevels (Modes.Mode.cbcDecWide 4) levels (Modes.Mode.cbcDecChained 4)

/-- `vg_camellia_ofb`, with its scratch buffer as the sixth argument. -/
def ofb : Prog isa := (dirCore .encrypt).seq (Modes.Mode.ofb 4)

/-- `vg_camellia_cfb128_encrypt`, with its scratch buffer as the sixth argument. -/
def cfbEncrypt : Prog isa := (dirCore .encrypt).seq (Modes.Mode.cfbEnc 4)

/-- `vg_camellia_cfb128_decrypt`, with its scratch buffer as the sixth argument. -/
def cfbDecrypt : Prog isa :=
  (dirCore .encrypt).seqLevels (Modes.Mode.cfbDecWide 4) levels (Modes.Mode.cfbDecEarly 4)

end VG.Impl.Camellia.X86
