module

public import VerifiedGarbage.Impl.Seed.X86.Ecb
public import VerifiedGarbage.Impl.Modes.X86.Seq
public import VerifiedGarbage.Impl.Modes.CbcChained

/-!
# SEED's core for the modes on x86 (32-bit)

`dirCore d`: the bitsliced ECB's pieces (`Ecb.lean`) as a core for the
modes (`Impl/Modes/X86/Seq.lean`): `prepare` builds the table of round keys
in the order of the direction `d` from the schedule (the first stack
argument), and `crypt` runs the sixteen rounds on the eight blocks of the
tail buffer. The modes' slots follow ECB's 206: 216 slots in all
(`[u64; 108]`).

CBC runs in the core's direction; OFB and CFB128 run the cipher forwards
(encryption) in both directions.
-/

@[expose] public section

namespace VG.Impl.Seed.X86

open VG.X86
open VG.Spec.Seed (Direction)

/-- SEED's core for the direction `d`. -/
def dirCore (d : Direction) : Modes.X86.Core where
  prepare := .block (keyTable d)
  crypt := crypt8
  slots := X86.slots
  total := X86.slots + 10
  buf := tailSlot
  G := 8
  bw := 4

/-- `vg_seed_cbc_encrypt_chained`, with its scratch buffer as the fifth argument. -/
def cbcEncryptChained : Prog isa := (dirCore .encrypt).seq (Modes.Mode.cbcEncChained 4)

/-- `vg_seed_cbc_decrypt_chained`, with its scratch buffer as the fifth argument. -/
def cbcDecryptChained : Prog isa := (dirCore .decrypt).seq (Modes.Mode.cbcDecChained 4)

/-- `vg_seed_ofb`, with its scratch buffer as the fifth argument. -/
def ofb : Prog isa := (dirCore .encrypt).seq (Modes.Mode.ofb 4)

/-- `vg_seed_cfb128_encrypt`, with its scratch buffer as the fifth argument. -/
def cfbEncrypt : Prog isa := (dirCore .encrypt).seq (Modes.Mode.cfbEnc 4)

/-- `vg_seed_cfb128_decrypt`, with its scratch buffer as the fifth argument. -/
def cfbDecrypt : Prog isa := (dirCore .encrypt).seq (Modes.Mode.cfbDec 4)

end VG.Impl.Seed.X86
