module

public import VerifiedGarbage.Impl.Camellia.X86.Prepared
public import VerifiedGarbage.Impl.Modes.X86.Seq
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
-/

@[expose] public section

namespace VG.Impl.Camellia.X86

open VG.X86 VG.Impl.Aes.X86

/-- The number of rounds, the second stack argument, compared with 18. -/
def cmpRounds : List Instr := [.mov .eax (.mem (argOp 1)), .alu .cmp .eax (.imm 18)]

/-- Camellia's core for the direction `d`. -/
def dirCore (d : Dir) : Modes.X86.Core where
  prepare := .seq (.block cmpRounds) (.ite .e (keys d 3) (keys d 4))
  crypt := cryptCall
  slots := slots
  total := slots + 10
  buf := tailSlot
  G := 8
  bw := 4
  stack := 16
  ka := 2

/-- `vg_camellia_cbc_encrypt_chained`, with its scratch buffer as the sixth argument. -/
def cbcEncryptChained : Prog isa := (dirCore .encrypt).seq (Modes.Mode.cbcEncChained 4)

/-- `vg_camellia_cbc_decrypt_chained`, with its scratch buffer as the sixth argument. -/
def cbcDecryptChained : Prog isa := (dirCore .decrypt).seq (Modes.Mode.cbcDecChained 4)

/-- `vg_camellia_ofb`, with its scratch buffer as the sixth argument. -/
def ofb : Prog isa := (dirCore .encrypt).seq (Modes.Mode.ofb 4)

/-- `vg_camellia_cfb128_encrypt`, with its scratch buffer as the sixth argument. -/
def cfbEncrypt : Prog isa := (dirCore .encrypt).seq (Modes.Mode.cfbEnc 4)

/-- `vg_camellia_cfb128_decrypt`, with its scratch buffer as the sixth argument. -/
def cfbDecrypt : Prog isa := (dirCore .encrypt).seq (Modes.Mode.cfbDec 4)

end VG.Impl.Camellia.X86
