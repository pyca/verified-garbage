module

public import VerifiedGarbage.Impl.Modes.RISCV64.Seq
public import VerifiedGarbage.Impl.Modes.CbcChained
public import VerifiedGarbage.Impl.Blowfish.RISCV64

/-!
# Blowfish's modes on RISC-V

`dirCore up`: ECB's block function, inlined, as a core for the modes
(`Impl/Modes/RISCV64/Seq.lean`), encrypting (`up`) or decrypting the block
in its buffer in place. Its slots: the buffer's one block (slot 6), and a
copy of the schedule after it (from slot 7), which `prepare` makes a byte
at a time, since the contracts state no alignment for the schedule and the
block function reads it a word at a time. 528 slots in all, with the
modes', which the mode zeroes before it frees them. The block function
writes only temporaries and argument registers but `a0`, so it keeps the
modes' state in `s1`–`s4` and the schedule's argument.

`cbcEncryptChained`, `cbcDecryptChained`, `ofb`, `cfbEncrypt` and
`cfbDecrypt` (schedule = a0, iv = a1, data = a2, n = a3) are the modes over
it: CBC in both directions, and the others with the encryption.
-/

@[expose] public section

namespace VG.Impl.Blowfish.RISCV64

open VG.RISCV64
open VG.Impl.Modes.RISCV64 (sb)
open VG.Impl.Words.RISCV64 (copyLoop)

/-- The buffer's block. -/
def bufSlot : Nat := 6

/-- The buffer's offset in the frame. -/
def bufOff : Nat := 8 * bufSlot

/-- The schedule's copy, after the buffer. -/
def schOff : Nat := bufOff + 8

/-- The schedule (at `a0`, through `t2`, which the copy advances) to its
copy in the frame. -/
def modePrepare : Prog isa :=
  .seq (.block ([.addi rowPtr sb schOff, .addi .t2 .a0 0] ++ li4168)) (copyLoop .t1 .t2 rowPtr tmp)

/-- The buffer's block encrypted (`up`) or decrypted in place under the
schedule's copy. -/
def modeCrypt (up : Bool) : Prog isa :=
  .seq (.block [.addi sch sb schOff, .addi ptr sb bufOff])
    (.seq (.block loadBlock) (.seq (cipher up) (.block storeBlock)))

/-- Blowfish's core for the modes, encrypting (`up`) or decrypting. -/
def dirCore (up : Bool) : Modes.RISCV64.Core where
  prepare := modePrepare
  crypt := modeCrypt up
  total := 528
  buf := bufSlot
  G := 1
  bw := 2

/-- `vg_blowfish_cbc_encrypt_chained`. -/
def cbcEncryptChained : Prog isa := (dirCore true).seq (Modes.Mode.cbcEncChained 2)

/-- `vg_blowfish_cbc_decrypt_chained`. -/
def cbcDecryptChained : Prog isa := (dirCore false).seq (Modes.Mode.cbcDecChained 2)

/-- `vg_blowfish_ofb`. -/
def ofb : Prog isa := (dirCore true).seq (Modes.Mode.ofb 2)

/-- `vg_blowfish_cfb64_encrypt`. -/
def cfbEncrypt : Prog isa := (dirCore true).seq (Modes.Mode.cfbEnc 2)

/-- `vg_blowfish_cfb64_decrypt`. -/
def cfbDecrypt : Prog isa := (dirCore true).seq (Modes.Mode.cfbDec 2)

end VG.Impl.Blowfish.RISCV64
