module

public import VerifiedGarbage.Impl.Modes.RISCV64.Seq
public import VerifiedGarbage.Impl.Modes.RISCV64.Wide
public import VerifiedGarbage.Impl.Modes.Wide
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

`dirCore2 up`: the same with ECB's block function of two blocks
(`cipher2`), on the buffer's two blocks (slots 6 and 7), the schedule's copy
after them (from slot 8). That function writes `s1`–`s10`, among them the
modes' state. Memory is secret to the analysis of constant time, so the
modes' state, which addresses and counts, waits in registers the function
does not write: `s1`–`s3` in `s0`, `s11` and `ra` (`park2`), and `s4`, the
frame's base, is the copy's address in `sch` less its offset (`unpark2`).
The caller's `s0`, `s5`–`s11` and `ra` are saved in nine slots after the
copy (from slot 529, `saved2`), through `t0`, which the core sets from the
copy's address (`slotBase`), and restored after: 540 slots in all.

`cbcEncryptChained`, `ofb` and `cfbEncrypt` (schedule = a0, iv = a1,
data = a2, n = a3) are the modes over `dirCore`, with the encryption but
CBC encryption's; `cbcDecryptChained` and `cfbDecrypt`, whose blocks can be
deciphered independently, take two blocks a step over `dirCore2` while two
are left (`Core.seq2`), then one.
-/

@[expose] public section

namespace VG.Impl.Blowfish.RISCV64

open VG.RISCV64
open VG.Impl.Modes.RISCV64 (sb mov)
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

/-! ## Two blocks a step -/

/-- The schedule's copy for two blocks, after the buffer's two. -/
def schOff2 : Nat := bufOff + 16

/-- The schedule (at `a0`) to its copy at `schOff2`. -/
def modePrepare2 : Prog isa :=
  .seq (.block ([.addi rowPtr sb schOff2, .addi .t2 .a0 0] ++ li4168)) (copyLoop .t1 .t2 rowPtr tmp)

/-- The registers the two-block core saves, and their offsets from `t0`. -/
def saved2 : List (Reg × Nat) :=
  [(.s0, 0), (.s5, 8), (.s6, 16), (.s7, 24), (.s8, 32), (.s9, 40), (.s10, 48), (.s11, 56), (.ra, 64)]

/-- The modes' `s1`–`s3` to `s0`, `s11` and `ra`. -/
def park2 : List Instr := [mov .s0 .s1, mov .s11 .s2, mov .ra .s3]

/-- The modes' `s1`–`s3` back, and the frame's base from the copy's address. -/
def unpark2 : List Instr := [mov .s1 .s0, mov .s2 .s11, mov .s3 .ra, .addi sb sch (-(schOff2 : Int))]

/-- `t0` at the saved registers' slots, from the copy's address in `sch`. -/
def slotBase : List Instr := [.addi rowPtr sch 2047, .addi rowPtr rowPtr 2047, .addi rowPtr rowPtr 74]

/-- The buffer's two blocks encrypted (`up`) or decrypted in place under the
schedule's copy, the registers saved and the modes' state parked around it. -/
def modeCrypt2 (up : Bool) : Prog isa :=
  .seq (.block ([.addi sch sb schOff2, .addi ptr sb bufOff] ++ slotBase ++
      saved2.map (fun (r, d) => .store .d r rowPtr d) ++ park2))
    (.seq (.block loadBlock2) (.seq (cipher2 up)
      (.block (storeBlock2 ++ unpark2 ++ slotBase ++ saved2.map fun (r, d) => .load .d r rowPtr d))))

/-- Blowfish's core for the modes, two blocks at a time. -/
def dirCore2 (up : Bool) : Modes.RISCV64.Core where
  prepare := modePrepare2
  crypt := modeCrypt2 up
  total := 540
  buf := bufSlot
  G := 2
  bw := 2

/-- `vg_blowfish_cbc_encrypt_chained`. -/
def cbcEncryptChained : Prog isa := (dirCore true).seq (Modes.Mode.cbcEncChained 2)

/-- `vg_blowfish_cbc_decrypt_chained`: two blocks a step, then one. -/
def cbcDecryptChained : Prog isa :=
  (dirCore2 false).seq2 (Modes.Mode.cbcDecWide 2 2) (Modes.Mode.cbcDecChained 2) 1

/-- `vg_blowfish_ofb`. -/
def ofb : Prog isa := (dirCore true).seq (Modes.Mode.ofb 2)

/-- `vg_blowfish_cfb64_encrypt`. -/
def cfbEncrypt : Prog isa := (dirCore true).seq (Modes.Mode.cfbEnc 2)

/-- `vg_blowfish_cfb64_decrypt`: two blocks a step, then one. -/
def cfbDecrypt : Prog isa :=
  (dirCore2 true).seq2 (Modes.Mode.cfbDecWide 2 2) (Modes.Mode.cfbDecEarly 2) 1

end VG.Impl.Blowfish.RISCV64
