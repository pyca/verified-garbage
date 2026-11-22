module

public import VerifiedGarbage.Impl.Modes.CbcChained
public import VerifiedGarbage.Impl.TripleDes.RISCV64.Ecb
public import VerifiedGarbage.Impl.TripleDes.RISCV64.Bitsliced
public import VerifiedGarbage.Impl.Modes.RISCV64.Wide
public import VerifiedGarbage.Impl.Modes.RISCV64.Shared

/-!
# Triple DES's modes on RISC-V

`cbcEncryptChained`, `ofb`, `cfbEncrypt`, `cfb8Encrypt` and `cfb8Decrypt`
(schedule = a0, iv = a1, data = a2, n = a3), whose blocks each need the one
before, are the modes (`Impl/Modes/RISCV64/Seq.lean`) over `dirCore`
(`Ecb.lean`), the block function, with the encryption (CBC with its
direction).

`wideCore d`: the bitsliced ECB of the direction `d` (`Bitsliced.lean`) on
the 64 blocks of its buffer, as a core for CBC and CFB decryption, whose
blocks are deciphered independently (`Impl/Modes/RISCV64/Wide.lean`). The
buffer is ECB's 64 state words, at slot 6 as `dirCore`'s one block is, so
that ECB's working space starts there (`wideOff`) and its copy of the
schedules is the block function's (`keyOff`); its masks and the registers
it saves follow (slots 118 to 137), 138 slots in all, and two more for the
call (`Core.shared`). `prepare` copies the schedules as `dirCore`'s does
and stores the masks; `crypt` transposes the buffer, runs the three passes
and transposes it back.

The passes write every register but `a1`, `a2`, `s11` and their base
(`s0`), and the calls of the passes and of the transposition write `ra`;
memory is secret to the analysis of constant time, so the modes' state
(`s1`–`s3`, which address and count) waits in `a1`, `a2` and `s11`
(`wideIn`), and the frame's base (`s4`) is ECB's base less `wideOff`
(`wideOut`). The return address, the caller's `s0` and `s5`–`s11` and the
key's argument `a0` wait in the working space: they come back secret, and
nothing addresses or branches on them after.

ECB costs the same whatever the number of blocks, about three blocks by the
block function: so the blocks left after the groups of 64 go by groups of
32, 16, 8 and 4 (`levels`, at most one of each), and the fewer than four
left after them one at a time by the block function on the buffer's first
block (`Core.seqLevelsWith`), which writes only the buffer and the copy of
the schedules' slots before the masks. As on PPC64LE
(`Impl/TripleDes/PPC64LE/Modes.lean`).
-/

@[expose] public section

namespace VG.Impl.TripleDes.RISCV64

open VG.RISCV64
open VG.Spec.TripleDes (Direction)

/-- ECB's base, as an offset from the frame's: the buffer. -/
def wideOff : Nat := 8 * bufSlot

/-- The return address, the key's argument and the caller's registers the
passes write, and where they wait, as offsets from ECB's base; the base
itself last. -/
def wideSaved : List (Reg × Nat) :=
  [(.ra, 968), (.a0, 1032), (.s5, 976), (.s6, 984), (.s7, 992), (.s8, 1000), (.s9, 1008), (.s10, 1016), (.s11, 1024),
    (.s0, 1040)]

/-- The schedules copied as the block function has them, and ECB's masks
stored, with its base in `s0` meanwhile (the caller's in `t5`). -/
def widePrepare : Prog isa :=
  .seq modePrepare (.block ([movR .t5 Bitslice.base, .addi Bitslice.base sb wideOff] ++ Bitslice.storeMasks ++
    ([movR Bitslice.base .t5] : List Instr)))

/-- `a0` and the caller's registers to the working space, ECB's base, and
the modes' state to `a1`, `a2` and `s11`. -/
def wideIn : List Instr :=
  .addi .t0 sb wideOff :: (wideSaved.map (fun (r, o) => .store .d r .t0 o) ++
    ([movR Bitslice.base .t0, movR .a1 .s1, movR .a2 .s2, movR .s11 .s3] : List Instr))

/-- The modes' state back, the frame's base, `a0` and the caller's registers. -/
def wideOut : List Instr :=
  [movR .s1 .a1, movR .s2 .a2, movR .s3 .s11, .addi sb Bitslice.base (-(wideOff : Int))] ++
    wideSaved.map (fun (r, o) => .load .d r Bitslice.base o)

/-- The buffer's 64 blocks, transposed, through the three passes, and back. -/
def wideCrypt (d : Direction) : Prog isa :=
  .seq (.block wideIn) (.seq Bitslice.transposeCall (.seq (Bitslice.passes d)
    (.seq Bitslice.transposeCall (.block wideOut))))

/-- Triple DES's core for the modes, in the direction `d`, on 64 blocks. -/
def wideInline (d : Direction) : Modes.RISCV64.Core where
  prepare := widePrepare
  crypt := wideCrypt d
  total := 138
  buf := bufSlot
  G := 64
  bw := 2

/-- The core on 64 blocks, its preparation and its batch called. -/
def wideCore (d : Direction) : Modes.RISCV64.Core :=
  (wideInline d).shared "vg_triple_des_modes_prepare"
    ("vg_triple_des_modes_crypt_" ++ (if d = .encrypt then "encrypt" else "decrypt"))

/-- The block function of the direction `d` on the wide core's first block. -/
def wideOne (d : Direction) : Prog isa := block d sb bufOff

/-- The groups of the wide modes, `2 ^ lg` blocks for each `lg` in turn. -/
def levels : List Nat := [6, 5, 4, 3, 2]

/-- `vg_triple_des_cbc_encrypt_chained`. -/
def cbcEncryptChained : Prog isa := (dirCore .encrypt).seq (Modes.Mode.cbcEncChained 2)

/-- `vg_triple_des_cbc_decrypt_chained`. -/
def cbcDecryptChained : Prog isa :=
  (wideCore .decrypt).seqLevelsWith (wideOne .decrypt) levels (Modes.Mode.cbcDecChained 2)

/-- `vg_triple_des_ofb`. -/
def ofb : Prog isa := (dirCore .encrypt).seq (Modes.Mode.ofb 2)

/-- `vg_triple_des_cfb64_encrypt`. -/
def cfbEncrypt : Prog isa := (dirCore .encrypt).seq (Modes.Mode.cfbEnc 2)

/-- `vg_triple_des_cfb64_decrypt`. -/
def cfbDecrypt : Prog isa :=
  (wideCore .encrypt).seqLevelsWith (wideOne .encrypt) levels (Modes.Mode.cfbDecEarly 2)

/-- `vg_triple_des_cfb8_encrypt`. -/
def cfb8Encrypt : Prog isa := (dirCore .encrypt).seq (Modes.Mode.cfb8Enc 2)

/-- `vg_triple_des_cfb8_decrypt`. -/
def cfb8Decrypt : Prog isa := (dirCore .encrypt).seq (Modes.Mode.cfb8Dec 2)

end VG.Impl.TripleDes.RISCV64
