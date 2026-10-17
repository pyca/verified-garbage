module

public import VerifiedGarbage.Impl.Modes.AArch64.Cbc
public import VerifiedGarbage.Impl.Modes.AArch64.CbcEnc
public import VerifiedGarbage.Impl.Modes.AArch64.Fb

/-!
# CBC on AArch64 that updates the chaining value, for any block cipher with blocks of 8 or 16 bytes

`cbcEncryptChained core regs iv` and `cbcDecryptChained core regs`: the
modes' CBC encryption and decryption (`CbcEnc.lean`, `Cbc.lean`), which
also replace the IV with the chaining value to continue from, `Cₙ`, the last
ciphertext block (and leave it unchanged if `n = 0`). As on x86-64
(`Impl/Modes/X86_64/CbcChained.lean`):

* Encryption keeps the IV's address in the register `iv`, which the core
  keeps, as OFB and CFB do (`Fb.lean`), and after the last block copies the
  core's buffer, which still holds `Cₙ`, back to the IV (`fbStore`).
* Decryption copies the last block of the data, `Cₙ`, to the IV at entry,
  after the IV has gone to the chaining value's slots and before any block
  is decrypted: its address, `data + 8 bw (n - 1)`, is computed from the
  arguments, which are public.

Only the pointers and `n` (and what is computed from them) are public; no
address or branch depends on the key, the IV or the data.
-/

@[expose] public section

namespace VG.Impl.Modes.AArch64

open VG.AArch64 VG.Impl.Aes.AArch64

namespace Core

variable (c : Core)

/-- `log₂` of a block's size in bytes (`8 bw`, for `bw` of 1 or 2). -/
def blkShift : Nat := if c.bw = 1 then 3 else 4

/-- The address of the last block, `r.data + 8 bw (r.n - 1)`, to `x7`. -/
def lastAddr (r : CtrRegs) : List Instr :=
  [.subImm .x .x7 r.n 1, .lsl .x .x7 .x7 c.blkShift, .add .x .x7 .x7 r.data]

/-- The last block of the data to the IV at `r.ctr` (through `x6`), unless
`r.n` is zero. -/
def cbcLastToIv (r : CtrRegs) : Prog isa :=
  .ite (.zero .x r.n) (.block []) (.block (c.lastAddr r ++ (List.range c.bw).flatMap (copyW .x6 r.ctr .x7 0 0)))

/-- `cbcDecrypt`, with the last block of the data to the IV once the IV is
in the chaining value's slots. -/
def cbcDecryptChained (r : CtrRegs) : Prog isa :=
  .seq (.block (c.ctrEntry r ++ c.cbcSetup r))
    (.seq (c.cbcLastToIv r)
      (.seq (.block (c.ctrArgs r))
        (.seq c.prepare
          (.seq (.ite (.zero .x c.leftReg) (.block []) (.loop c.cbcDecGroup (.nonzero .x c.leftReg)))
            (.block c.restoreRegs)))))

/-- `cbcEncrypt`, with the IV's address in `iv` and the buffer, the last
ciphertext block, back to the IV after the blocks. -/
def cbcEncryptChained (r : CtrRegs) (iv : Reg) : Prog isa :=
  .seq (.block (c.ctrEntry r ++ ([movR iv r.ctr] : List Instr))) (.seq (c.cbcWhiten r) (.seq (.block (c.ctrArgs r))
    (.seq c.prepare
      (.seq (.ite (.zero .x c.leftReg) (.block [])
          (.seq (.loop c.cbcEncBlock (.nonzero .x c.leftReg)) (.block (c.fbStore iv))))
        (.block c.restoreRegs)))))

end Core

end VG.Impl.Modes.AArch64
