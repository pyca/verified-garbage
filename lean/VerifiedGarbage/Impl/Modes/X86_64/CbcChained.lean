module

public import VerifiedGarbage.Impl.Modes.X86_64.Cbc
public import VerifiedGarbage.Impl.Modes.X86_64.CbcEnc
public import VerifiedGarbage.Impl.Modes.X86_64.Fb

/-!
# CBC on x86-64 that updates the chaining value, for any block cipher with blocks of 8 or 16 bytes

`cbcEncryptChained core regs` and `cbcDecryptChained core regs`: the modes'
CBC encryption and decryption (`CbcEnc.lean`, `Cbc.lean`), which also
replace the IV with the chaining value to continue from, `Cₙ`, the last
ciphertext block (and leave it unchanged if `n = 0`):

* Encryption keeps the IV's address in `xmm15`, as OFB and CFB do
  (`Fb.lean`: a core whose code is scalar leaves it alone, and a slot would
  not do for the constant-time analysis), and after the last block copies
  the core's buffer, which still holds `Cₙ`, back to the IV (`fbStore`).
* Decryption copies the last block of the data, `Cₙ`, to the IV at entry,
  after the IV has gone to the chaining value's slots and before any block
  is decrypted: its address, `data + 8 bw (n - 1)`, is computed from the
  arguments, which are public.

Only the pointers and `n` (and what is computed from them) are public; no
address or branch depends on the key, the IV or the data.
-/

@[expose] public section

namespace VG.Impl.Modes.X86_64

open VG.X86_64 VG.Impl.Aes.X86_64

namespace Core

variable (c : Core)

/-- `log₂` of a block's size in bytes (`8 bw`, for `bw` of 1 or 2). -/
def blkShift : Nat := if c.bw = 1 then 3 else 4

/-- The address of the last block, `r.data + 8 bw (r.n - 1)`, to `rax`. -/
def lastAddr (r : CtrRegs) : List Instr :=
  [movR .rax r.n, .alu .sub .rax (.imm 1), .shift .shl .rax c.blkShift, .alu .add .rax (.reg r.data)]

/-- The last block of the data to the IV at `r.ctr` (through `rbx`), unless
`r.n` is zero. -/
def cbcLastToIv (r : CtrRegs) : Prog isa :=
  .seq (.block [.alu .test r.n (.reg r.n)])
    (.ite .e (.block []) (.block (c.lastAddr r ++ (List.range c.bw).flatMap (copyW .rbx r.ctr .rax 0 0))))

/-- `cbcDecrypt`, with the last block of the data to the IV once the IV is
in the chaining value's slots. -/
def cbcDecryptChained (r : CtrRegs) : Prog isa :=
  .seq (.block (c.ctrEntry r ++ c.cbcSetup r))
    (.seq (c.cbcLastToIv r)
      (.seq (.block (c.ctrArgs r))
        (.seq c.prepare
          (.seq (.block [.alu .test c.leftReg (.reg c.leftReg)])
            (.seq (.ite .e (.block []) (.loop c.cbcDecGroup .ne)) (.block c.restoreRegs))))))

/-- `cbcEncrypt`, with the IV's address in `ivX` and the buffer, the last
ciphertext block, back to the IV after the blocks. -/
def cbcEncryptChained (r : CtrRegs) : Prog isa :=
  .seq (.block (c.ctrEntry r ++ ([.xop (.movq ivX r.ctr)] : List Instr)))
    (.seq (c.cbcWhiten r) (.seq (.block (c.ctrArgs r))
      (.seq c.prepare
        (.seq (.block [.alu .test c.leftReg (.reg c.leftReg)])
          (.seq (.ite .e (.block []) (.seq (.loop c.cbcEncBlock .ne) (.block c.fbStore)))
            (.block c.restoreRegs))))))

end Core

end VG.Impl.Modes.X86_64
