module

public import VerifiedGarbage.Impl.Modes.PPC64LE.Seq
public import VerifiedGarbage.Impl.Modes.CbcChained
public import VerifiedGarbage.Impl.Cast5.PPC64LE

/-!
# CAST5's modes on PPC64LE

`dirCore up n`: ECB's block function (`crypt`), inlined, as a core for the
modes (`Impl/Modes/PPC64LE/Seq.lean`), encrypting (`up`) or decrypting the
block in its buffer in place with `n` rounds. The buffer is slot 0 of the
scratch buffer, so its address is `sb` (`r5`), which the block function
keeps, as it keeps `r3` (the schedule), `r31` and `r6`/`r7`. Of the modes'
state, it writes `r29` and `r30`, which the core keeps in `r6` and `r7`
meanwhile, rather than in memory, so they stay public; our caller's
`r14`–`r28`, which it writes too, are saved in slots 1 to 15. Each block,
the core forms the table's address (`adrSym`, which writes the link
register, which the mode saved), 255, zero and the count of rounds in the
registers the block function reads them from. 16 slots, the modes' 6 after
them: 22 in all (`[u64; 22]`).

The functions take the number of rounds as their second argument, which the
modes' code does not: `modeFn m` moves `rounds` to `r10` and the others
down to the modes' registers (schedule = r3, iv = r4, data = r5, n = r6,
scratch = r7), then branches on the public `rounds` (12 or 16) to the mode
`m n` over the core with that count.
-/

@[expose] public section

namespace VG.Impl.Cast5.PPC64LE

open VG.PPC64LE
open VG.Impl.Modes.PPC64LE (sb)

/-- Our caller's registers the core saves, and their slots: those the block
function writes, but `r29` and `r30`. -/
def modeSaved : List (Reg × Nat) :=
  [.r14, .r15, .r16, .r17, .r18, .r19, .r20, .r21, .r22, .r23, .r24, .r25, .r26, .r27, .r28].zipIdx.map
    fun (r, i) => (r, 8 * (i + 1))

/-- The block in slot 0 encrypted (`up`) or decrypted with `n` rounds:
`r29`, `r30` to `r6`, `r7`, our caller's registers saved, the table's
address, 255, zero and `n` set, the block function, and the registers
back. -/
def modeCrypt (up : Bool) (n : Nat) : Prog isa :=
  .seq (.block (([mov .r6 .r29, mov .r7 .r30] : List Instr) ++ modeSaved.map (fun (r, d) => .store .d r sb d) ++
      ([.adrSym tbl s1234Sym, .li c255 255, .li zero 0, .li rnd n] : List Instr)))
    (.seq (crypt up sb)
      (.block (modeSaved.map (fun (r, d) => .load .d r sb d) ++ ([mov .r29 .r6, mov .r30 .r7] : List Instr))))

/-- CAST5's core for the modes, encrypting (`up`) or decrypting with `n` rounds. -/
def dirCore (up : Bool) (n : Nat) : Modes.PPC64LE.Core where
  prepare := .block []
  crypt := modeCrypt up n
  slots := 16
  total := 22
  buf := 0
  G := 1
  bw := 2

/-- `f(schedule = r3, rounds = r4, iv = r5, data = r6, n = r7, scratch =
r8)`: the mode `m 12` or `m 16`, as `rounds` says, with the arguments in
the modes' registers. -/
def modeFn (m : Nat → Prog isa) : Prog isa :=
  .seq (.block [mov .r10 .r4, mov .r4 .r5, mov .r5 .r6, mov .r6 .r7, mov .r7 .r8, .subi .r10 .r10 12])
    (.ite (.zero .d .r10) (m 12) (m 16))

/-- `vg_cast5_cbc_encrypt_chained`, with its scratch buffer as the sixth argument. -/
def cbcEncryptChained : Prog isa := modeFn fun n => (dirCore true n).seq (Modes.Mode.cbcEncChained 2)

/-- `vg_cast5_cbc_decrypt_chained`, with its scratch buffer as the sixth argument. -/
def cbcDecryptChained : Prog isa := modeFn fun n => (dirCore false n).seq (Modes.Mode.cbcDecChained 2)

/-- `vg_cast5_ofb`, with its scratch buffer as the sixth argument. -/
def ofb : Prog isa := modeFn fun n => (dirCore true n).seq (Modes.Mode.ofb 2)

/-- `vg_cast5_cfb64_encrypt`, with its scratch buffer as the sixth argument. -/
def cfbEncrypt : Prog isa := modeFn fun n => (dirCore true n).seq (Modes.Mode.cfbEnc 2)

/-- `vg_cast5_cfb64_decrypt`, with its scratch buffer as the sixth argument. -/
def cfbDecrypt : Prog isa := modeFn fun n => (dirCore true n).seq (Modes.Mode.cfbDec 2)

end VG.Impl.Cast5.PPC64LE
