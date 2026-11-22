module

public import VerifiedGarbage.Impl.RsaOaep.PPC64LE

/-!
# HKDF (RFC 5869) on PPC64LE, with HMAC through a table

Three functions, each with HMAC over the hash function of the table `hmac`
of the interface `Hmac` (`Spec/HmacTable.lean`), whose functions they call
indirectly (`tcall`: the table's word `j` into `r12`, then `bctrl`): HMAC's
`init` for a key of any length (word 0), the streaming `update` (word 1)
and HMAC's `finalize` (word 2), each with its working space in `r7`, in our
frame (`work` bytes: that of `init` for a key longer than a block, the
most). The digest length `D` and HMAC's block size `B` are the table's
words of data 4 and 5, which the code loads where it needs them: nothing in
the code depends on the hash function but those two words and the table's
functions.

* `vg_hkdf_key(prk = r3, prk_len = r4, key = r5, hmac = r6)` (`key`):
  `init` with `PRK` as the key, into the states at `key` and `key + 192`.
* `vg_hkdf_extract(salt = r3, salt_len = r4, ikm = r5, ikm_len = r6,
  prk = r7, prk_len = r8, hmac = r9)` (`extract`): `init` with the salt as
  the key, into the inner and outer states in the frame; `update` with the
  input keying material; `finalize`, which writes the MAC, `PRK`, to `prk`.
* `vg_hkdf_expand(key = r3, info = r4, info_len = r5, out = r6,
  out_len = r7, hmac = r8)` (`expand`): unless `out_len` is 0, for each
  block `T(i)` (`block`): the inner state at `key` made the working state in
  the frame, by copying its first 64 bytes (`copyLoop`, a byte at a time):
  the inner state holds a whole block of key, so its hash value, at most 64
  bytes, is all of it that matters; `update` with `T(i - 1)` (the `r22`
  bytes at `T` in the frame: none for the first block, `D` after), then with
  `info`, then with the counter `i` (a byte, kept in `r23`); `finalize` with
  the outer state at `key + 192`, which writes `T(i)` to the frame; and its
  first `min(D, rem)` bytes (chosen with no branch, `minArgs`), `rem` the
  bytes of `out` still to write (in `r19`), copied to `out` (in `r18`) by
  `copyLoop`. `key` is only read.

Each runs in a frame (`alloc`) whose first doubleword past its header holds
our return address (moved to `r0` by `mflr`), which the calls replace, then
our caller's registers it uses; our variables live in callee-saved
registers, which the functions we call keep. Each block that touches the
frame first puts its base in `r11` (`addi r11, r1, 0`), since a call leaves
`r0`, `r11` and `r12` unknown. The functions we call use the stack below the
frame (144 bytes for `init`, 96 for `finalize`). Every address depends only
on the pointers and `D`, and every branch only on lengths.
-/

@[expose] public section

namespace VG.Impl.Hkdf.PPC64LE

open VG.PPC64LE
open VG.Impl.AesGcm.PPC64LE (mov)
open VG.Impl.RsaOaep.PPC64LE (Fns copyLoop)

/-- The working space the table's functions get: `init`'s for a key of any
length, the most (SHA-512's 234 doublewords). -/
def work : Nat := 1872

/-- The indirect call of the table's function `j`, among `ts`, with the
table in `t`: its word `j` into `r12`, then `bctrl`. -/
def tcall (t : Reg) (j : Nat) (ts : List (String × Prog isa)) : Prog isa :=
  .seq (.block [.load .d .r12 t (8 * j)]) (Code.icalls .bctrl ts)

/-- Where the return address is in each frame. -/
def oLr : Nat := 32

/-- The return address into the frame. -/
def saveLr : List Instr := [.mflr .r0, .addSp .r11 0, .store .d .r0 .r11 oLr]

/-- The return address back from the frame. -/
def restoreLr : List Instr := [.addSp .r11 0, .load .d .r0 .r11 oLr, .mtlr .r0]

/-! ## Keying HMAC -/

/-- Where the working space is in `key`'s frame. -/
def kW : Nat := 48
/-- `key`'s frame's size. -/
def kFr : Nat := kW + work

/-- The return address saved; `init`'s arguments: the states at `key` and
`key + 192`, `PRK` as the key, the working space; the table in `r8`. -/
def keyPro : List Instr :=
  saveLr ++ [mov .r8 .r6, mov .r9 .r3, mov .r10 .r4, mov .r3 .r5, .addi .r4 .r5 192, mov .r5 .r9,
    mov .r6 .r10, .addSp .r7 kW]

/-- The frame's body of `vg_hkdf_key`, whose table's `init` may be `f`'s. -/
def keyMain (f : Fns) : Prog isa :=
  .seq (.block keyPro) (.seq (tcall .r8 0 f.init) (.block restoreLr))

/-- `vg_hkdf_key`. -/
def key (f : Fns) : Prog isa := .frame (.alloc kFr) (keyMain f) (.free kFr)

/-! ## HKDF-Extract -/

/-- Our caller's registers `extract` uses, and where in its frame. -/
def xSaved : List (Reg × Nat) := [(.r14, 40), (.r15, 48), (.r16, 56), (.r17, 64)]

/-! Where things are in `extract`'s frame: the return address and the saved
registers, then HMAC's inner and outer states (192 bytes each), then the
working space. -/
def xIn : Nat := 80
def xOut : Nat := 272
def xW : Nat := 464
/-- `extract`'s frame's size. -/
def xFr : Nat := xW + work

/-- `extract`'s prologue: the return address and our caller's registers
saved; `ikm` and its length in `r14` and `r15`, `prk` in `r16`, the table in
`r17`; then `init`'s arguments: the states, the salt as the key, the working
space. -/
def extractPro : List Instr :=
  saveLr ++ xSaved.map (fun (r, d) => .store .d r .r11 d) ++
    [mov .r14 .r5, mov .r15 .r6, mov .r16 .r7, mov .r17 .r9, mov .r5 .r3, mov .r6 .r4, .addSp .r3 xIn,
      .addSp .r4 xOut, .addSp .r7 xW]

/-- `update`'s arguments: the inner state, which holds `B` bytes, the input
keying material, the working space. -/
def extractUpd : List Instr :=
  [.addSp .r3 xIn, .load .d .r4 .r17 40, mov .r5 .r14, mov .r6 .r15, .addSp .r7 xW]

/-- `finalize`'s arguments: the states, the `B + ikm_len` bytes the inner one
holds, `prk`, the working space. -/
def extractFin : List Instr :=
  [.addSp .r3 xIn, .addSp .r4 xOut, .load .d .r5 .r17 40, .add .r5 .r5 .r15, mov .r6 .r16, .addSp .r7 xW]

/-- The return address and our caller's registers restored. -/
def extractEpi : List Instr := restoreLr ++ xSaved.map fun (r, d) => .load .d r .r11 d

/-- The frame's body of `vg_hkdf_extract`, whose table's functions may be
`f`'s. -/
def extractMain (f : Fns) : Prog isa :=
  .seq (.block extractPro)
  (.seq (tcall .r17 0 f.init)
  (.seq (.block extractUpd)
  (.seq (tcall .r17 1 f.upd)
  (.seq (.block extractFin)
  (.seq (tcall .r17 2 f.fin)
    (.block extractEpi))))))

/-- `vg_hkdf_extract`. -/
def extract (f : Fns) : Prog isa := .frame (.alloc xFr) (extractMain f) (.free xFr)

/-! ## HKDF-Expand -/

/-- Our caller's registers `expand` uses, and where in its frame. -/
def eSaved : List (Reg × Nat) :=
  [(.r14, 40), (.r15, 48), (.r16, 56), (.r17, 64), (.r18, 72), (.r19, 80), (.r20, 88), (.r21, 96),
    (.r22, 104), (.r23, 112)]

/-! Where things are in `expand`'s frame: the return address and the saved
registers, the working state (192 bytes), `T(i)` (64 bytes), the counter's
byte, then the working space. -/
def eWs : Nat := 120
def eT : Nat := 312
def eC : Nat := 376
def eW : Nat := 384
/-- `expand`'s frame's size. -/
def eFr : Nat := eW + work

/-- `expand`'s prologue: the return address and our caller's registers
saved; the table in `r14`, `key` in `r15`, `info` and its length in `r16`
and `r17`, `out` in `r18`, the bytes of `out` left in `r19`, `D` and `B` in
`r20` and `r21`, the length of `T(i - 1)` (none yet) in `r22` and the counter
`i = 1` in `r23`. -/
def expandPro : List Instr :=
  saveLr ++ eSaved.map (fun (r, d) => .store .d r .r11 d) ++
    [mov .r14 .r8, mov .r15 .r3, mov .r16 .r4, mov .r17 .r5, mov .r18 .r6, mov .r19 .r7,
      .load .d .r20 .r14 32, .load .d .r21 .r14 40, .li .r22 0, .li .r23 1]

/-- The copy's arguments: the inner state at `key` in `r4`, the working state
in `r5`, and the 64 bytes to copy in `r6`. -/
def copyArgs : List Instr := [mov .r4 .r15, .addSp .r5 eWs, .li .r6 64]

/-- `update`'s arguments for `T(i - 1)`: the working state, which holds `B`
bytes, the `r22` bytes at `T`, the working space. -/
def updT : List Instr := [.addSp .r3 eWs, mov .r4 .r21, .addSp .r5 eT, mov .r6 .r22, .addSp .r7 eW]

/-- `update`'s arguments for `info`: the working state, which holds
`B + r22` bytes. -/
def updI : List Instr := [.addSp .r3 eWs, .add .r4 .r21 .r22, mov .r5 .r16, mov .r6 .r17, .addSp .r7 eW]

/-- The counter's byte stored; `update`'s arguments for it: the working
state, which holds `B + r22 + info_len` bytes, and the byte. -/
def updC : List Instr :=
  [.addSp .r11 0, .stb .r23 .r11 eC, .addSp .r3 eWs, .add .r4 .r21 .r22, .add .r4 .r4 .r17, .addSp .r5 eC,
    .li .r6 1, .addSp .r7 eW]

/-- `finalize`'s arguments: the working state, which holds
`B + r22 + info_len + 1` bytes, the outer state at `key + 192`, `T`, the
working space. -/
def finT : List Instr :=
  [.addSp .r3 eWs, .addi .r4 .r15 192, .add .r5 .r21 .r22, .add .r5 .r5 .r17, .addi .r5 .r5 1,
    .addSp .r6 eT, .addSp .r7 eW]

/-- The copy's arguments: `r6 = min(D, rem)` (`D + ((rem - D) & -(rem < D))`,
`rem` the bytes of `out` left in `r19`, whose comparison with `D` is the top
bit of their difference), kept in `r9`, `T` in `r4` and `out` in `r5`; and
`rem` less those bytes. -/
def outArgs : List Instr :=
  [.sub .r10 .r19 .r20, .lsr .d .r6 .r10 63, .li .r7 0, .sub .r6 .r7 .r6, .logic .and .r10 .r10 .r6,
    .add .r6 .r20 .r10, mov .r9 .r6, .addSp .r4 eT, mov .r5 .r18, .sub .r19 .r19 .r6]

/-- After the copy: `out` past the bytes written, `T(i)`'s `D` bytes the next
block's `T(i - 1)`, and the next counter. -/
def nextBlock : List Instr := [.add .r18 .r18 .r9, mov .r22 .r20, .addi .r23 .r23 1]

/-- One block `T(i)`, whose table's functions may be `f`'s: `T(i)` into the
frame, its first `min(D, rem)` bytes to `out`. -/
def block (f : Fns) : Prog isa :=
  .seq (.seq (.block copyArgs) copyLoop)
  (.seq (.seq (.block updT) (tcall .r14 1 f.upd))
  (.seq (.seq (.block updI) (tcall .r14 1 f.upd))
  (.seq (.seq (.block updC) (tcall .r14 1 f.upd))
  (.seq (.seq (.block finT) (tcall .r14 2 f.fin))
  (.seq (.block outArgs)
  (.seq copyLoop
    (.block nextBlock)))))))

/-- The return address and our caller's registers restored. -/
def expandEpi : List Instr := restoreLr ++ eSaved.map fun (r, d) => .load .d r .r11 d

/-- The frame's body of `vg_hkdf_expand`, whose table's functions may be
`f`'s: the blocks while bytes of `out` are left. -/
def expandMain (f : Fns) : Prog isa :=
  .seq (.block expandPro)
  (.seq (.ite (.nonzero .d .r19) (.loop (block f) (.nonzero .d .r19)) (.block []))
    (.block expandEpi))

/-- `vg_hkdf_expand`. -/
def expand (f : Fns) : Prog isa := .frame (.alloc eFr) (expandMain f) (.free eFr)

end VG.Impl.Hkdf.PPC64LE
