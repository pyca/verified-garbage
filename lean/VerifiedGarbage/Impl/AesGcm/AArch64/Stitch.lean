module

public import VerifiedGarbage.Impl.AesGcm.AArch64.Fast
public import VerifiedGarbage.Impl.Gcm.AArch64.Stitch
public import VerifiedGarbage.Impl.AesGcm.AArch64.SealGather

/-!
# AES-GCM on AArch64: the path for TLS records, interleaved

The path for TLS records (`Fast.lean`) of the functions with the powers
(`_with_powers`, `_store_powers`), for CPUs with FEAT_AES, FEAT_PMULL and
FEAT_SHA3: the first `128 ⌊len / 128⌋` bytes of the
text encrypted (or decrypted) and hashed by the interleaved loops of
`Impl.Gcm.AArch64.Stitch`, then the rest as `Fast.lean` does.

* The loops read the table of keys at `W + 512` (`Stitch.tbl`), which
  `tbl` writes from `H'` to `H'⁸` in `tReg`/`sReg`
  (`Impl.Gcm.AArch64.Pmull`): computed as `vg_ghash_aes` computes them
  (`powTbl`, for `_store_powers`), or loaded from `pw` (`pwTbl`, for
  `_with_powers`). Plain `seal` and `open`, which would compute the powers
  on every call, keep `Fast.lean`'s path.
* Only a text of at least `minLen` bytes takes the loops (`thr`); a shorter
  one takes `Fast.lean`'s path, as the `_aes` functions do. Writing the
  table and the loops' first and last steps cost about as much as 3.4 to 6.2
  of the loops' 128-byte steps save (measured on Neoverse N2: 600-byte texts
  slower, 1023-byte ones faster; pyca/verified-garbage#2758).
* `open` decrypts the first bytes before it knows whether the tag is right:
  it keeps the first counter block at `W + cbO`, and if the tag is wrong
  encrypts those bytes again from it, which leaves them as they were.
-/

@[expose] public section

namespace VG.Impl.AesGcm.AArch64.Stitch

open VG.AArch64
open VG.Impl.AesGcm.AArch64.Fast
open VG.Impl.Gcm.AArch64.Pmull (tReg sReg powers loadPw loadRev Y)

/-- Where `open` keeps the first counter block. -/
def cbO : Nat := 320

/-- The table of keys from `H'` to `H'⁸` in `tReg` and `sReg`: each power
with its halves swapped, then the sums of each power's halves, two to a
register, for the pairs of `ghPart`. -/
def tbl : List Instr :=
  (List.range 8).flatMap (fun k => [.strq (sReg (k + 1)) .x19 (Gcm.AArch64.Stitch.sOff (k + 1))]) ++
  (List.range 4).flatMap fun p =>
    [.vop (.logic .eor .v2 (sReg (Gcm.AArch64.Stitch.pk p)) (tReg (Gcm.AArch64.Stitch.pk p))),
     .vop (.logic .eor .v3 (sReg (Gcm.AArch64.Stitch.pl p)) (tReg (Gcm.AArch64.Stitch.pl p))),
     .vop (.ext .v4 .v2 .v3 8), .strq .v4 .x19 (Gcm.AArch64.Stitch.kOff p)]

/-- The table, from the powers computed from `H'` (kept at `W + hO`). -/
def powTbl : List Instr := hReload ++ powers ++ tbl

/-- The table, from the powers in `pw`, the stack argument at `sp + k`. -/
def pwTbl (k : Nat) : List Instr :=
  ([.ldrSp .x5 k] : List Instr) ++ (List.range 8).flatMap (fun k => loadPw (k + 1)) ++ tbl

/-- The shortest text the loops take, in bytes: six of their steps. -/
def minLen : Nat := 768

/-- `x9 = ⌊(x7 + 256) / 1024⌋`, zero exactly when the text's length `x7` is
less than `minLen`. -/
def thr : List Instr := [.addImm .x .x9 .x7 (1024 - minLen), .lsr .x .x9 .x9 10]

/-- `x9 = 128 ⌊x26 / 128⌋`, the bytes the loops take. -/
def whole : List Instr := [.lsr .x .x9 .x26 7, .lsl .x .x9 .x9 7]

/-- The loop `l` on the first `128 ⌊x26 / 128⌋` bytes at `x23`, after `pre`
and the table `tb`, if there are any. -/
def stitched (pre tb : List Instr) (l : Prog isa) : Prog isa :=
  .seq (.block [.lsr .x .x9 .x26 7]) (.ite (.zero .x .x9) (.block []) (.seq (.block (pre ++ tb)) l))

variable (c : Callees)

/-- `runWithP`, the first bytes encrypted and hashed by the interleaved loop. -/
def runWithS (tb : List Instr) (cl : Prog isa) : Prog isa :=
  .seq front
  (.seq (stitched [] tb Gcm.AArch64.Stitch.enc)
  (.seq (.block (whole ++ [.add .x .x23 .x23 .x9, mov .x27 .x23, .sub .x .x24 .x26 .x9, imm .x25 0]))
  (.seq (Tail.cryptAlT c)
  (.seq (.block ([mov .x23 .x27] ++ whole ++ [.sub .x .x24 .x26 .x9] ++ absSeg2 16))
  (.seq cl
  (.seq (.block (hReload ++ loadRev Y .x20 16 ++ [mov .x13 .x24, mov .x12 .x23]))
  (.seq padMulT
  (.seq (.block lensTag)
  (.seq (ctrCall c)
  (.seq (.block tagOut)
    (.block restore)))))))))))

/-- `openRunWithP`, the first bytes decrypted and hashed by the interleaved
loop, the first counter block kept; the rest decrypted if the tag is right,
and the first bytes encrypted again from it if not. -/
def openRunWithS (tb : List Instr) (cl : Prog isa) : Prog isa :=
  .seq front
  (.seq (.block [.ldrq .v0 .x20 48, .strq .v0 .x19 cbO])
  (.seq (stitched [] tb Gcm.AArch64.Stitch.dec)
  (.seq (.block (whole ++ [.add .x .x23 .x23 .x9, .sub .x .x24 .x26 .x9, imm .x25 0] ++ absSeg2 16))
  (.seq cl
  (.seq (.block (hReload ++ loadRev Y .x20 16 ++ [mov .x13 .x24, mov .x12 .x23]))
  (.seq padMulT
  (.seq (.block (lensTagAt uO))
  (.seq (ctrCall c)
  (.seq cmp
  (.seq (.block [imm .x27 1, .sub .x .x27 .x27 .x10])
  (.seq (.ite (.zero .x .x27)
      (.seq (.block ([.ldrq .v0 .x19 cbO, .strq .v0 .x20 48, .ldr .x .x23 .x19 dataO,
          .ldr .x .x26 .x19 lenO] ++ whole ++ [mov .x24 .x9, imm .x25 0])) (Tail.cryptAlT c))
      (.seq (.block ([.ldr .x .x23 .x19 dataO, .ldr .x .x26 .x19 lenO] ++ whole ++
          [.add .x .x23 .x23 .x9, .sub .x .x24 .x26 .x9, imm .x25 0])) (Tail.cryptAlT c)))
    (.block [mov .x0 .x27]))))))))))))

/-- `openFastP` with `openRunWithS`. -/
def openFastS (tb : List Instr) (cl : Prog isa) : Prog isa :=
  .seq tagLenOk
  (.seq (.ite (.zero .x .x9) (.block [imm .x0 0]) (.seq tagIn (openRunWithS c tb cl)))
    (.block restore))

/-! ## Short records

A TLS record of at most `shortMax` bytes (`seal`'s from 17 bytes) is sealed
or opened by one pass of each part of the loops, with no call. With
`n = ⌈len / 16⌉ ≤ 6` and `p = 7 − n`, two buffers of eight blocks in the
working space:

* `B₁` (at `W + b1O`) holds the text at block `p`, and zeros at block
  `p − 1`. One `aesPart` from the counter `c₀ + n − 7` (`c₀` the counter of
  `inc₃₂(J₀)`) XORs block `p` with its keystream and block `p − 1` with
  `CIPH_K(J₀)`; the eight results are stored back to `B₁`. The other blocks'
  results are never read.
* `B₂` (at `W + b2O`), zeroed, gets the additional data at block `p − 1`,
  the first `len` bytes of the ciphertext at block `p`, and the lengths
  block at block 7. Its first blocks stay zero, which leave GHASH from a
  zero accumulator as it is, so one `ghPart` from zero is `GHASH_H(A, C)`.

The tag is that GHASH XORed with block `p − 1` of `B₁`. `open` writes the
plaintext only if the tags are equal. Every branch and address depends only
on the lengths (and, in `open`, on whether the tags are equal).

Modelled for Neoverse N2 (`llvm-mca` of the instructions `qemu` runs, with
the powers published), with AES-128: sealing 31, 63 and 95 bytes from 111,
135 and 161 cycles to 107, 112 and 114; opening 15, 31, 63 and 95 bytes
from 102, 111, 130 and 148 to 99, 101, 103 and 110. -/

/-- The buffers. -/
def b1O : Nat := 768
def b2O : Nat := 896

/-- The longest text of the path, in bytes. -/
def shortMax : Nat := 96

/-- `x9 = ⌊(x7 + 31) / 128⌋`, zero exactly when the text's length `x7` is at
most `shortMax`. -/
def shortThr : List Instr := [.addImm .x .x9 .x7 (127 - shortMax), .lsr .x .x9 .x9 7]

/-- `x9 = ⌊(x7 + 15) / 32⌋`, zero exactly when the text's length `x7` is at
most 16 bytes, which `seal` and `open` give `Fast.lean`'s path: modelled for
Neoverse N2, `sealShort` costs about as much as that path for 16 bytes, and
less for more; `openShort`, which the model put below it, ran 50–150 more
instructions for these, measured 1.5–8% slower on Neoverse N2 (#2865). -/
def shortMin : List Instr := [.addImm .x .x9 .x7 15, .lsr .x .x9 .x9 5]

/-- The length in `x26`, the text in `x27`, the additional data's length in
`x24` (`tb` may write `x5`), and `x25 = 16 n`: every length and pointer the
path uses after `tb` is in a register. -/
def shortLen : List Instr :=
  [mov .x26 .x7, mov .x27 .x6, mov .x24 .x5, .addImm .x .x25 .x7 15, .lsr .x .x25 .x25 4,
    .lsl .x .x25 .x25 4]

/-- `r` at block `p + d − 1` of the buffer at `W + b`. -/
def atP (r : Reg) (b d : Nat) : List Instr := [.addImm .x r .x19 (b + 96 + 16 * d), .sub .x r r .x25]

/-- `B₂` and block `p − 1` of `B₁` (which `CIPH_K(J₀)` is encrypted from) zeroed. -/
def zeroBufs : List Instr :=
  .vop (.movi0 .v0) :: (List.range 8).map (fun i => .strq .v0 .x19 (b2O + 16 * i)) ++ atP .x9 b1O 0 ++
    ([.strq .v0 .x9 0] : List Instr)

/-- `J₀` and the first counter block, `shortLen`, the table `tb`, and the
buffers zeroed. -/
def shortPre (tb : List Instr) : Prog isa :=
  .seq (.block (j012 ++ initState ++ shortLen)) (.seq (.block tb) (.block zeroBufs))

/-- The `x13` bytes at `x12` copied to `x11`, through `v0`: fewer than 16
with `copy`; otherwise the whole blocks (`SealGather.copyBlocks`), then the
last 16 bytes, which overlap them. -/
def copyQ : Prog isa :=
  .seq (.block [.lsr .x .x14 .x13 4])
    (.ite (.zero .x .x14) copy
      (.seq (.block [.add .x .x9 .x12 .x13, .subImm .x .x9 .x9 16, .add .x .x10 .x11 .x13,
          .subImm .x .x10 .x10 16])
        (.seq SealGather.copyBlocks (.block [.ldrq .v0 .x9 0, .strq .v0 .x10 0]))))

/-- The text copied to block `p` of `B₁`. -/
def textIn : Prog isa := .seq (.block (atP .x11 b1O 1 ++ [mov .x12 .x27, mov .x13 .x26])) copyQ

/-- The counter `c₀ + n − 7` in `w10`, and `B₁` in `x9`. -/
def shortCtr : List Instr :=
  [.ldr .w .x10 .x20 60, .rev32 .x10 .x10, .lsr .x .x9 .x25 4, .add .w .x10 .x10 .x9,
    .subImm .w .x10 .x10 7, .addImm .x .x9 .x19 b1O]

/-- One pass of the counter mode over `B₁`, stored back. -/
def shortAes (nr : Nat) : Prog isa :=
  .block (Gcm.AArch64.Stitch.aesPart nr 0 ++ Gcm.AArch64.Stitch.stores 0)

/-- The `n` blocks at block `p` of `B₁` copied to block `p` of `B₂`, and the
bytes there after the first `len` zeroed with one 16-byte store (into block
7 at most, which the lengths block then takes). -/
def ctToB2 : Prog isa :=
  .seq (.block (atP .x12 b1O 1 ++ atP .x11 b2O 1 ++ [.lsr .x .x14 .x25 4]))
    (.seq (.ite (.zero .x .x14) (.block []) SealGather.copyBlocks)
      (.block (atP .x9 b2O 1 ++ [.add .x .x9 .x9 .x26, .vop (.movi0 .v0), .strq .v0 .x9 0])))

/-- The ciphertext copied from `B₁` to the text, then to `B₂` (`ctToB2`). -/
def textOut : Prog isa :=
  .seq (.block (atP .x12 b1O 1 ++ [mov .x11 .x27, mov .x13 .x26])) (.seq copyQ ctToB2)

/-- The additional data copied to block `p − 1` of `B₂`. -/
def aadIn : Prog isa :=
  .seq (.block ([mov .x12 .x4] ++ atP .x11 b2O 0 ++ [mov .x13 .x24])) copy

/-- The lengths block, at block 7 of `B₂`. -/
def lensB : List Instr :=
  [.lsl .x .x9 .x24 3, .rev .x9 .x9, .str .x .x9 .x19 (b2O + 112),
    .lsl .x .x9 .x26 3, .rev .x9 .x9, .str .x .x9 .x19 (b2O + 120)]

/-- GHASH of `B₂` from zero, into `v16` (`Gcm.AArch64.Stitch.Y`). -/
def shortGh : List Instr :=
  ([.movz .x .x12 0xc200 3, .vop (.dup .d2 Gcm.AArch64.Stitch.C .x12), .vop (.movi0 Gcm.AArch64.Stitch.Y),
    .addImm .x .x9 .x19 b2O] : List Instr) ++ Gcm.AArch64.Stitch.ghPart

/-- The tag, the hash XORed with block `p − 1` of `B₁`, at `W + o`. -/
def shortTagAt (o : Nat) : List Instr :=
  ([.vop (.rev .rev64b Gcm.AArch64.Stitch.Y Gcm.AArch64.Stitch.Y)] : List Instr) ++ atP .x9 b1O 0 ++
    ([.ldrq .v0 .x9 0, .vop (.logic .eor Gcm.AArch64.Stitch.Y Gcm.AArch64.Stitch.Y .v0),
      .strq Gcm.AArch64.Stitch.Y .x19 o] : List Instr)

/-- The tag at `W`, then to `x28`. -/
def shortTag : List Instr := shortTagAt 0 ++ tagOut

/-- `seal`'s path for a record of at most `shortMax` bytes, with the table `tb`. -/
def sealShort (tb : List Instr) : Prog isa :=
  .seq (shortPre tb)
  (.seq textIn
  (.seq (.block shortCtr)
  (.seq (Gcm.AArch64.Stitch.byRounds shortAes)
  (.seq textOut
  (.seq aadIn
    (.block (lensB ++ shortGh ++ shortTag ++ restore)))))))

/-- The plaintext copied from block `p` of `B₁` to the text. -/
def plainOut : Prog isa :=
  .seq (.block (atP .x12 b1O 1 ++ [mov .x11 .x27, mov .x13 .x26])) copyQ

/-- `open`'s path for a record of at most `shortMax` bytes, once the tag
length is allowed and the received tag is at `W`: the ciphertext hashed from
`B₂` and decrypted in `B₁`, the tag to `W + uO` and compared, and the
plaintext written only if they are equal, `x0` then 1 and else 0. -/
def openShort (tb : List Instr) : Prog isa :=
  .seq (shortPre tb)
  (.seq textIn
  (.seq ctToB2
  (.seq aadIn
  (.seq (.block (lensB ++ shortGh ++ shortCtr))
  (.seq (Gcm.AArch64.Stitch.byRounds shortAes)
  (.seq (.block (shortTagAt uO))
  (.seq cmp
  (.seq (.block [imm .x24 1, .sub .x .x24 .x24 .x10])
  (.seq (.ite (.zero .x .x24) (.block []) plainOut)
    (.block [mov .x0 .x24]))))))))))

/-- `openShort`, after the tag length is checked and the tag read. -/
def openShortF (tb : List Instr) : Prog isa :=
  .seq tagLenOk
  (.seq (.ite (.zero .x .x9) (.block [imm .x0 0]) (.seq tagIn (openShort tb)))
    (.block restore))

/-- `vg_aes_gcm_seal`, with `work` at `sp + k`: with `sh`, from 17 to
`shortMax` bytes, `sealShort`; otherwise below `minLen` bytes, `Fast.lean`'s
path. Only `_with_powers` takes `sealShort`: `_store_powers` must store the
powers, which only the call `cl` does, and is called only on longer texts. -/
def sealWithS (k : Nat) (tb : List Instr) (cl : Prog isa) (sh : Bool := false) : Prog isa :=
  .seq (.block (oneEntry k ++ stashArg 0))
    (.seq cond (.ite (.zero .x .x10)
      (if sh then
        .seq (.block shortThr) (.ite (.zero .x .x9)
          (.seq (.block shortMin) (.ite (.zero .x .x9) (runWithP c cl) (sealShort tb)))
          (.seq (.block thr) (.ite (.zero .x .x9) (runWithP c cl) (runWithS c tb cl))))
      else .seq (.block thr) (.ite (.zero .x .x9) (runWithP c cl) (runWithS c tb cl)))
      (sealRest c)))

/-- `vg_aes_gcm_open`, with `work` at `sp + k`: with `sh`, from 17 to
`shortMax` bytes, `openShort`; otherwise below `minLen` bytes, `Fast.lean`'s
path (as for `sealWithS`'s `sh`). -/
def openWithS (k : Nat) (tb : List Instr) (cl : Prog isa) (sh : Bool := false) : Prog isa :=
  .seq (.block (oneEntry k ++ stashArg 8 ++ ([.ldrSp .x12 0] : List Instr)))
    (.seq cond (.ite (.zero .x .x10)
      (if sh then
        .seq (.block shortThr) (.ite (.zero .x .x9)
          (.seq (.block shortMin) (.ite (.zero .x .x9) (openFastP c cl) (openShortF tb)))
          (.seq (.block thr) (.ite (.zero .x .x9) (openFastP c cl) (openFastS c tb cl))))
      else .seq (.block thr) (.ite (.zero .x .x9) (openFastP c cl) (openFastS c tb cl)))
      (openRest c)))

/-- `vg_aes_gcm_seal_with_powers`, hashing the rest by `gh`. -/
def sealWithPw (gh : Fn) : Prog isa := sealWithS c 16 (pwTbl 8) (pwSel c 8 gh) true

/-- `vg_aes_gcm_open_with_powers`, hashing the rest by `gh`. -/
def openWithPw (gh : Fn) : Prog isa := openWithS c 24 (pwTbl 16) (pwSel c 16 gh) true

/-- `vg_aes_gcm_seal_store_powers`, `gh` storing the powers. -/
def sealStorePw (gh : Fn) : Prog isa := sealWithS c 16 powTbl (pwCall 8 gh)

/-- `vg_aes_gcm_open_store_powers`, `gh` storing the powers. -/
def openStorePw (gh : Fn) : Prog isa := openWithS c 24 powTbl (pwCall 16 gh)

end VG.Impl.AesGcm.AArch64.Stitch
